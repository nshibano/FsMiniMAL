module FsMiniMAL.Value

open System
open System.Collections.Generic
open System.Threading
open System.Reflection
open FSharp.Reflection

open Types
open System.Text
open System.ComponentModel
open FsMiniMAL.MalLex

let sizeof_int, sizeof_float, block_overhead, block_increment, array_overhead, array_increment, string_overhead, string_increment =
    if IntPtr.Size = 8
    then 32, 40, 64, 8, 96, 8, 70, 2
    else 20, 24, 36, 4, 48, 4, 34, 2

let sizeof_block len = block_overhead + block_increment * len
let sizeof_array cap = array_overhead + array_increment * cap
let sizeof_string len = string_overhead + string_increment * len

// Ordering is significant for COMPARE to GREATER_EQUAL
type builtin_id =
    | COMPARE = 0
    | TRY_COMPARE = 1
    | EQUAL = 2
    | NOT_EQUAL = 3
    | LESS_THAN = 4
    | GREATER_THAN = 5
    | LESS_EQUAL = 6
    | GREATER_EQUAL = 7    
    | KPRINTF = 8
    | SLEEP = 9
    | LEXING = 10

type value =
    | Vint of int * int ref
    | Vfloat of float * int ref
    | Vblock of int * value array * int ref
    | Varray of malarray
    | Vstring of string * int ref
    | Vformat of PrintfFormat.PrintfCommand list
    | Vbuiltin of arity : int * builtin_id
    | Vfunc of arity : int * func : (runtime -> value array -> value)
    | Vclosure of arity : int * env_size : int * offsets : int array * captures : value array * code : code
    | Vpartial of arity : int * values : value array
    | Vvar of value ref
    | Vobj of obj
    
    override this.Finalize() =
        match this with
        | Vint (_, counter) -> Interlocked.Add(counter, - sizeof_int) |> ignore
        | Vfloat (_, counter) -> Interlocked.Add(counter, - sizeof_float) |> ignore
        | Vblock (_, fields, counter) -> Interlocked.Add(counter, - sizeof_block fields.Length) |> ignore
        | Varray { storage = storage; memory_counter = counter } -> Interlocked.Add(counter, - sizeof_array storage.Length) |> ignore
        | Vstring (s, counter) -> Interlocked.Add(counter, - sizeof_string s.Length) |> ignore
        | _ -> ()

and malarray =
    { mutable count : int
      mutable storage : value array
      memory_counter : int ref }

and code =
  // expressions
  | UEconst of value
  | UEenv of int
  | UEenvvar of int
  | UEsetenvvar of int * code
  | UEblock of tag : int * fields : code array
  | UEblockwith of orig : code * field_indexes : int array * field_values : code array // { orig with field = expr; ... }
  | UEarray of code array
  | UEapply of code array
  | UEfn of env_size : int * arity : int * capture_ofs_from : int array * capture_ofs_to : int array * code
  | UEbegin of cmdl : code array
  | UEcase of code * (pattern * code option * code) array // (test_expr, [| (pat, when_clause_expr, result_expr); ... |])
  | UEtry of code * (pattern * code) array
  | UEif of code * code * code
  | UEfor of ofs : int * first : code * dirflag * last : code * code
  | UEwhile of code * code
  
  // dummy code
  | UEcompare

  // commands
  | UCval of (pattern * code) array
  | UCvar of (int * code) array
  | UCfun of (int * code) array

  // toplevel commands
  | UTCtype of Syntax.typedef list * Syntax.location
  | UTChide of string
  | UTCremove of string
  | UTCexn of string * Syntax.location
  | UTClex of (int * int * HashSet<int> * DfaNode * code array) array // arity, offset, alphabets, dfa, actions
  | UTCupd of tyenv * Allocator * shadowed_genv_offsets : int array option
  | UTCprint_value of type_expr
  | UTCprint_new_values of (string * value_info) list

and pattern =
  | UPid of int
  | UPas of pattern * int
  | UPint of int
  | UPchar of char
  | UPfloat of float
  | UPstring of string
  | UPblock of int * pattern array
  | UParray of pattern array
  | UPor of pattern * pattern
  | UPany

and config =
    { 
      /// When memory_counter values exceedes this limit, GC will be called.
      bytes_trigger_gc : int

      /// After GC called, if the memory_counter still exceeds this limit, interpreter is stopped.
      bytes_stop_exec : int

      maximum_stack_depth : int

      maximum_array_length : int
    }

    static member Default =
        {
            bytes_trigger_gc = 256 <<< 20 // 256 MiB
            bytes_stop_exec = 128 <<< 20 // 128 MiB
            maximum_stack_depth = 1 <<< 20 // 1048576
            
            // A practical limit for length of arrays. 128MiB for value array on 64 bit machine.
            maximum_array_length = 1 <<< 24 // 16777216 
        }

and runtime =
    { 
      /// The value obtained from System.Diagnostics.Stopwatch.GetTimestamp() at start of this time slice.
      mutable timestamp_at_start : int64

      /// The counter for interpreter cycles.
      mutable cycles : int64
      
      /// Total bytes used by mal values this interpreter owns.
      /// This field is increased when new mal value is created, and decreased when mal value is freed by CLR garbage collector. 
      memory_counter : int ref

      mutable print_string : string -> unit
      
      config : config
    }

exception InsufficientMemory

let dummy_runtime =
    { runtime.memory_counter = ref 0
      timestamp_at_start = 0L
      cycles = 0L
      print_string = ignore
      config =
        { 
            maximum_stack_depth = Int32.MaxValue
            bytes_trigger_gc = Int32.MaxValue
            bytes_stop_exec = Int32.MaxValue
            maximum_array_length = Int32.MaxValue
        }
    }

let collect () =
    GC.Collect()
    GC.WaitForPendingFinalizers()
    GC.Collect()

let check_free_memory (rt : runtime) needed_bytes =
    Volatile.Read(rt.memory_counter) + needed_bytes < rt.config.bytes_trigger_gc ||
    (collect()
     Volatile.Read(rt.memory_counter) + needed_bytes < rt.config.bytes_stop_exec)

let of_int (rt : runtime) i =
    Interlocked.Add(rt.memory_counter, sizeof_int) |> ignore
    Vint (i, rt.memory_counter)

let to_int v = match v with Vint (i, _) -> i | _ -> dontcare()

let of_char (rt : runtime) (c : char) = of_int rt (int c)

let to_char (v : value) =
    let i = to_int v
    if int Char.MinValue <= i && i <= int Char.MaxValue then
        char i
    else
        dontcare()

let of_float (rt : runtime) x =
    Interlocked.Add(rt.memory_counter, sizeof_float) |> ignore
    Vfloat (x, rt.memory_counter)

let to_float v = match v with Vfloat (x, _) -> x | _ -> dontcare()

let is_float v = match v with Vfloat _ -> true | _ -> false

let block_createrange (rt : runtime) tag (fields : value array) =
    Interlocked.Add(rt.memory_counter, block_overhead + fields.Length * block_increment) |> ignore
    Vblock (tag, fields, rt.memory_counter)

let gettag (v : value) =
    match v with
    | Vint (i, _) -> i
    | Vblock (tag, _, _) -> tag
    | _ -> dontcare()

let getfields (v : value) =
    match v with
    | Vint _ -> [||]
    | Vblock (_, fields, _) -> fields
    | _ -> dontcare()
    
let block_getrange (v : value) =
    match v with
    | Vblock (_, fields, _) -> fields
    | _ -> dontcare()
         
/// raises InsufficientMemory
let array_create (rt : runtime) (needed_capacity : int) =
    let capacity =
        try find_next_capacity_exn rt.config.maximum_array_length needed_capacity
        with :? InvalidOperationException -> raise InsufficientMemory
    let bytes = array_overhead + array_increment * capacity
    if not (check_free_memory rt bytes) then raise InsufficientMemory
    Interlocked.Add(rt.memory_counter, bytes) |> ignore
    Varray { count = 0; storage = Array.zeroCreate<value> capacity; memory_counter = rt.memory_counter }

/// raises InsufficientMemory, RuntimeTypeError
let array_add (rt : runtime) (ary : value) (item : value) =
    match ary with  
    | Varray ({ count = count; storage = storage } as ary) ->
        let capacity = if isNull storage then 0 else storage.Length
        if capacity < count + 1 then
            let new_capacity =
                try find_next_capacity_exn rt.config.maximum_array_length (count + 1)
                with :? InvalidOperationException -> raise InsufficientMemory
            let increased_bytes = array_increment * (new_capacity - capacity)
            if not (check_free_memory rt increased_bytes) then raise InsufficientMemory
            let new_storage = Array.zeroCreate<value> new_capacity
            if not (isNull storage) then Array.blit storage 0 new_storage 0 count
            ary.storage <- new_storage
            Interlocked.Add(ary.memory_counter, increased_bytes) |> ignore
        ary.storage.[ary.count] <- item
        ary.count <- ary.count + 1
    | _ -> dontcare()

let array_append (rt : runtime) (a : value) (b : value) =
    match a, b with
    | Varray { count = a_count; storage = a_storage }, Varray { count = b_count; storage = b_storage } ->
        let c_count = a_count + b_count
        let c = array_create rt c_count
        match c with
        | Varray ({ storage = c_storage } as c_ary) ->
            if a_count <> 0 then Array.blit a_storage 0 c_storage 0 a_count
            if b_count <> 0 then Array.blit b_storage 0 c_storage a_count b_count
            c_ary.count <- c_count
            c
        | _ -> dontcare()
    | _ -> dontcare()

/// raises IndexOutOfRangeException
let array_get (rt : runtime) (v : value) (i : int) =
    match v with
    | Varray ary ->
        if 0 <= i && i < ary.count then
            ary.storage.[i]
        else raise (IndexOutOfRangeException())
    | _ -> dontcare()

/// raises IndexOutOfRangeException
let array_set (ary : value) i (x : value) =
    match ary with
    | Varray ary ->
        if 0 <= i && i < ary.count then
            ary.storage.[i] <- x
        else raise (IndexOutOfRangeException())
    | _ -> dontcare()

/// raises IndexOutOfRangeException, RuntimeTypeError
let array_remove_at (rt : runtime) (v : value) i =
    match v with
    | Varray ary ->
        if 0 <= i && i < ary.count then
            for j = i + 1 to ary.count - 1 do
                ary.storage.[j - 1] <- ary.storage.[j]
            ary.storage.[ary.count - 1] <- Unchecked.defaultof<value>
            ary.count <- ary.count - 1
        else raise (IndexOutOfRangeException())
    | _ -> dontcare()

let array_clear (rt : runtime) (v : value) =
    match v with
    | Varray ary ->
        for i = 0 to ary.count - 1 do
            ary.storage.[i] <- Unchecked.defaultof<value>
        ary.count <- 0
    | _ -> dontcare()

let array_copy (rt : runtime) (orig : value) =
    match orig with
    | Varray { count = count; storage = storage } ->
        let copy = array_create rt count
        match copy with
        | Varray ({ storage = copy_storage } as copy_ary) ->
            if count <> 0 then Array.blit storage 0 copy_storage 0 count;
            copy_ary.count <- count
            copy
        | _ -> dontcare()
    | _ -> dontcare()

let zero = of_int dummy_runtime 0
let one = of_int dummy_runtime 1
let neg_one = of_int dummy_runtime (-1)
let int_min = of_int dummy_runtime (Int32.MinValue)

let of_compare n =
    match n with
    | 1 -> one
    | 0 -> zero
    | -1 -> neg_one
    | Int32.MinValue -> int_min
    | _ -> dontcare()

let unit = zero
let ``false`` = zero
let ``true`` = one

let of_bool b = if b then ``true`` else ``false``

let to_string v =
    match v with
    | Vstring (s, _) -> s
    | _ -> dontcare()

let of_string (rt : runtime) (s : string) =
    Interlocked.Add(rt.memory_counter, string_overhead + string_increment * s.Length) |> ignore
    Vstring (s, rt.memory_counter)

let to_obj v =
    match v with
    | Vobj o -> o
    | _ -> dontcare()

let of_obj o = Vobj o

let to_bool v =
    match v with
    | Vint (0, _) -> false
    | Vint (1, _) -> true
    | _ -> dontcare()

exception MALException of value // exception which user code can catch

let mal_failure rt msg = block_createrange rt tag_exn_Failure [| of_string rt msg |]
let mal_failwith rt msg = raise (MALException (mal_failure rt msg))

let mal_DivisionByZero = of_int dummy_runtime tag_exn_DivisionByZero
let mal_raise_DivisionByZero () = raise (MALException mal_DivisionByZero)

let mal_IndexOutOfRange = of_int dummy_runtime tag_exn_IndexOutOfRange
let mal_raise_IndexOutOfRange () = raise (MALException mal_IndexOutOfRange)

let mal_MatchFailure = of_int dummy_runtime tag_exn_MatchFailure
let mal_raise_MatchFailure () = raise (MALException mal_MatchFailure)

let to_hash v =
    let mutable values_limit = 100
    let mutable meaningful_limit = 10
        
    let mutable accu = 17
    let combine h =
        accu <- (accu * 23) + h
        meaningful_limit <- meaningful_limit - 1
        
    let queue = Queue<value>()        
    queue.Enqueue(v)

    let rec scan v =
        match v with
        | Vint (i, _) -> combine i
        | Vfloat (x, _) -> combine (x.GetHashCode())
        | Vstring (s, _) -> combine (s.GetHashCode())
        | Vblock (tag, fields, _) ->
            combine tag
            let n = min fields.Length values_limit
            for i = 0 to n - 1 do
                queue.Enqueue(fields.[i])
            values_limit <- values_limit - n
        | Varray ary ->
            let n = min ary.count values_limit
            for i = 0 to n - 1 do
                queue.Enqueue(ary.storage.[i])
            values_limit <- values_limit - n
        | Vformat fmt -> combine (fmt.GetHashCode())
        | Vbuiltin (_, id) -> combine (int id)
        | Vfunc (_, f) -> combine (LanguagePrimitives.PhysicalHash f)
        | Vclosure (code = code; captures = captures) ->
            combine (LanguagePrimitives.PhysicalHash code)
            let n = min captures.Length values_limit
            for i = 0 to n - 1 do
                queue.Enqueue(captures.[i])
            values_limit <- values_limit - n
        | Vpartial (_, values) ->
            scan values.[0]
            let n = min (values.Length - 1) values_limit
            for i = 1 to n do
                queue.Enqueue(values.[i])
            values_limit <- values_limit - n                
        | Vvar _ -> dontcare()
        | Vobj obj -> combine (obj.GetHashCode())

    while queue.Count > 0 && meaningful_limit > 0 do
        scan (queue.Dequeue())

    accu

let rec obj_of_value (cache : Dictionary<Type, HashSet<value> -> value -> obj>) (tyenv : tyenv) (touch : HashSet<value>) (ty : Type) (value : value) =
    if touch.Contains(value) then mal_failwith dummy_runtime "cyclic value in interop"
    match cache.TryGetValue(ty) with
    | true, f -> f touch value
    | false, _ ->
        let f =
            if ty = typeof<unit> then
                (fun (touch : HashSet<value>) (value : value) -> box ())
            elif ty = typeof<bool> then
                (fun (touch : HashSet<value>) (value : value) -> box (to_bool value))
            elif ty = typeof<int32> then
                (fun (touch : HashSet<value>) (value : value) -> box (to_int value))
            elif ty = typeof<char> then
                (fun (touch : HashSet<value>) (value : value) -> box (to_char value))
            elif ty = typeof<float> then
                (fun (touch : HashSet<value>) (value : value) -> box (to_float value))
            elif ty = typeof<string> then
                (fun (touch : HashSet<value>) (value : value) -> box (to_string value))
            elif tyenv.registered_abstract_types.ContainsKey(ty) then
                (fun (touch : HashSet<value>) (value : value) -> box (to_obj value))
            elif ty.IsArray then
                let ty_elem = ty.GetElementType()
                (fun (touch : HashSet<value>) (value : value) ->
                    match value with
                    | Varray malarray ->
                        let array = System.Array.CreateInstance(ty_elem, malarray.count)
                        touch.Add(value) |> ignore
                        for i = 0 to malarray.count - 1 do
                            array.SetValue(obj_of_value cache tyenv touch ty_elem malarray.storage.[i], i)
                        touch.Remove(value) |> ignore
                        array :> obj
                    | _ -> dontcare())
            elif FSharpType.IsTuple ty then
                let constr = FSharpValue.PreComputeTupleConstructor(ty)
                let types = FSharpType.GetTupleElements(ty)
                (fun (touch : HashSet<value>) (value : value) ->
                    let fields = block_getrange value
                    touch.Add(value) |> ignore
                    let objs = Array.map2 (fun ty field -> obj_of_value cache tyenv touch ty field) types fields
                    touch.Remove(value) |> ignore
                    constr objs)
            elif FSharpType.IsRecord ty then
                let constr = FSharpValue.PreComputeRecordConstructor(ty)
                let types = Array.map (fun (info : PropertyInfo) -> info.PropertyType) (FSharpType.GetRecordFields(ty))
                (fun (touch : HashSet<value>) (value : value) ->
                    let fields = block_getrange value
                    touch.Add(value) |> ignore
                    let objs = Array.map2 (fun ty value -> obj_of_value cache tyenv touch ty value) types fields
                    touch.Remove(value) |> ignore
                    constr objs)
            elif FSharpType.IsUnion ty then
                let cases = FSharpType.GetUnionCases(ty)
                let constrs = Array.map (fun (case : UnionCaseInfo) -> FSharpValue.PreComputeUnionConstructor(case)) cases
                let case_field_types = Array.map (fun (case : UnionCaseInfo) -> Array.map (fun (prop : PropertyInfo) -> prop.PropertyType) (case.GetFields())) cases
                (fun (touch : HashSet<value>) (value : value) ->
                    let tag = gettag value
                    let types = case_field_types.[tag]
                    let fields = getfields value
                    touch.Add(value) |> ignore
                    let objs = Array.map2 (fun ty value -> obj_of_value cache tyenv touch ty value) types fields
                    touch.Remove(value) |> ignore
                    constrs.[tag] objs)
            else
                raise (NotImplementedException())
        cache.[ty] <- f
        f touch value

let rec value_of_obj (cache : Dictionary<Type, runtime -> obj -> value>) (tyenv : tyenv) (ty : Type) (rt : runtime) (obj : obj) =
    match cache.TryGetValue(ty) with
    | true, f -> f rt obj
    | false, _ ->
        let f =
            if ty = typeof<unit> then
                (fun (rt : runtime) (obj : obj) -> unit)
            elif ty = typeof<bool> then
                (fun (rt : runtime) (obj : obj) -> of_bool (obj :?> bool))
            elif ty = typeof<int32> then
                (fun (rt : runtime) (obj : obj) -> of_int rt (obj :?> int32))
            elif ty = typeof<char> then
                (fun (rt : runtime) (obj : obj) -> of_char rt (obj :?> char))
            elif ty = typeof<float> then
                (fun (rt : runtime) (obj : obj) -> of_float rt (obj :?> float))
            elif ty = typeof<string> then
                (fun (rt : runtime) (obj : obj) -> of_string rt (obj :?> string))
            elif tyenv.registered_abstract_types.ContainsKey(ty) then
                (fun (rt : runtime) (obj : obj) -> of_obj obj)
            elif ty.IsArray then
                let ty_elem = ty.GetElementType()
                (fun (rt : runtime) (obj : obj) ->
                    let ary = obj :?> System.Array
                    let len = ary.Length
                    let malary = array_create rt len
                    for i = 0 to len - 1 do
                        array_add rt malary (value_of_obj cache tyenv ty_elem rt (ary.GetValue(i)))
                    malary)
            elif FSharpType.IsTuple ty then
                let reader = FSharpValue.PreComputeTupleReader(ty)
                let types = FSharpType.GetTupleElements(ty)
                (fun (rt : runtime) (obj : obj) -> 
                    let objs = reader obj
                    let values = Array.map2 (fun ty obj -> value_of_obj cache tyenv ty rt obj) types objs
                    block_createrange rt 0 values)
            elif FSharpType.IsRecord ty then
                let reader = FSharpValue.PreComputeRecordReader(ty)
                let types = Array.map (fun (info : PropertyInfo) -> info.PropertyType) (FSharpType.GetRecordFields(ty))
                (fun (rt : runtime) (obj : obj) -> 
                    let objs = reader obj
                    let values = Array.map2 (fun ty obj -> value_of_obj cache tyenv ty rt obj) types objs
                    block_createrange rt 0 values)
            elif FSharpType.IsUnion ty then
                let tag_reader = FSharpValue.PreComputeUnionTagReader(ty)
                let cases = FSharpType.GetUnionCases(ty)
                let fs =
                    Array.mapi (fun i (case : UnionCaseInfo) ->
                        if i <> case.Tag then dontcare()
                        let fields = case.GetFields()
                        if fields.Length = 0 then
                            (fun (rt : runtime) (obj : obj) ->
                                of_int rt i)
                        else
                            let field_types = Array.map (fun (field : PropertyInfo) -> field.PropertyType) fields
                            let case_reader = FSharpValue.PreComputeUnionReader(case)
                            (fun (rt : runtime) (obj : obj) ->
                                let field_objs = case_reader obj
                                let field_vals = Array.map2 (fun ty obj -> value_of_obj cache tyenv ty rt obj) field_types field_objs
                                block_createrange rt i field_vals)) cases
                (fun (rt : runtime) (obj : obj) ->
                    let tag = tag_reader obj
                    fs.[tag] rt obj)
            else
                raise (NotImplementedException())

        cache.[ty] <- f
        f rt obj

let touch_create() = HashSet<value>(Misc.PhysicalEqualityComparer)

let wrap_fsharp_func (tyenv : tyenv) (obj_of_value_cache : Dictionary<Type, HashSet<value> -> value -> obj>) (value_of_obj_cache : Dictionary<Type, runtime -> obj -> value>) (ty : Type) (func : obj) =
    
    let rec flatten ty =
        if FSharpType.IsFunction ty then
            let t1, t2 = FSharpType.GetFunctionElements ty
            t1 :: flatten t2
        else
            [ty]
    
    let tyl = Array.ofList (flatten ty)

    if not (tyl.Length >= 3 && tyl.[0] = typeof<runtime>) then dontcare()

    match tyl.Length with
    | 3 ->
        let invokefast =
            let methods = typedefof<FSharpFunc<_, _>>.MakeGenericType(tyl.[0], tyl.[1]).GetTypeInfo().DeclaredMethods
            let invokefast_gen = Seq.find (fun (mi : MethodInfo) -> mi.Name = "InvokeFast" && mi.GetParameters().Length = 3) methods
            invokefast_gen.MakeGenericMethod(tyl.[2])
        let func rt values =
            match values with
            | [| arg0 |] ->
                let touch = touch_create()
                let arg0 = obj_of_value obj_of_value_cache tyenv touch tyl.[1] arg0
                let result_obj =
                    try invokefast.Invoke(null, [| func; rt; arg0 |])
                    with :? System.Reflection.TargetInvocationException as exn -> raise exn.InnerException
                value_of_obj value_of_obj_cache tyenv  tyl.[2] rt result_obj
            | _ -> dontcare()
        Vfunc (1, func)
    | 4 ->
        let invokefast =
            let methods = typedefof<FSharpFunc<_, _>>.MakeGenericType(tyl.[0], tyl.[1]).GetTypeInfo().DeclaredMethods
            let invokefast_gen = Seq.find (fun (mi : MethodInfo) -> mi.Name = "InvokeFast" && mi.GetParameters().Length = 4) methods
            invokefast_gen.MakeGenericMethod(tyl.[2], tyl.[3])
        let func rt values =
            match values with
            | [| arg0; arg1 |] ->
                let touch = touch_create()
                let arg0 = obj_of_value obj_of_value_cache tyenv touch tyl.[1] arg0
                let arg1 = obj_of_value obj_of_value_cache tyenv touch tyl.[2] arg1
                let result_obj =
                    try invokefast.Invoke(null, [| func; rt; arg0; arg1 |])
                    with :? System.Reflection.TargetInvocationException as exn -> raise exn.InnerException
                value_of_obj value_of_obj_cache tyenv  tyl.[3] rt result_obj
            | _ -> dontcare()
        Vfunc (2, func)
    | 5 ->
        let invokefast =
            let methods = typedefof<FSharpFunc<_, _>>.MakeGenericType(tyl.[0], tyl.[1]).GetTypeInfo().DeclaredMethods
            let invokefast_gen = Seq.find (fun (mi : MethodInfo) -> mi.Name = "InvokeFast" && mi.GetParameters().Length = 5) methods
            invokefast_gen.MakeGenericMethod(tyl.[2], tyl.[3], tyl.[4])
        let func rt values =
            match values with
            | [| arg0; arg1; arg2 |] ->
                let touch = touch_create()
                let arg0 = obj_of_value obj_of_value_cache tyenv touch tyl.[1] arg0
                let arg1 = obj_of_value obj_of_value_cache tyenv touch tyl.[2] arg1
                let arg2 = obj_of_value obj_of_value_cache tyenv touch tyl.[3] arg2
                let result_obj =
                    try invokefast.Invoke(null, [| func; rt; arg0; arg1; arg2 |])
                    with :? System.Reflection.TargetInvocationException as exn -> raise exn.InnerException
                value_of_obj value_of_obj_cache tyenv  tyl.[4] rt result_obj
            | _ -> dontcare()
        Vfunc (3, func)
    | 6 ->
        let invokefast =
            let methods = typedefof<FSharpFunc<_, _>>.MakeGenericType(tyl.[0], tyl.[1]).GetTypeInfo().DeclaredMethods
            let invokefast_gen = Seq.find (fun (mi : MethodInfo) -> mi.Name = "InvokeFast" && mi.GetParameters().Length = 6) methods
            invokefast_gen.MakeGenericMethod(tyl.[2], tyl.[3], tyl.[4], tyl.[5])
        let func rt values =
            match values with
            | [| arg0; arg1; arg2; arg3 |] ->
                let touch = touch_create()
                let arg0 = obj_of_value obj_of_value_cache tyenv touch tyl.[1] arg0
                let arg1 = obj_of_value obj_of_value_cache tyenv touch tyl.[2] arg1
                let arg2 = obj_of_value obj_of_value_cache tyenv touch tyl.[3] arg2
                let arg3 = obj_of_value obj_of_value_cache tyenv touch tyl.[4] arg3
                let result_obj =
                    try invokefast.Invoke(null, [| func; rt; arg0; arg1; arg2; arg3 |])
                    with :? System.Reflection.TargetInvocationException as exn -> raise exn.InnerException
                value_of_obj value_of_obj_cache tyenv  tyl.[5] rt result_obj
            | _ -> dontcare()
        Vfunc (4, func)
    | _ -> raise (NotImplementedException())