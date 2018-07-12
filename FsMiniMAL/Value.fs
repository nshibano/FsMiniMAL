module FsMiniMAL.Value

open System
open System.Collections.Generic
open System.Threading

open Types

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
  | UTChideval of string
  | UTCexn of string * Syntax.location
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
      /// A rough estimate of elapsed time from start of time slice.
      /// This value is set to 0 at start of time slice. Incremented for interpreter cycles.
      /// For expensive builtin functions (e.g. array_copy), this field increased more at once. 
      mutable stopwatch : int64

      /// Total bytes used by mal values this interpreter owns.
      /// This field is increased when new mal value is created, and decreased when mal value is freed by CLR garbage collector. 
      memory_counter : int ref

      mutable print_string : string -> unit
      
      config : config
    }

exception InsufficientMemory

let dummy_runtime =
    { runtime.memory_counter = ref 0
      stopwatch = 0L
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
let array_add (rt : runtime) (v : value) (x : value) =
    match v with  
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
        ary.storage.[ary.count] <- x
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
        rt.stopwatch <- rt.stopwatch + int64 ary.count
        for i = 0 to ary.count - 1 do
            ary.storage.[i] <- Unchecked.defaultof<value>
        ary.count <- 0
    | _ -> dontcare()

let array_copy (rt : runtime) (orig : value) =
    match orig with
    | Varray { count = count; storage = storage } ->
        rt.stopwatch <- rt.stopwatch + int64 count
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

let to_bool v =
    match v with
    | Vint (0, _) -> false
    | Vint (1, _) -> true
    | _ -> dontcare()

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

    while queue.Count > 0 && meaningful_limit > 0 do
        scan (queue.Dequeue())

    accu