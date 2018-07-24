module FsMiniMAL.Stdlib

open System
open System.Text
open Printf

open Types
open Value

let getfield_func (rt : runtime) argv =
    match argv with
    | [| Vblock (_, fields, _); Vint (i, _) |] -> fields.[i]
    | _ -> dontcare()

let getfield = Vfunc (2, getfield_func)

let setfield_func (rt : runtime) argv =
    match argv with
    | [| Vblock (_, fields, _); Vint (i, _); x |] ->
        fields.[i] <- x
        Value.unit
    | _ -> dontcare()

let setfield = Vfunc (3, setfield_func)

let add_stdlib (tyenv : tyenv) (genv : value array) (alloc : Allocator) =
    let mutable tyenv = tyenv
    let mutable genv = genv
    let mutable alloc = alloc

    let a = Tvar { link = None; level = Types.generic_level; }
    let b = Tvar { link = None; level = Types.generic_level; }

    let ty_vvi = arrow2 a a ty_int
    let ty_bbb = arrow2 ty_bool ty_bool ty_bool
    let ty_vvb = arrow2 a a ty_bool    
    let ty_ii = arrow ty_int ty_int
    let ty_iii = arrow2 ty_int ty_int ty_int
    let ty_ff = arrow ty_float ty_float
    let ty_fff = arrow2 ty_float ty_float ty_float

    let add_builtin name ty arity id =
        tyenv <- Types.add_value tyenv name { vi_access = access.Immutable; vi_type = ty }
        let ofs = alloc.Add(name, access.Immutable)
        genv <- array_ensure_capacity_exn Int32.MaxValue (ofs + 1) genv
        genv.[ofs] <- Vbuiltin (arity, id)

    add_builtin "compare" ty_vvi 2 builtin_id.COMPARE
    add_builtin "try_compare" ty_vvi 2 builtin_id.TRY_COMPARE
    add_builtin "kprintf" (arrow2 (arrow ty_string b) (Tconstr (type_id.FORMAT, [a; b])) a) (-1) builtin_id.KPRINTF
    add_builtin "sleep" (arrow ty_float ty_unit) 1 builtin_id.SLEEP

    add_builtin "=" ty_vvb 2 builtin_id.EQUAL
    add_builtin "<>" ty_vvb 2 builtin_id.NOT_EQUAL
    add_builtin "<" ty_vvb 2 builtin_id.LESS_THAN
    add_builtin ">" ty_vvb 2 builtin_id.GREATER_THAN
    add_builtin "<=" ty_vvb 2 builtin_id.LESS_EQUAL
    add_builtin ">=" ty_vvb 2 builtin_id.GREATER_EQUAL

    let add_func name ty arity func =
        let value = Vfunc (arity, func) 
        let info = { vi_access = access.Immutable; vi_type = ty }
        tyenv <- Types.add_value tyenv name info
        let ofs = alloc.Add(name, access.Immutable)
        genv <- array_ensure_capacity_exn Int32.MaxValue (ofs + 1) genv
        genv.[ofs] <- value

    let and_func (rt : runtime) argv = 
            match argv with
            | [| Vint (1, _); Vint (1, _) |] -> Value.``true``
            | _ -> Value.``false``
    add_func "&&" ty_bbb 2 and_func

    let or_func (rt : runtime) argv = 
            match argv with
            | [| Vint (0, _); Vint (0, _) |] -> Value.``false``
            | _ -> Value.``true``
    add_func "||" ty_bbb 2 or_func
    
    let func_ii (func : int -> int) (rt : runtime) (argv : value array) =
        let a = to_int argv.[0]
        of_int rt (func a)
    
    let func_iii (func : int -> int -> int) (rt : runtime) (argv : value array) =
        let a = to_int argv.[0]
        let b = to_int argv.[1]
        of_int rt (func a b)
    
    let add_iii name (func : int -> int -> int) =
        add_func name ty_iii 2 (func_iii func)
    
    let add_ii name (func : int -> int) =
        add_func name ty_ii 1 (func_ii func)

    let add_i name i =
        let value = of_int dummy_runtime i
        let info = { vi_access = access.Immutable; vi_type = ty_int }
        tyenv <- Types.add_value tyenv name info
        let ofs = alloc.Add(name, access.Immutable)
        genv <- array_ensure_capacity_exn Int32.MaxValue (ofs + 1) genv
        genv.[ofs] <- value
    
    let add_fff name (func : float -> float -> float) =
        let builtin_func (g : runtime) argv = 
            match argv with
            | [| Vfloat (a, _); Vfloat (b, _) |] -> of_float g (func a b)
            | _ -> dontcare()
        add_func name ty_fff 2 builtin_func

    let add_ff name (func : float -> float) =
        let builtin_func (g : runtime) argv = 
            match argv with
            | [| Vfloat (a, _) |] -> of_float g (func a)
            | _ -> dontcare()
        add_func name ty_ff 1 builtin_func
    
    let ty_if = arrow ty_int ty_float
    let add_if name (func : int -> float) =         
        let builtin_func (g : runtime) argv = 
            match argv with
            | [| Vint (n, _) |] -> of_float g (func n)
            | _ -> dontcare()
        add_func name ty_if 1 builtin_func
    
    let ty_fi = arrow ty_float ty_int
    let add_fi name (func : float -> int) =
        let builtin_func (g : runtime) argv = 
            match argv with
            | [| Vfloat (a, _) |] -> of_int g (func a)
            | _ -> dontcare()
        add_func name ty_fi 1 builtin_func
        
    let add_vvb name (func : value -> value -> bool) =
        let builtin_func (g : runtime) argv = 
            match argv with
            | [| a; b |] -> of_int g (match func a b with false -> 0 | true -> 1)
            | _ -> dontcare()
        add_func name ty_vvb 2 builtin_func

    add_iii "+" ( + )
    add_iii "-" ( - )
    add_iii "*" ( * )
    add_iii "/" (fun a b -> if b <> 0 then a / b else mal_raise_DivisionByZero ())
    add_iii "%" (fun a b -> if b <> 0 then a % b else mal_raise_DivisionByZero ())
    add_ii "~-" ( ~- )
    add_ii "~~~" ( ~~~ )
    add_iii "|||" ( ||| )
    add_iii "^^^" ( ^^^ )
    add_iii "&&&" ( &&& )
    add_iii ">>>" ( >>> )
    add_iii "<<<" ( <<< )
    add_fff "+." ( + )
    add_fff "-." ( - )
    add_fff "*." ( * )
    add_fff "/." ( / )
    add_fff "**" ( ** )
    add_ff "~-." ( ~- )

    let not_func (g : runtime) argv =
        match argv with
        | [| Vint (i, _) |] -> of_int g (match i with 0 -> 1 | 1 -> 0 | _ -> dontcare())
        | _ -> dontcare()
    add_func "not" (arrow ty_bool ty_bool) 1 not_func
    
    let array_create_func (rt : runtime) (argv : value array) =
        let n = to_int argv.[0]
        if n < 0 then mal_failwith rt "array_create: negative length"
        let x = argv.[1]
        match x with
        | _ ->
            let v = array_create rt n
            match v with
            | Varray ({ storage = storage } as ary) ->
                for i = 0 to n - 1 do
                    storage.[i] <- x
                ary.count <- n
                v
            | _ -> dontcare()
    add_func "array_create" (arrow2 ty_int a (ty_array a)) 2 array_create_func 

    let array_append_func (rt : runtime) (argv : value array) =
        let a = argv.[0]
        let b = argv.[1]
        array_append rt a b
    add_func "^" (arrow2 (ty_array a) (ty_array a) (ty_array a)) 2 array_append_func

    let ty_sss = arrow2 ty_string ty_string ty_string
    let string_append_func (rt : runtime) (argv : value array) =
        of_string rt (to_string argv.[0] + to_string argv.[1])
    add_func "string_append" ty_sss 2 string_append_func
    add_func "^^" ty_sss 2 string_append_func

    let array_get_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vstring (s, _) ->
            let i = to_int argv.[1]
            if 0 <= i && i < s.Length then
                of_char rt s.[i]
            else mal_raise_IndexOutOfRange()
        | Varray _ ->
            try array_get rt (argv.[0]) (to_int argv.[1])
            with :? IndexOutOfRangeException -> mal_raise_IndexOutOfRange()
        | _ -> dontcare()
    let ty_array_get = arrow2 (ty_array a) ty_int a
    add_func ".[]" ty_array_get 2 array_get_func
    add_func "array_get" ty_array_get 2 array_get_func

    let array_set_func (g : runtime) (argv : value array) =
        try
            array_set argv.[0] (to_int argv.[1]) argv.[2];
            Value.unit
        with :? IndexOutOfRangeException -> mal_raise_IndexOutOfRange ()
    let ty_array_set = arrow3 (ty_array a) ty_int a ty_unit
    add_func ".[]<-" ty_array_set 3 array_set_func
    add_func "array_set" ty_array_set 3 array_set_func

    let array_length_func (g : runtime) argv =
        match argv with
        | [| Varray a |] -> of_int g a.count
        | _ -> dontcare()
    add_func "array_length" (arrow (ty_array a) ty_int) 1 array_length_func

    let array_copy_func (rt : runtime) (argv : value array) =
        array_copy rt argv.[0]
    add_func "array_copy" (arrow (ty_array a) (ty_array a)) 1 array_copy_func

    let array_sub_func (rt : runtime) (argv : value array) =
        let start = to_int argv.[1]
        let count = to_int argv.[2]
        match argv.[0] with
        | Varray ary ->
            if not (0 <= count && 0 <= start && start + count <= ary.count) then mal_raise_IndexOutOfRange ()
            let sub = array_create rt count
            match sub with
            | Varray subary ->
                if not (isNull ary.storage) then
                    Array.blit ary.storage start subary.storage 0 count
                subary.count <- count
                sub
            | _ -> dontcare ()
        | _ -> dontcare()
    add_func "array_sub" (arrow3 (ty_array a) ty_int ty_int (ty_array a)) 3 array_sub_func

    let array_blit_func (rt : runtime) (argv : value array) =
        let src = argv.[0]
        let i = to_int argv.[1]
        let dst = argv.[2]
        let j = to_int argv.[3]
        let count = to_int argv.[4]
        match src, dst with
        | Varray { count = src_count }, Varray { count = dst_count } ->
            if not (0 <= i && i + count <= src_count && 0 <= j && j + count <= dst_count) then mal_raise_IndexOutOfRange ()
            if count = 0 then unit
            else
                match src, dst with
                | Varray { storage = src_storage }, Varray { storage = dst_storage } ->
                    for k = 0 to count - 1 do
                        dst_storage.[j+k] <- src_storage.[i+k]
                    unit
                | _ -> dontcare()
        | _ -> dontcare ()
    add_func "array_blit" (arrow5 (ty_array a) ty_int (ty_array a) ty_int ty_int ty_unit) 5 array_blit_func

    let string_length_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vstring (s, _) -> of_int rt s.Length
        | _ -> dontcare()
    add_func "string_length" (arrow ty_string ty_int) 1 string_length_func

    let string_of_char_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vint (i, _) -> of_string rt (String(char i, 1))
        | _ -> dontcare()
    add_func "string_of_char" (arrow ty_char ty_string) 1 string_of_char_func

    let string_of_char_array_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Varray ary ->
            let sb = StringBuilder(ary.count)
            for i = 0 to ary.count - 1 do
                match ary.storage.[i] with
                | Vint (i, _) -> sb.Add(char i)
                | _ -> dontcare()
            of_string rt (sb.ToString())
        | _ -> dontcare()
    add_func "string_of_char_array" (arrow (ty_array ty_char) ty_string) 1 string_of_char_array_func

    let char_array_of_string_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vstring (s, _) ->
            let v = array_create rt s.Length
            match v with
            | Varray ary ->
                for i = 0 to s.Length - 1 do
                    ary.storage.[i] <- of_int rt (int s.[i])
                ary.count <- s.Length
                v
            | _ -> dontcare()
        | _ -> dontcare()
    add_func "char_array_of_string" (arrow ty_string (ty_array ty_char)) 1 char_array_of_string_func

    let string_concat_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Varray ary ->
            let sb = StringBuilder()
            for i = 0 to ary.count - 1 do
                match ary.storage.[i] with
                | Vstring(s, _) -> sb.Add(s)
                | _ -> dontcare()
            of_string rt (sb.ToString())
        | _ -> dontcare()
    add_func "string_concat" (arrow (ty_array ty_string) ty_string) 1 string_concat_func

    let print_string_func (rt : runtime) (argv : value array) =
        rt.print_string (to_string argv.[0])
        Value.unit
    add_func "print_string" (arrow (ty_string) ty_unit) 1 print_string_func

    let newline_func (g : runtime) argv =
        match argv with
        | [| _ |] ->
            g.print_string "\r\n"
            Value.unit
        | _ -> Value.unit
    add_func "newline" (arrow ty_unit ty_unit) 1 newline_func

    add_i "int_min" System.Int32.MinValue
    add_i "int_max" System.Int32.MaxValue

    add_if "float" (fun n -> float n)
    add_fi "round" (fun x -> int (round x))

    add_ff "exp" exp
    add_ff "log" log
    add_ff "sqrt" sqrt
    add_ff "sin" sin
    add_ff "cos" cos
    add_ff "tan" tan
    add_ff "asin" asin
    add_ff "acos" acos
    add_ff "atan" atan
    add_ff "abs" abs

    add_vvb "==" LanguagePrimitives.PhysicalEquality
    add_vvb "!=" (fun a b -> not (LanguagePrimitives.PhysicalEquality a b))

    let array_add_func (rt : runtime) argc =
        match argc with
        | [| ary; x |] ->
            array_add rt ary x
            Value.unit
        | _ -> dontcare()
    add_func "array_add" (arrow2 (ty_array a) a ty_unit) 2 array_add_func
    add_func "<<" (arrow2 (ty_array a) a ty_unit) 2 array_add_func

    let array_remove_at_func (rt : runtime) (argv : value array) =
        try
            array_remove_at rt argv.[0] (to_int argv.[1])
            Value.unit
        with :? IndexOutOfRangeException -> mal_raise_IndexOutOfRange()
    add_func "array_remove_at" (arrow2 (ty_array a) ty_int ty_unit) 2 array_remove_at_func

    let array_clear_func (rt : runtime) (argv : value array) =
        array_clear rt argv.[0]
        unit
    add_func "array_clear" (arrow (ty_array a) ty_unit) 1 array_clear_func
    
    let random = Random()

    let random_int_func (rt : runtime) argv =
        match argv with
        | [| Vint (n, _) |] ->
            try
                of_int rt (random.Next(n))
            with :? ArgumentOutOfRangeException -> mal_failwith rt "random_int に無効な引数が与えられました"
        | _ -> dontcare()
    add_func "random_int" (arrow ty_int ty_int) 1 random_int_func 

    let random_float_func (rt : runtime) argv =
        of_float rt (random.NextDouble())
    add_func "random_float" (arrow ty_unit ty_float) 1 random_float_func

    let ty_uu = arrow ty_unit ty_unit
    let add_uu name (func : runtime -> unit) =
        let builtin_func (rt : runtime) (argv : value array) = 
            func rt
            unit
        add_func name ty_uu 1 builtin_func
    
    add_uu "memstat" (fun rt ->
        let process_memory_bytes = GC.GetTotalMemory(false) 
        let mal_memory_bytes = System.Threading.Volatile.Read(rt.memory_counter)

        let sb = StringBuilder()
        let pf fmt = Printf.bprintf sb fmt
        pf "total managed memory: %d\r\n" process_memory_bytes
        pf "total mal values memory: %d\r\n" mal_memory_bytes
        pf "used: %d%%\r\n" (int (100.0 * float mal_memory_bytes / float rt.config.bytes_stop_exec))
        rt.print_string (sb.ToString()))

    add_uu "collect" (fun g -> collect ())

    let print_uvalue_func (rt : runtime) (argv : value array) =
        if argv.Length <> 1 then dontcare()
        else
            let s = 
                if box argv.[0] = null
                then "<null>\r\n"
                else Printf.sprintf "%A\r\n" argv.[0]
            rt.print_string s
            Value.unit
    add_func "print_uvalue" (arrow a ty_unit) 1 print_uvalue_func

    let string_of_float_func (g : runtime) (argv : value array) =
        match argv with
        | [| Vfloat (x, _) |] ->
            of_string g (Misc.string_of_float x)
        | _ -> dontcare()
    add_func "string_of_float" (arrow ty_float ty_string) 1 string_of_float_func

    let float_of_string_func (rt : runtime) (argv : value array) =
        match argv with
        | [| v |] ->
            let s = to_string v
            match Double.TryParse s with
            | true, x -> of_float rt x
            | false, _ -> mal_failwith rt "float_of_string: Invalid argument."
        | _ -> dontcare()
    add_func "float_of_string" (arrow ty_string ty_float) 1 float_of_string_func

    let char_of_int_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vint (i, _) ->
            if int Char.MinValue <= i && i <= int Char.MaxValue then
                argv.[0]
            else mal_failwith rt "char_of_int: given int is out of range."
        | _ -> dontcare()
    add_func "char_of_int" (arrow ty_int ty_char) 1 char_of_int_func

    let int_of_char_func (rt : runtime) (argv : value array) =
        match argv.[0] with
        | Vint _ -> argv.[0]
        | _ -> dontcare()
    add_func "int_of_char" (arrow ty_char ty_int) 1 int_of_char_func
    
    let raise_func (rt : runtime) (argv : value array) =
        match argv with
        | [| exn |] -> raise (MALException exn)
        | _ -> dontcare()

    add_func "raise" (arrow ty_exn a) 1 raise_func
    
    add_func "hash" (arrow a ty_int) 1 (fun rt argv -> of_int rt (to_hash argv.[0]))

    (tyenv, genv, alloc)

let tyenv_std, genv_std, alloc_std = add_stdlib Types.tyenv_basic [||] (Allocator.Create())
