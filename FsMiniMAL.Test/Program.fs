open System
open Printf

open FsMiniMAL

[<EntryPoint>]
let main argv = 

    let topcase source answer =
        let mal = Interpreter()
        mal.Do (source)
        match mal.State with
        | State.Finished ->
            let value, ty = mal.Result
            let result = Printer.print_value_without_type mal.TypeEnv 10000 ty value
            if result = answer then
                ()
            else
                printfn "Test failed."
                printfn "Source: %s" source
                printfn "Expected %s but %s." answer result
        | State.StoppedDueToError ->
            printfn "Test failed (mal error)."
            printfn "Source: %s" source
        | State.Running ->
            printfn "Test failed (interpreter crashed)."
            printfn "Source: %s" source
        | _ -> failwith ""

    let case source answer =
        topcase source answer
        topcase (String.Concat("begin ", source, " end")) answer
    
    let type_error source = 
        let mal = Interpreter()
        try mal.Do (source) with _ -> ()
        if mal.State = State.StoppedDueToError && (match mal.Error with Error.TypeError _ -> true | _ -> false) then
            ()
        else
            printfn "Test failed. (expected type error)"
            printfn "Source: %s" source

    let fails_safely source =
        let mal = Interpreter({ FsMiniMAL.Value.config.Default with maximum_stack_depth = 1000; bytes_trigger_gc = 20000; bytes_stop_exec = 10000 })
        try
            mal.Do (source)
            if mal.State = State.Finished then
                printfn "Test failed. Should fail safely but succeeded."
                printfn "Source: %s" source
        with exn ->
            printfn "Test failed. Should fail safely but raises exception."
            printfn "Source: %s" source
            printfn "exn: %s %s" (exn.GetType().Name) exn.Message
    
    let timeout slice source =
        let mal = Interpreter()
        mal.Start(source)
        mal.Run(slice)
        if mal.State = State.Running then ()
        else
            printfn "Test failed. Should timeout but didn't."
            printfn "Source: %s" source

    let keep_shadowed_globals_after_failure () =
        let mal = Interpreter() 
        mal.Do("val n = 100")
        mal.Do("val n = 200 / 0")
        mal.Do("n")

        let value, ty = mal.Result
        let result = Printer.print_value_without_type mal.TypeEnv 10000 ty value
        if result = "100" then
            ()
        else
            printfn "Test keep_shadowed_globals_after_failure failed."

    let apply_side_effects_on_tyenv_even_if_execution_failed () =
        let mal = Interpreter() 
        mal.Do("val a = [||]")
        mal.Do("begin add a 100; 1 / 0 end")
        mal.Do("a.[0]")

        let value, ty = mal.Result
        let result = Printer.print_value_without_type mal.TypeEnv 10000 ty value
        if result = "100" then
            ()
        else
            printfn "Test apply_side_effects_on_tyenv_even_if_execution_failed failed."
    
    let int_min = "-2147483648"

    let sw = System.Diagnostics.Stopwatch.StartNew()

    case "()" "()"
    case "true" "true"
    case "false" "false"
    case "1" "1"
    case "-1" "-1"
    case int_min int_min
    case "1.0" "1.0"
    case "nan" "nan"
    
    case "Some 0" "Some 0"
    case "Some (-1)" "Some (-1)"
    case "Some (1, 1)" "Some (1, 1)"
    case "Some (1, -1)" "Some (1, -1)"
    case "Some (-1, 1)" "Some (-1, 1)"
    case "Some (-1, -1)" "Some (-1, -1)"

    case "1 + 1" "2"
    case "1.0 / 3.0" "0.33333333333333331"

    case "1 = 1" "true"
    case "1 = 2" "false"
    
    case "1 <> 1" "false"
    case "1 <> 2" "true"

    case "1 < 2" "true"
    case "1 < 1" "false"
    case "2 < 1" "false"

    case "1 > 2" "false"
    case "1 > 1" "false"
    case "2 > 1" "true"

    case "1 <= 2" "true"
    case "1 <= 1" "true"
    case "2 <= 1" "false"

    case "1 >= 2" "false"
    case "1 >= 1" "true"
    case "2 >= 1" "true"

    case "nan = nan" "false"
    case "nan <> nan" "true"
    case "nan = 0.0" "false"
    case "nan <> 0.0" "true"

    case "(); 1" "1"
    case "val x = 1; x + x" "2"
    case "var x = 0; x <- x + 1; x " "1"
    case "fun f x = x + 1; f 0" "1"
    case "val x = 1; fun f y = x + y; val x = 2; f 3" "4"
    case "var n = 0; n <- n + 1; n <- n + 1; n" "2"
    case "fun f n = n + n; fun g n = f n + n; g 10" "30"

    case "fun fib n = if n <= 2 then 1 else fib (n-1) + fib (n-2); fib 20" "6765"

    case "1.0 + 0.5" "1.5"

    case "\"hello\"" "\"hello\""
    case "\"hello\" ^ \" world\"" "\"hello world\""

    case "var n = 0; for i = 1 to 1000 do n <- n + i; n" "500500"

    case "val a = [||]; for i = 2147483647 to 2147483647 do array_add a i; a" "[|2147483647|]"
    case "val a = [||]; for i = 2147483646 to 2147483647 do array_add a i; a;" "[|2147483646, 2147483647|]"
    case "val a = [||]; for i = 2147483645 to 2147483647 do array_add a i; a;" "[|2147483645, 2147483646, 2147483647|]"

    case "val a = [||]; for i = 2147483647 downto 2147483647 do array_add a i; a" "[|2147483647|]"
    case "val a = [||]; for i = 2147483647 downto 2147483646 do array_add a i; a" "[|2147483647, 2147483646|]"
    case "val a = [||]; for i = 2147483647 downto 2147483645 do array_add a i; a" "[|2147483647, 2147483646, 2147483645|]"

    case "val a = [||]; for i = 2147483647 to 2147483646 do array_add a i; a" "[||]"
    case "val a = [||]; for i = 2147483646 downto 2147483647 do array_add a i; a" "[||]"

    case "val a = [||]; for i = -2147483648 to -2147483648 do array_add a i; a" "[|-2147483648|]"
    case "val a = [||]; for i = -2147483648 to -2147483647 do array_add a i; a" "[|-2147483648, -2147483647|]"
    case "val a = [||]; for i = -2147483648 to -2147483646 do array_add a i; a" "[|-2147483648, -2147483647, -2147483646|]"

    case "val a = [||]; for i = -2147483648 downto -2147483648 do array_add a i; a" "[|-2147483648|]"
    case "val a = [||]; for i = -2147483647 downto -2147483648 do array_add a i; a" "[|-2147483647, -2147483648|]"
    case "val a = [||]; for i = -2147483646 downto -2147483648 do array_add a i; a" "[|-2147483646, -2147483647, -2147483648|]"

    case "val a = [||]; for i = -2147483647 to -2147483648 do array_add a i; a" "[||]"
    case "val a = [||]; for i = -2147483648 downto -2147483647 do array_add a i; a" "[||]"

    case "var sum = 0; var i = 0; while i <= 100 do begin sum <- sum + i; i <- i + 1 end; sum" "5050"

    case "[|1,2,3,4,5|]" "[|1, 2, 3, 4, 5|]"
    case "[1,2,3]" "[1, 2, 3]"
    case "[[[[]]]]" "[[[[]]]]"
    case "[|[|[|[||]|]|]|]" "[|[|[|[||]|]|]|]"

    case "fun f a b c d e f g h i j k l m n = a + b + c + d + e + f + g + h + i + j + k + l + m + n; f 1 2 3 4 5 6 7 8 9 10 11 12 13 14" "105"
    case "fun f a b c d e f g h i j k l m n = a + b + c + d + e + f + g + h + i + j + k + l + m + n; val g = f 1 2 3 4 5; val h = g 6 7 8 9 10; h 11 12 13 14" "105"
    case "(fn a -> (fn b -> (fn c -> (fn d -> [|a, b, c, d|])))) 1 2 3 4" "[|1, 2, 3, 4|]"

    case "array_get [| (fn a -> (fn b -> [a, b])) |] 0 1 2" "[1, 2]" // apply builtin which returns closure at once
    case "(fn a -> ( + )) 0 1 2" "3" // apply closure which returns builtin at once

    case """kprintf (fn s -> ( + )) "hello %f" 1.0 3 7""" "10"
    case "val x = 1; val f = begin val y = 2; begin fun f z = x + y + z; f end end; f 3" "6"
    case "val t = (1, 2); val (y, x) = t; (x, y)" "(2, 1)"
    case " case 1 + 1 of 1 -> false | 2 -> true | n -> false" "true"

    case "case 3 of 1 -> 1 | 2 -> 4 | n -> n * n" "9"
    case "case true || false of true -> 1 | false -> 0" "1"
    case "case [| 1, 2, 3 |] of [| i, j |] -> 0 | [| i, j, k |] -> i + j + k" "6"
    case """case "bar" of "foo" -> 1  | "bar" -> 2 | "baz" -> 3""" "2"

    case "false && (1 / 0) = 0" "false"
    case "true || (1 / 0) = 0" "true"
    case "(( || ) false) true" "true"
    case "(( && ) true) false" "false"

    // short-circuit tests
    case "var x = false; var y = false; (begin x <- true; false end) && (begin y <- true; false end); (x, y)" "(true, false)"
    case "var x = false; var y = false; (begin x <- true; true  end) || (begin y <- true; true  end); (x, y)" "(true, false)"
    case "var x = false; var y = false; ( && ) (begin x <- true; false end) (begin y <- true; false end); (x, y)" "(true, false)"
    case "var x = false; var y = false; ( || ) (begin x <- true; true  end) (begin y <- true;  true end); (x, y)" "(true, false)"
    case "var x = false; var y = false; val f = ( && ); f (begin x <- true; false end) (begin y <- true; false end); (x, y)" "(true, true)"
    case "var x = false; var y = false; val f = ( || ); f (begin x <- true; true  end) (begin y <- true; true  end); (x, y)" "(true, true)"

    case "begin begin begin 123 end end end" "123"

    case "[|0|].[0]" "0"
    case "1+1" "2"
    case "3-2" "1"
    case "7*4" "28"
    case "15/3" "5"
    case "27 % 6" "3"
    case "-3" "-3"
    case "10 ||| 1 ||| 4" "15"
    case "11 ^^^ 8" "3"
    case "10 &&& 3" "2"
    case "3.0 + 2.5" "5.5"
    case "2.0 ** 3.0" "8.0"
    case "1e10" "10000000000.0"
    case "1e-5" "1e-05"
    case "-10.0 * - 7.0" "70.0"
    case "1 = 1" "true"
    case "2 <= 2" "true"
    case "2 < 2" "false"
    case "true && true" "true"
    case "true && false" "false"
    case "not false" "true"
    case "[1,2,3] @ [4,5,6]" "[1, 2, 3, 4, 5, 6]"
    case """[| "foo", "bar", "baz" |].[1]""" "\"bar\""

    case "val a = [| false, false, false |]; a.[2] <- true; a" "[|false, false, true|]"

    topcase "type foobar = Foo | Bar; [|Foo, Bar|]" "[|Foo, Bar|]"

    topcase "
    type foobar = Foo | Bar of int;
    val a = [| Foo, Foo, Bar 1, Bar 2 |];
    fun f x = case x of
        | Foo -> 1
        | Bar n -> n * 100;
    var sum = 0;
    for i = 0 to length a - 1 do
        sum <- sum + f a.[i];
    sum" "302"

    case "begin val n = 1; val n = n + n; val n = n + n; n end;" "4"

    case "printf \"age: %d\" 31" "()"

    case "compare (-infinity) nan" "1"
    case "compare [| 0, 0 |] [|  1 |]" "1"
    case "compare [| 0, 0 |] [| -1 |]" "1"
    case "compare [| nan, 1.0 |] [| nan, 1.0 |]" "0"
    case "compare [| nan, 2.0 |] [| nan, 1.0 |]" "1"
    case "compare [| -infinity, 0.0 |] [| nan, 1.0 |]" "1"
    case "compare [| nan, 0.0 |] [| nan, 1.0 |]" "-1"
    topcase "type foobar = Foo | Bar of int; compare (Bar 1) Foo" "1"
    case "try_compare nan 0.0" int_min
    case "try_compare nan infinity" int_min
    case "try_compare nan (-infinity)" int_min
    case "try_compare nan nan" int_min
    case "try_compare [| nan, 1.0 |] [| nan, 1.0 |]" int_min
    case "try_compare [| nan, 2.0 |] [| nan, 1.0 |]" int_min
    case "try_compare [||] [||]" "0"
    case "val y = try_compare; y 0 1" "-1"
    case "var n = 100; n <- n + 23; n" "123"

    type_error "printf \"%x%y%z\""  // invalid format string

    fails_safely "
    type cons = Cons of cell | Nil and cell = { mutable content : cons };
    val cell = { content = Nil };
    val cons = Cons cell;
    cell.content <- cons;
    compare cons cons"

    fails_safely "case 3 of Foo -> 3"

    case """case (1, 2) of (a, b) when a = b -> "=" | (i, j) when i < j -> "<" | _ -> "other" """ "\"<\""

    type_error "case (1.0, 2.0) of (a, b) when a = b  -> () | (x, y) when a < b -> ()"

    fails_safely "val a = [||]; while true do array_add a 1.0" // this will be out of memory

    topcase "type foobar = Foo | Bar of int; val l = [ Foo, Bar 100 ]; hide foobar; l" "[<abstract>, <abstract>]"

    topcase "type 'a mylist = Cons of ('a * 'a mylist) | Nil; Cons (1, Cons (2, Cons (3, Nil)))" "Cons (1, Cons (2, Cons (3, Nil)))"

    type_error "type foo == foo"
    type_error "type foo == foo list"
    type_error "type foo == bar and bar == foo"
    type_error "type foo == bar and bar == foo list"
    type_error "type 'a foo == foo foo"

    case "val i = 0; case (1, 2) of (i, 3) -> 4 | _ -> i" "0"

    case """val x = 1; try failwith "error" catch Failure "error" -> x + 100""" "101"
    case """try failwith "Error" catch Failure msg -> msg""" "\"Error\""
    topcase "exception FooException of int * int; try raise (FooException (1,2)) catch Failure _ -> 0 | FooException (n, m) -> n + m" "3"

    case "val a = 1 and b = 2; a + b" "3"
    case "var a = 1 and b = 2; a + b" "3"

    fails_safely "type myint == int; (0.0 : myint)"

    topcase "type rec1 = { rec1_field : int ref }; val x = { rec1_field = ref 0 }; !x.rec1_field" "0" // syntax check. dot vs deref.
    
    keep_shadowed_globals_after_failure ()
    apply_side_effects_on_tyenv_even_if_execution_failed ()

    fails_safely "array_create (1000 * 1000* 1000) 0"
    fails_safely "array_create (1000 * 1000* 1000) 0.0"
    fails_safely "array_create (-1) 0"

    case "\"foo\" ^ \"bar\"" "\"foobar\""

    case "[||] ^ [||]" "[||]"
    case "[|1,2,3|] ^ [||]" "[|1, 2, 3|]"
    case "[||] ^ [|4,5,6|]" "[|4, 5, 6|]"
    case "[|1,2,3|] ^ [|4,5,6|]" "[|1, 2, 3, 4, 5, 6|]"

    case "[||] ^ [||]" "[||]"
    case "[|1.0,2.0,3.0|] ^ [||]" "[|1.0, 2.0, 3.0|]"
    case "[||] ^ [|4.0,5.0,6.0|]" "[|4.0, 5.0, 6.0|]"
    case "[|1.0,2.0,3.0|] ^ [|4.0,5.0,6.0|]" "[|1.0, 2.0, 3.0, 4.0, 5.0, 6.0|]"

    case """ "foo" ^ "bar" """ "\"foobar\""
    case """ "foo" ^^ "bar" """ "\"foobar\""

    case "fun array_map2 a f = array_map f a; array_map2 [| 0.0 |] (fn x -> x + x)" "[|0.0|]" // allow this without type annotation for x

    case "kprintf (fn s -> 3); ()" "()"

    topcase "fun f x = (x : 'a); f 0; f 0.0" "0.0"
    type_error "begin fun f x = (x : 'a); f 0; f 0.0 end"

    case "begin end" "()"

    case "fun f x : float = x + x; f 1.0" "2.0"
    case "(( + ) 1.0) 1.0" "2.0"
    case "(( + ) : float -> float -> float) 1.0 1.0" "2.0"

    case "fun f x = 2.0 * x * x; f 3.0" "18.0"

    topcase "type foo = { mutable foo : foo option }; val x = {foo = None}; x.foo <- Some x; x" "{foo = Some ...}"
        
    timeout 1000L "while true do ()"
    timeout 1000L "var n = 0; while true do n <- n + 1"

    topcase "type foo1 = { foo : int }; type foo2 = { foo : int }; ({ foo = 0 } : foo1); ()" "()" // Accept this with no type error.
    topcase "type foo1 = Foo of int; type foo2 = Foo of int; ((Foo 0) : foo1); ()" "()" // Accept this with no type error.

    topcase "type foo1 = { foo : int }; type foo2 = { foo : string }; (fn (x : foo1) -> x.foo + 1); ()" "()" // Accept this with no type error.
    topcase "type foo1 = Foo of int; type foo2 = Foo of string; (fn x -> case (x : foo1) of Foo x -> x); ()" "()" // Accept this with no type error.

    topcase "type foo1 = { foo : int }; type foo2 = { foo : int }; (fn ({ foo = n } : foo1) -> n); ()" "()"
    type_error "fun p i = 10e-3 * i * i; p 0"

    case "fun f x : float = x + x; f 1.0" "2.0"
    case "fun f (x : float) = x + x; f 1.0" "2.0"
    case "val f = ((fn x -> x + x) : float -> 'a); f 1.0" "2.0"
    case "val f = ((fn x -> x + x) : 'a -> float); f 1.0" "2.0"

    printfn "Done."
    //printfn "Elapsed: %d (ms)" sw.ElapsedMilliseconds
    printfn "Press any key to close."
    Console.ReadKey() |> ignore
    0
