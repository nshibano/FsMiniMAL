open System

open FsMiniMAL.Value

[<EntryPoint>]
let main argv =

    printfn "Is64BitProcess : %b" (IntPtr.Size = 8)

    let get_total_memory () =
        GC.Collect()
        GC.WaitForPendingFinalizers()
        GC.Collect()
        GC.GetTotalMemory(true)
        
    let many = 1000

    let test constr =
        let ary = Array.zeroCreate<value> many
        let x0 = get_total_memory()
        for i = 0 to ary.Length - 1 do
            ary.[i] <- constr dummy_runtime i
        let x1 = get_total_memory()
        ary.[0] |> ignore // To keep ary in scope. In release build this changes result.
        float (x1 - x0) / float many
        
    let sizeof_int = test (fun rt i -> of_int rt i)
    let sizeof_float = test (fun rt i -> of_float rt (float i))

    let sizeof_block_len0 = test (fun rt i -> block_createrange rt 0 (Array.create 0 unit))
    let sizeof_block_len1000 = test (fun rt i -> block_createrange rt 0 (Array.create 1000 unit))
    let block_overhead = sizeof_block_len0
    let block_increment = (sizeof_block_len1000 - sizeof_block_len0) / 1000.0

    let sizeof_array_cap0 = test (fun rt i -> array_create rt 0)
    let sizeof_array_cap1000 = test (fun rt i -> array_create rt 1000)
    let array_overhead = sizeof_array_cap0
    let array_increment = (sizeof_array_cap1000 - sizeof_array_cap0) / 1000.0

    // We don't use String('a', 0) here because it returns shared constant object.
    let sizeof_string_len1 = test (fun rt i -> of_string rt (String('a', 1))) 
    let sizeof_string_len1000 = test (fun rt i -> of_string rt (String('a', 1000)))
    let string_increment = (sizeof_string_len1000 - sizeof_string_len1) / 999.0
    let string_overhead = sizeof_string_len1 - string_increment

    printfn "sizeof int: %.1f" sizeof_int
    printfn "sizeof float: %.1f" sizeof_float
    printfn "block overhead: %.1f" sizeof_block_len0
    printfn "block increment: %.1f" block_increment
    printfn "array overhead: %.1f" sizeof_array_cap0
    printfn "array increment: %.1f" array_increment
    printfn "string overhead: %.1f" string_overhead
    printfn "string increment: %.1f" string_increment

    Console.ReadKey() |> ignore
    0
