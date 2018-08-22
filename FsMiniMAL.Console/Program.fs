open System
open System.Diagnostics
open System.Threading
open System.IO
open System.Text

open FsMiniMAL

[<EntryPoint>]
let main argv =

    let lang =
        match System.Globalization.CultureInfo.CurrentCulture.Name with
        | "ja-JP" -> Printer.Ja
        | _ -> Printer.En

    let history =
        let path = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments), "mal_history.txt")
        try
            let f =new StreamWriter(path, true)
            f.WriteLine("// " + DateTime.Now.ToString())
            f.Flush()
            printfn "Command history is saved to %s" path
            Some f
        with _ ->
            printfn "!!! Failed to open history file. !!!"
            None
        
    let mal = Top.createInterpreter()
    mal.MessageHook <- (fun msg -> Console.Write(FsMiniMAL.Printer.print_message lang (Console.WindowWidth - 1) msg))
    mal.PrintString<- Console.Write
    
    Console.WriteLine("> FsMiniMAL")
    Console.WriteLine("")

    let lock l f =
        Monitor.Enter(l)
        let result = f()
        Monitor.Exit(l)
        result

    Console.CancelKeyPress.Add(fun ev ->
            lock mal (fun () -> mal.Cancel())
            ev.Cancel <- true)

    while true do
        Console.Write("# ")
        let s = Console.ReadLine()
        Option.iter (fun (f : StreamWriter) ->
            f.WriteLine(s)
            f.Flush()) history

        if isNull s then
            exit 0
        else
            lock mal (fun () -> mal.Start(s))

        while
            lock mal (fun () ->
                match mal.State with
                | State.Running ->
                    if mal.IsSleeping && DateTime.Now < mal.Wakeup then
                        Thread.Sleep(100)
                    else
                        mal.Run(1000L)
                    true
                | State.Success ->
                    false
                | State.Failure ->
                    match mal.LatestMessage with
                    | Some (Message.UncaughtException (tyenv, exn)) ->
                        let sb = StringBuilder()
                        mal.Stacktrace(10, sb)
                        Console.Write(sb.ToString())
                    | _ -> ()
                    false
                | _ -> dontcare()) do ()
    0