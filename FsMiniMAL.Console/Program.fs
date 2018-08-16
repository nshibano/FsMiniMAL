open System
open System.Diagnostics
open System.Threading
open System.IO

open FsMiniMAL

[<EntryPoint>]
let main argv =

    let lang =
        match System.Globalization.CultureInfo.CurrentCulture.Name with
        | "ja-JP" -> Ja
        | _ -> En

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
        
    let mal = Interpreter()
    mal.PrintString<- Console.Write
    
    Console.WriteLine("> FsMiniMAL")
    Console.WriteLine("")

    let lock l f =
        Monitor.Enter(l)
        let result = f()
        Monitor.Exit(l)
        result

    Console.CancelKeyPress.Add(fun ev ->
            lock mal (fun () -> 
                if mal.IsRunning then
                    mal.Cancel())
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
                if mal.IsRunning then
                    if mal.IsSleeping && DateTime.Now < mal.Wakeup then
                        Thread.Sleep(100)
                    else
                        mal.Run(1000L)
                    true
                else
                    if mal.State = State.Failure then
                        Console.Write(mal.StringOfError(lang, 80, mal.Error))
                    false) do ()
    0