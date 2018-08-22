open System
open System.IO

let paths =
    let l = Array.concat [
        Directory.GetFiles(Environment.CurrentDirectory, "*.fs");
        Directory.GetFiles(Environment.CurrentDirectory, "*.fsy");
        Directory.GetFiles(Environment.CurrentDirectory, "*.fsl")]
    let exclude = [| "Parser.fs"; "Lexer.fs"; "Parsing.fs"; "Lexing.fs" |]
    Array.filter (fun path -> not (Array.contains (Path.GetFileName(path)) exclude)) l

let p = printfn "%-15s %6d %-7s"

let newline_scan (s : string) =
    let mutable crlf = 0
    let mutable lf = 0
    let mutable i = 0

    while i < s.Length do
        let c0 = s.[i]
        match c0 with
        | '\n' ->
            lf <- lf + 1
            i <- i + 1
        | '\r' ->
            if i + 1 < s.Length then
                let c1 = s.[i + 1]
                match c1 with
                | '\n' ->
                    crlf <- crlf + 1
                    i <- i + 2
                | _ ->
                    i <- i + 1
            else
                i <- i + 1
        | _ -> i <- i + 1
    
    match crlf, lf with
    | 0, 0 -> "UNKNOWN"
    | _, 0 -> "CRLF"
    | 0, _ -> "LF"
    | _, _ -> "MIXED"

let items =
    Array.map (fun path ->
        let s = File.ReadAllText(path)
        let lines = s.Split([|"\n"; "\r\n"|], StringSplitOptions.None).Length
        let newline = newline_scan s
        (path, lines, newline)) paths
    |> Array.sortByDescending (fun (_, lines, _) -> lines)
let total = Array.sum (Array.map (fun (_, lines, _) -> lines) items)

for (path, lines, newline) in items do
    p (Path.GetFileName path) lines newline

printfn ""

p "Total" total ""

