open System
open System.IO
open System.Diagnostics

open FsMiniMAL

type Stopwatch with
    member this.ElapsedMicroseconds = int64 ((1000000I * bigint this.ElapsedTicks) / bigint Stopwatch.Frequency)

[<EntryPoint>]
let main argv =
    printfn "> 64bit process: %A" Environment.Is64BitProcess
    printfn "> Debugger attached: %A" System.Diagnostics.Debugger.IsAttached

    let mal = Interpreter()
    mal.Do("
fun fib n =
    if n <= 1 then
        n
    else
        fib (n - 1) + fib (n - 2)

fun integ n =
  begin
    val dx = 1.0 / float n;
    fun f x = 3.0 * x * x;
    var accu = 0.0;
    accu <- accu + 0.5 * f 0.0;
    for i = 1 to n - 1 do
      begin
        val x = float i * dx;
        accu <- accu + f x;
      end;
    accu <- accu + 0.5 * f 1.0;
    accu * dx
  end;

fun vector_loop n =
  begin
    val dx = 1.0 / float (n - 1);
    val a = [||];
    for i = 0 to n - 1 do array_add a 1.0;
    val b = [||];
    for i = 0 to n - 1 do array_add b (float i * dx);
    val c = [||];
    for i = 0 to n - 1 do array_add c (a.[i] + b.[i]);
    c
  end;

fun vector_lambda n =
  begin
    val dx = 1.0 / float (n - 1);
    val a = array_init n (fn _ -> 1.0);
    val b = array_init n (fn i -> float i * dx);
    val c = array_init n (fn i -> a.[i] + b.[i]);
    c
  end;

type 'a node =
  | Nil
  | Node of 'a node_fields

and 'a node_fields =
  { level : int,
    left : 'a node,
    value : 'a,
    right : 'a node };

fun skew node =
  case node of
  | Node { level = level, left = Node { level = left_level, left = a, value = x, right = b }, value = y, right = c } when level = left_level ->
      Node { level = level, left = a, value = x, right = skew (Node { level = level, left = b, value = y, right = c })}
  | _ -> node;

fun level_of node =
  case node of
  | Nil -> 0
  | Node { level = level } -> level;

fun split node =
  case node of
  | Node { level = level, left = a, value = x, right = Node {level = right_level, left = b, value = y, right = c}} when level = level_of c ->
      Node { level = level + 1, left = Node { level = level, left = a, value = x, right = b }, value = y, right = split c }
  | _ -> node;

fun balance node = split (skew node);

fun add node x =
  case node of
  | Nil -> Node { level = 1, left = Nil, value = x, right = Nil }
  | Node fields ->
    if x < fields.value then
      balance (Node { level = fields.level, left = add fields.left x, value = fields.value, right = fields.right })
    else if fields.value < x then
      balance (Node { level = fields.level, left = fields.left, value = fields.value, right = add fields.right x })
    else node;
 
fun aatree n =
  begin
    var tree = Nil;
    for i = 1 to n do
      tree <- add tree i;
    tree
  end;")
    
    let dir = Path.GetDirectoryName(Reflection.Assembly.GetExecutingAssembly().Location)

    let path_ref = Path.Combine(dir, "ref.xml")
    let path_best = Path.Combine(dir, "best.xml")

    let cases = [|
        "integ 100"
        "vector_loop    100"
        "vector_lambda  100"
        "aatree 10"
        "fib 10" |]
    
    let serializer = System.Xml.Serialization.XmlSerializer(typeof<int64 array>)

    let load name (path : string) =
        try
            use reader = new StreamReader(path)
            let data = serializer.Deserialize(reader) :?> int64 array
            printfn "> %s data loaded from %s." name path
            data
        with _ ->
            printfn "> %s data not found. Use dummy value." name
            Array.create cases.Length Int64.MaxValue
    
    let save (name : string) (path : string) (data : int64 array) =
        use writer = new StreamWriter(path)
        serializer.Serialize(writer, data)
        printfn "> %s data saved to %s." name path

    let run repeat =
        printfn "Run (repeat = %d)" repeat
        let ref = load "Ref" path_ref
        let best = load "Best" path_best

        let oldbest = Array.copy best

        printfn ""

        printfn """                     oldbest current     kHz newbest      ref cur/old new/ref"""
        ignore  """"integ 100"          1000000 1000000 1000000 1000000* 1000000    100%    100%"""
        
        let sw = Stopwatch()
        for i = 0 to cases.Length - 1 do
            let mutable cur = Int64.MaxValue
            let mutable accu_malticks = 0L
            let mutable accu_microseconds = 0L
            for j = 0 to repeat - 1 do
                sw.Restart()
                mal.Do(cases.[i])
                sw.Stop()
                if mal.State <> State.Finished then failwith ""
                cur <- min cur sw.ElapsedMicroseconds
                accu_malticks <- accu_malticks + mal.Runtime.stopwatch
                accu_microseconds <- accu_microseconds + sw.ElapsedMicroseconds
            let cur_oldbest = int (Math.Round(100.0 * float cur / float oldbest.[i]))
            let newbest = min cur oldbest.[i]
            best.[i] <- newbest
            let newbest_ref = int (Math.Round(100.0 * float newbest / float ref.[i]))
            let string_of_data x =
                if x <> Int64.MaxValue
                then sprintf "%7d" x
                else "-"
            let kHz = int (1000I * bigint accu_malticks / bigint accu_microseconds)
            printfn "%-20s %7s %7s %7s %7s%1s %7s   %4d%%   %4d%%" ("\"" + cases.[i] + "\"") (string_of_data oldbest.[i]) (string_of_data cur) (string_of_data (int64 kHz)) (string_of_data best.[i]) (if best.[i] < oldbest.[i] then "*" else " ") (string_of_data ref.[i]) cur_oldbest newbest_ref
    
        printfn ""

        if best <> oldbest then
            save "best" path_best best
            printfn "> New best data has been saved to %s." path_best
        else printfn "> No update on best data."

    let default_repeat = 10
    
    let help () =
        printfn "> Enter 'r' or empty line to run test again with default repeat parameter (=%d)." default_repeat
        printfn "> Enter 'r <repeat>' to run test with manual repeat parameter."
        printfn "> Enter 'C' to copy best data to ref data."
        printfn "> Enter 'd' to delete best data."
        printfn "> Enter 'D' to delete ref data."
        printfn "> Enter 'q' to quit."
        printfn "> Enter '?' to show this help message."
    
    run default_repeat

    printfn ""

    help ()
    printf "# "
    let mutable cmd = Console.ReadLine()
    while not (cmd.StartsWith("q")) do
        let words = cmd.Split([| ' '; '\t'; '\r'; '\n' |], StringSplitOptions.RemoveEmptyEntries)
        match words with
        | [||] 
        | [| "r" |] -> run default_repeat
        | [| "r"; n |] when fst (Int32.TryParse(n)) ->
            let n = Int32.Parse(n)
            run n
        | [| "C" |] ->
            if File.Exists(path_best) then
                File.Copy(path_best, path_ref, true)
                printfn "> The best data file (%s) has been copied to ref data path (%s)" path_best path_ref
            else
                printfn "> The best data doesn't exist."
        | [| "d" |] ->
            File.Delete(path_best)
            printfn "> The best data file (%s) has been removed." path_best
        | [| "D" |] ->
            File.Delete(path_ref)
            printfn "> The ref data file (%s) has been removed." path_ref
        | [| "?" |] -> help()
        | _ -> printfn "> Unrecognized command"
        
        printf "# "
        cmd <- Console.ReadLine()

    0
