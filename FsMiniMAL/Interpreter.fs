namespace FsMiniMAL

open System
open System.Collections.Generic
open System.Text
open System.Diagnostics
open Printf

open FsMiniMAL.Lexing
open Syntax
open Types
open Typechk
open Value
open Stdlib
open Translate
open MalLex
open System.Linq.Expressions

type Tag =
    | Start = 0

    | Block_Eval = 1
    
    | Array_Eval = 1
    
    | BlockWith_EvalOrig = 1
    | BlockWith_EvalSets = 2
    
    | Apply_Eval = 1
    | Apply_Apply = 2
    | Apply_Closure = 3
    | Apply_Return = 4
    
    | Begin_Eval = 1
    
    | Case_EvalTest = 1
    | Case_Match = 2
    | Case_EvalWhen = 3
    | Case_EvalResult = 4
    
    | Try_EvalTry = 1
    | Try_EvalCatch = 2
    
    | If_EvalTest = 1
    | If_EvalResult = 2
    
    | Setenvref_Eval = 1
    
    | Forloop_EvalFirst = 1
    | Forloop_EvalLast = 2
    | Forloop_To = 3
    | Forloop_Downto = 4
    
    | While_EvalCond = 1
    | While_EvalBody = 2
    
    | Val_Eval = 1
    
    | Var_Eval = 1

    | Compare_CompareFields = 1
    | ComparisonOperators_CallCompare = 1

type Frame =
    struct
        val mutable code : code
        val mutable frame : obj
    end

type BlockFrame = { mutable pc : Tag; mutable fields : value array; mutable i : int }
type ArrayFrame = { mutable pc : Tag; mutable ary : value; mutable i : int }
type BlockwithFrame = { mutable pc : Tag; mutable fields : value array; mutable i : int; mutable tag : int }
type CompareFrame = { mode : builtin_id; mutable v0 : value; mutable v1 : value; mutable pc : Tag; mutable i : int }
type ApplyFrame = { mutable pc : Tag; mutable i : int; mutable values : value array; mutable oldenv : value array }
type BeginFrame = { mutable pc : Tag; mutable i : int }
type CaseFrame = { mutable pc : Tag; mutable testvalue : value; mutable i : int }
type ForloopFrame = { mutable pc : Tag; mutable i : int; mutable j : int }
type ValVarFrame = { mutable pc : Tag; mutable i : int }

type State =
    | Running = 0
    | Sleeping = 1
    | Finished = 2
    | StoppedDueToError = 3

type Message =
    | TypeError of Typechk.type_error_desc * location
    | EvaluationComplete of tyenv * type_expr * value
    | NewValues of tyenv * (string * value * value_info) list 
    | TypeDefined of Syntax.typedef list
    | ExceptionDefined of string
    | Hide of string
    | Remove of string

type Error =
    | LexicalError of LexHelper.lexical_error_desc * location
    | SyntaxError of location
    | TypeError of Typechk.type_error_desc * location
    | UncaughtException of value
    | MALInsufficientMemory
    | MALStackOverflow
    | EnvSizeLimit

type Interpreter(config : config) as this =

    let mutable state = State.Finished
    let mutable accu : value = unit
    let mutable env : value array = Array.copy genv_std
    let mutable stack = Array.zeroCreate<Frame> 16
    let mutable stack_topidx = -1
    let mutable tyenv = tyenv_clone tyenv_std
    let mutable alloc = alloc_std.Clone()
    let mutable cols = 80
    let mutable error : Error = Unchecked.defaultof<Error>
    let mutable wakeup  = DateTime.MinValue
    let mutable result = (unit, ty_unit)
    let rt =
        { memory_counter = ref 0
          timestamp_at_start = 0L
          cycles = 0L
          print_string = ignore
          config = config }

    let stacktrace limit (sb : StringBuilder) =
        let pfn fmt = Printf.kprintf (fun s -> sb.AppendLine s |> ignore) fmt
        let pfni fmt = Printf.kprintf (fun s ->
            sb.Append("  ") |> ignore
            sb.AppendLine s |> ignore) fmt
        pfn "Stacktrace:"
        let st = min (limit - 1) stack_topidx
        if st <> stack_topidx then
            pfn "  (printing bottom %d frames only)" limit
        for i = st downto 0 do
            match stack.[i].code with
            | UEblock _ -> pfni "Block"
            | UEarray _ -> pfni "Array"
            | UEblockwith _ -> pfni "BlockWith"
            | UEcompare _ -> pfni "Compare"
            | UEapply _ -> pfni "Apply"
            | UEbegin _ -> pfni "Begin"
            | UEcase _ -> pfni "Case"
            | UEtry _ -> pfni "Try"
            | UEif _ -> pfni "If"
            | UEsetenvvar _ -> pfni "Setenvvar"
            | UEfor _ -> pfni "For"
            | UEwhile _ -> pfni "While"
            | UCval _ -> pfni "Val"
            | UCvar _ -> pfni "Var"
            | _ -> pfn "  Error"

    let string_of_error (lang : lang) (cols : int) (err : Error) =
        let buf = new StringBuilder()
        match err with
        | LexicalError (lex_err, loc) ->
            bprintf buf "> %s\r\n  Lexical error (%A).\r\n" (Syntax.describe_location loc) lex_err
        | SyntaxError loc ->
            bprintf buf "> %s\r\n  Syntax error.\r\n" (Syntax.describe_location loc)
        | TypeError (type_err, loc) ->
            bprintf buf "> %s\r\n" (Syntax.describe_location loc)
            bprintf buf "%s\r\n" (Printer.print_typechk_error lang cols type_err)
        | UncaughtException exn_value ->
            buf.Add("UncaughtException: ")
            buf.Add(Printer.print_value_without_type tyenv cols ty_exn exn_value)
            buf.AppendLine() |> ignore
            stacktrace 10 buf
        | MALStackOverflow ->
            buf.Add("StackOverflow\r\n")
            stacktrace 10 buf
        | MALInsufficientMemory ->
            buf.Add("InsufficientMemory\r\n")
        | EnvSizeLimit ->
            bprintf buf "> Size of the global env hits the limit.\r\n"
        buf.ToString()
    
    let default_message_hook (msg : Message) =
        match msg with
        | Message.TypeError (err, loc) -> rt.print_string (string_of_error En 80 (Error.TypeError (err, loc)))
        | Message.EvaluationComplete (tyenv, ty, value)-> rt.print_string (Printer.print_value tyenv 80 ty value + "\r\n")
        | Message.NewValues (tyenv, new_values) ->
            let sb = new StringBuilder()
            for name, value, info in new_values do
                sb.Add (Printer.print_definition tyenv 80 name info value)
                sb.Add("\r\n")
            rt.print_string (sb.ToString())
        | Message.TypeDefined defs -> List.iter (fun def -> rt.print_string (sprintf "Type %s defined.\r\n" def.sd_name)) defs
        | Message.ExceptionDefined name -> rt.print_string (sprintf "Exception %s is defined.\r\n" name)
        | Message.Hide name -> rt.print_string (sprintf "Type %s is now abstract.\r\n" name)
        | Message.Remove name -> rt.print_string (sprintf "Value %s has been removed.\r\n" name)
    
    let mutable message_hook = default_message_hook

    let lang =
        match System.Globalization.CultureInfo.CurrentCulture.Name with
        | "ja-JP" -> Ja
        | _ -> En

    let pfn fmt = Printf.kprintf (fun s -> rt.print_string (s + "\r\n")) fmt
    
    let stack_push c f =
        stack_topidx <- stack_topidx + 1
        if (stack_topidx + 1) > stack.Length then
            let new_stack = Array.zeroCreate (2 * stack.Length)
            Array.blit stack 0 new_stack 0 stack.Length
            stack <- new_stack
        stack.[stack_topidx].code <- c
        stack.[stack_topidx].frame <- f

    let stack_discard_top() =
        match stack.[stack_topidx].code with
        | UEapply _ ->
            let frame = stack.[stack_topidx].frame :?> ApplyFrame
            if frame.pc = Tag.Apply_Closure then
                env <- frame.oldenv
        | _ -> ()
        stack.[stack_topidx].code <- Unchecked.defaultof<code>
        stack.[stack_topidx].frame <- null
        stack_topidx <- stack_topidx - 1
        
    let cancel() =
        state <- State.Finished
        accu <- Value.unit
        result <- (Value.unit, ty_unit)
        error <-  Unchecked.defaultof<Error>
        wakeup <- DateTime.MinValue
        while stack_topidx > -1 do
            stack_discard_top()
            
    let start_code (c : code) =
        match c with
        | UEconst v ->
            accu <- v
        | UEenv ofs ->
            accu <- env.[ofs]
        | UEenvvar ofs ->
            match env.[ofs] with
            | Vvar r -> accu <- !r
            | _ -> dontcare()
        | UEfn (env_size, argc, capture_ofs_from, capture_ofs_to, body) ->
            let captures = Array.zeroCreate<value> capture_ofs_from.Length
            for k = 0 to capture_ofs_from.Length - 1 do
                captures.[k] <- env.[capture_ofs_from.[k]]
            accu <- Vclosure (captures = captures, offsets = capture_ofs_to, arity = argc, env_size = env_size, code = body )
        | UCfun defs ->
            // Doing this in two steps because closure capture itself from env in recursive function.
            // Step 1: create closures with captures unfilled, and set it to env.
            for ofs, fn in defs do
                match fn with
                | UEfn (env_size, argc, ofss_from, ofss_to, body) ->
                    env.[ofs] <- Vclosure (captures = Array.zeroCreate<value> ofss_from.Length,
                                           offsets = ofss_to,
                                           arity = argc,
                                           env_size = env_size,
                                           code = body)
                | _ -> dontcare()
            // Step 2: fill captures.
            for ofs, fn in defs do
                match fn, env.[ofs] with
                | UEfn (_, _, ofss_from, _, _), Vclosure ( captures = captures ) ->
                    for l = 0 to ofss_from.Length - 1 do
                        captures.[l] <- env.[ofss_from.[l]]
                | _ -> dontcare()
        | UTCtype (dl, _) -> message_hook (Message.TypeDefined dl)
        | UTChide (name, tyenv', alloc') ->
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.Hide name)
        | UTCremove (name, ofs, tyenv', alloc') ->
            env.[ofs] <- Unchecked.defaultof<value>
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.Remove name)
        | UTCexn (name, tyenv', alloc') ->
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.ExceptionDefined name)
        | UTClex defs ->
            // Step 1
            let actionss =
                Array.map (fun (arity, ofs, alphabets, dfa, codes : code array) ->
                    let closures = Array.zeroCreate<value> codes.Length
                    let lexer_obj : HashSet<int> * DfaNode * value array = (alphabets, dfa, closures)
                    let partial = Vpartial (arity, [| Vbuiltin (-1, builtin_id.LEXING); Vobj lexer_obj |])
                    env.[ofs] <- partial
                    (codes, closures)) defs
            // Step 2
            for codes, closures in actionss do
                for i = 0 to codes.Length - 1 do
                    match codes.[i] with
                    | UEfn (env_size, arity, ofss_from, ofss_to, code) ->
                        let captures = Array.map (fun i -> env.[i]) ofss_from
                        closures.[i] <- Vclosure (arity, env_size, ofss_to, captures, code)
                    | _ -> dontcare()
        | UTCupd (tyenv', alloc', shadowed) ->
            tyenv <- tyenv'
            alloc <- alloc'
            match shadowed with
            | Some ofss ->
                for ofs in ofss do
                    env.[ofs] <- Unchecked.defaultof<value>
            | _ -> ()
        | UTCprint_value ty ->
            result <- (this.Accu, ty)
            message_hook (Message.EvaluationComplete (tyenv, ty, this.Accu))
        | UTCprint_new_values new_values ->
            let new_values = List.map (fun (name, info) ->
                let ofs, kind = alloc.Get(name)
                let value =
                    match env.[ofs], kind with
                    | (Vvar v) as r, Mutable -> r
                    | _, Mutable -> dontcare()
                    | x, Immutable -> x
                (name, value, info)) new_values
            message_hook (Message.NewValues (tyenv, new_values))
        | UEblock _ ->
            stack_push c { BlockFrame.pc = Tag.Start; fields = null; i = 0 }
        | UEarray _ ->
            stack_push c { ArrayFrame.pc = Tag.Start; ary = Unchecked.defaultof<value>; i = 0 }
        | UEblockwith _ ->
            stack_push c { BlockwithFrame.pc = Tag.Start; fields = null; i = 0; tag = 0 }
        | UEapply _ ->
            stack_push c { ApplyFrame.pc = Tag.Start; i = 0; values = null; oldenv = null }
        | UEbegin _ ->
            stack_push c { BeginFrame.pc = Tag.Start; i = 0 }
        | UEcase _ ->
            stack_push c { CaseFrame.pc = Tag.Start; testvalue = Unchecked.defaultof<value>; i = 0 }
        | UEtry _
        | UEif _
        | UEsetenvvar _
        | UEwhile _ ->
            stack_push c (ref Tag.Start)
        | UEfor _ ->
            stack_push c { ForloopFrame.pc = Tag.Start; i = 0; j = 0 }
        | UCval _
        | UCvar _ ->
            stack_push c { ValVarFrame.pc = Tag.Start; i = 0 }
        | UEcompare -> dontcare()

    let start_compare mode v0 v1 =
        if mode <= builtin_id.TRY_COMPARE then
            match v0, v1 with
            | Vint (i0, _), Vint (i1, _)
            | Vint (i0, _),  Vblock (i1, _, _)
            | Vblock (i0, _, _), Vint (i1, _) ->
                accu <- of_compare (compare i0 i1)
            | Vfloat (x0, _), Vfloat (x1, _) ->
                match mode with
                | builtin_id.COMPARE ->
                    accu <- of_compare (x0.CompareTo(x1))
                | builtin_id.TRY_COMPARE ->
                    accu <- of_compare (if Double.IsNaN x0 || Double.IsNaN x1 then Int32.MinValue else x0.CompareTo(x1))
                | _ -> dontcare()
            | Vstring (s0, _), Vstring (s1, _) ->
                accu <- of_compare (Math.Sign(String.CompareOrdinal(s0, s1)))
            | _ ->
                stack_push UEcompare { v0 = v0; v1 = v1; mode = mode; pc = Tag.Start; i = 0 }
        else
            stack_push UEcompare { v0 = v0; v1 = v1; mode = mode; pc = Tag.Start; i = 0 }

    let parse (src : string) =
        let lexbuf = LexBuffer<char>.FromString src
        lexbuf.EndPos <- { lexbuf.EndPos with pos_fname = "<console>" }
        lexbuf.BufferLocalStore.["src"] <- src
        try
            let cmds, _ = Parser.Program Lexer.main lexbuf
            Ok cmds
        with
        | LexHelper.Lexical_error lex_err ->
            let st, ed = lexbuf.Range
            let loc = { src = src; st = st; ed = ed }
            Error (LexicalError (lex_err, loc))
        | Failure "parse error" ->
            let st, ed = lexbuf.Range
            let loc = { src = src; st = st; ed = ed }
            Error (SyntaxError loc)

    let start src =
        cancel()
        match parse src with
        | Error err ->
            state <- State.StoppedDueToError
            error <- err
        | Ok cmds ->

            let warning_sink (err : type_error_desc, loc : location) =
                pfn "> %s" (Syntax.describe_location loc)
                pfn "%s" (Printer.print_typechk_error lang cols err)

            match attempt (Typechk.type_command_list warning_sink tyenv) cmds with
            | Error (Type_error (err, loc)) ->
                state <- State.StoppedDueToError
                error <- Error.TypeError (err, loc)
            | Error x -> dontcare()
            | Ok tyenvs ->
                let genv_size, tcmds = Translate.translate_command_list alloc tyenvs (Array.ofList cmds)
                if genv_size > config.maximum_array_length then
                    state <- State.StoppedDueToError
                    error <- EnvSizeLimit
                else
                    env <- array_ensure_capacity_exn config.maximum_array_length genv_size env
                    start_code (UEbegin tcmds)
                    state <- State.Running
        
    let rec do_match (bind : bool) (p : pattern) (x : value) =
        match p, x with
        | UPid ofs, _ ->
            if bind then env.[ofs] <- x
            true
        | UPas (p, ofs), _ ->
            if bind then env.[ofs] <- x
            do_match bind p x
        | UPor (p1, p2), _ -> do_match bind p1 x || do_match bind p2 x
        | UPint i1, Vint (i2, _) -> i1 = i2
        | UPfloat x1, Vfloat (x2, _) -> x1 = x2
        | UPstring s1, Vstring (s2, _) -> s1 = s2
        | UPblock (pattag, patl), Vblock (tag, fields, _) ->
            if pattag = tag && patl.Length = fields.Length then
                let mutable cont = true
                let mutable i = 0
                while cont && i < patl.Length do
                    cont <- do_match bind patl.[i] fields.[i]
                    i <- i + 1
                cont
            else false
        | UParray patl, Varray { count = ary_count } ->
            if patl.Length = ary_count then
                let mutable cont = true
                let mutable i = 0
                while cont && i < patl.Length do
                    cont <- do_match bind patl.[i] (array_get dummy_runtime x i)
                    i <- i + 1
                cont
            else false
        | UPany, _ -> true
        | UPint _, Vblock _
        | UPblock _, Vint _ -> false
        | _ -> dontcare()
    
    let do_raise (exn_value : value) =
        let rec case_loop (i : int) (cases : (pattern * code) array) (j : int) =
            if j < cases.Length then
                let pat, handler = cases.[j]
                if do_match false pat exn_value then
                    Some (i, pat, handler)
                else case_loop i cases (j + 1)
            else None

        let rec frame_loop i =
            if i >= 0 then
                match stack.[i].code with
                | UEtry (_, catchl) ->
                    let frame = stack.[i].frame :?> ref<Tag>
                    if !frame = Tag.Try_EvalTry then
                        case_loop i catchl 0
                    else frame_loop (i - 1)
                | _ -> frame_loop (i - 1)
            else None
        match frame_loop stack_topidx with
        | Some (i, pat, catch) ->
            while stack_topidx > i do
                stack_discard_top()
            let frame = stack.[i].frame :?> ref<Tag>
            frame := Tag.Try_EvalCatch
            do_match true pat exn_value |> ignore
            start_code catch
        | None ->
            error <- Error.UncaughtException exn_value
            state <- State.StoppedDueToError

    let run (slice_ticks : int64) =
        
        if state = State.Sleeping then state <- State.Running
        rt.timestamp_at_start <- Stopwatch.GetTimestamp()
        
        while state = State.Running && (Stopwatch.GetTimestamp() - rt.timestamp_at_start) < slice_ticks do
            let code = stack.[stack_topidx].code
            let frame = stack.[stack_topidx].frame
            match code with
            | UEblock (tag, field_exprs) ->
                let frame = frame :?> BlockFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Block_Eval
                    frame.fields <- Array.zeroCreate<value> field_exprs.Length
                    start_code field_exprs.[0]
                | Tag.Block_Eval ->
                    frame.fields.[frame.i] <- accu
                    frame.i <- frame.i + 1
                    if frame.i < field_exprs.Length then
                        start_code field_exprs.[frame.i]
                    else
                        accu <- block_createrange rt tag frame.fields
                        stack_discard_top()
                | _ -> dontcare()
            | UEarray fields ->
                let frame = frame :?> ArrayFrame
                match frame.pc with
                | Tag.Start ->
                    let cont =
                        try
                            frame.ary <- array_create rt fields.Length
                            true
                        with
                            | MALException v ->
                                do_raise v
                                false
                            | Value.InsufficientMemory as e ->
                                error <- Error.MALInsufficientMemory
                                state <- State.StoppedDueToError
                                false
                    if cont then
                        if fields.Length = 0 then
                            accu <- frame.ary
                            stack_discard_top()
                        else
                            frame.pc <- Tag.Array_Eval
                            start_code fields.[0]
                | Tag.Array_Eval ->
                    array_add rt frame.ary accu
                    frame.i <- frame.i + 1
                    if frame.i < fields.Length then
                        start_code fields.[frame.i]
                    else
                        accu <- frame.ary
                        stack_discard_top()
                | _ -> ()
            | UEblockwith (orig_expr, idxl, exprl) ->
                let frame = frame :?> BlockwithFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.BlockWith_EvalOrig
                    start_code orig_expr
                | Tag.BlockWith_EvalOrig ->
                    frame.pc <- Tag.BlockWith_EvalSets
                    match accu with
                    | Vblock (tag, fields, _) ->
                        frame.tag <- tag
                        frame.fields <- Array.copy fields
                    | _ -> dontcare()
                    start_code exprl.[0]
                | Tag.BlockWith_EvalSets ->
                    frame.fields.[frame.i] <- accu
                    frame.i <- frame.i + 1
                    if frame.i < idxl.Length then
                        start_code exprl.[frame.i]
                    else
                        accu <- block_createrange rt frame.tag frame.fields
                        stack_discard_top()
                | _ -> dontcare()
            | UEcompare ->
                let frame = frame :?> CompareFrame
                if frame.mode <= builtin_id.TRY_COMPARE then
                    match frame.v0, frame.v1 with
                    | Vblock (tag0, fields1, _), Vblock (tag1, fields2, _) ->
                        match frame.pc with
                        | Tag.Start ->
                            let d = compare tag0 tag1
                            if d <> 0 then
                                accu <- of_compare d
                                stack_discard_top()
                            else
                                let d = compare fields1.Length fields2.Length
                                if d <> 0 then  
                                    accu <- of_compare d
                                    stack_discard_top()
                                else
                                    frame.pc <- Tag.Compare_CompareFields
                                    start_compare frame.mode fields1.[0] fields2.[0]
                        | Tag.Compare_CompareFields ->
                            if to_int accu = 0 then
                                frame.i <- frame.i + 1
                                if frame.i < fields1.Length then
                                    start_compare frame.mode fields1.[frame.i] fields2.[frame.i]
                                else stack_discard_top()
                            else stack_discard_top()
                        | _ -> dontcare()
                    | Varray ary0, Varray ary1 ->
                        match frame.pc with
                        | Tag.Start ->
                            let d = compare ary0.count ary1.count
                            if d <> 0 || ary0.count = 0  then  
                                accu <- of_compare d
                                stack_discard_top()
                            else
                                frame.pc <- Tag.Compare_CompareFields
                                start_compare frame.mode (array_get rt frame.v0 0) (array_get rt frame.v1 0)
                        | Tag.Compare_CompareFields ->
                            if to_int accu = 0 then
                                frame.i <- frame.i + 1
                                if frame.i < ary0.count then
                                    start_compare frame.mode (array_get rt frame.v0 frame.i) (array_get rt frame.v1 frame.i)
                                else stack_discard_top()
                            else stack_discard_top()
                        | _ -> dontcare()
                    | (Vbuiltin _ | Vfunc _ | Vclosure _ | Vpartial _), (Vbuiltin _ | Vfunc _ | Vclosure _ | Vpartial _) ->
                        do_raise (mal_failure rt "compare: functional value")
                    | Vformat _, Vformat _ ->
                        do_raise (mal_failure rt "compare: format string")
                    | Vobj _, Vobj _ ->
                        do_raise (mal_failure rt "compare: CLR object")
                    | _ -> dontcare()
                elif frame.mode <= builtin_id.GREATER_EQUAL then
                    match frame.pc with
                    | Tag.Start ->
                        frame.pc <- Tag.ComparisonOperators_CallCompare
                        start_compare builtin_id.TRY_COMPARE frame.v0 frame.v1
                    | Tag.ComparisonOperators_CallCompare ->
                        accu <-
                            match frame.mode with
                            | builtin_id.EQUAL -> of_bool (to_int accu = 0)
                            | builtin_id.NOT_EQUAL -> of_bool (not (to_int accu = 0))
                            | builtin_id.LESS_THAN -> of_bool (match to_int accu with -1 -> true | _ -> false)
                            | builtin_id.GREATER_THAN -> of_bool (match to_int accu with 1 -> true | _ -> false)
                            | builtin_id.LESS_EQUAL -> of_bool (match to_int accu with -1 | 0 -> true | _ -> false)
                            | builtin_id.GREATER_EQUAL -> of_bool (match to_int accu with 0 | 1 -> true | _ -> false)
                            | _ -> dontcare()
                        stack_discard_top()
                    | _ -> dontcare()
                else dontcare()
            | UEapply expl ->
                let frame = frame :?> ApplyFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Apply_Eval
                    frame.values <- Array.zeroCreate<value> expl.Length
                    start_code expl.[0]
                | Tag.Apply_Eval ->
                    frame.values.[frame.i] <- accu
                    frame.i <- frame.i + 1
                    if frame.i < expl.Length then
                        start_code expl.[frame.i]
                    else
                        frame.pc <- Tag.Apply_Apply
                        frame.i <- 0
                | Tag.Apply_Apply ->
                    // At this point, frame.values contains function and arguments.
                    // The number of arguments is >= 1.
                    // The function is at frame.values.[frame.i]. The function can be Vbuiltin, Vfunc, Vclosure or Vpartial.
                    // The first argument is frame.values.[frame.i + 1].
                    // The last argument is frame.values.[frame.values.Length - 1].
                    let arity, is_partial = // Note arity is -1 for varg functions (e.g. kprintf).
                        match frame.values.[frame.i] with
                        | Vclosure (arity = arity)
                        | Vfunc (arity, _)
                        | Vbuiltin (arity, _) -> arity, false
                        | Vpartial (arity, _) -> arity, true
                        | _ -> dontcare()
                    let argc = frame.values.Length - frame.i - 1
                    if argc < arity then
                        accu <- Vpartial (arity - argc, Array.sub frame.values frame.i (frame.values.Length - frame.i))
                        stack_discard_top()
                    else
                        // if function is partial, expand it into frame.values.
                        if is_partial then
                            let rec partial_length_loop (v : value) =
                                match v with
                                | Vpartial (_, values) ->
                                    partial_length_loop values.[0] + values.Length - 1
                                | Vclosure _ | Vfunc _ | Vbuiltin _ -> 1
                                | _ -> dontcare()
                            let partial_length = partial_length_loop frame.values.[frame.i]
                            let ary = Array.zeroCreate<value> (partial_length + frame.values.Length - frame.i - 1)
                            let rec expand_loop (v : value) =
                                match v with
                                | Vpartial (_, values) ->
                                    let ofs = expand_loop values.[0]
                                    let n = values.Length - 1
                                    Array.blit values 1 ary ofs n
                                    ofs + n
                                | Vfunc _ 
                                | Vclosure _
                                | Vbuiltin _ ->
                                    ary.[0] <- v
                                    1
                                | _ -> dontcare()
                            let ofs = expand_loop frame.values.[frame.i]
                            Array.blit frame.values (frame.i + 1) ary ofs (frame.values.Length - frame.i - 1)
                            frame.values <- ary
                            frame.i <- 0
                        // call actual function
                        match frame.values.[frame.i] with
                        | Vbuiltin (_, id) when id <= builtin_id.GREATER_EQUAL ->
                            frame.pc <- Tag.Apply_Return
                            start_compare id frame.values.[frame.i + 1] frame.values.[frame.i + 2]
                        | Vbuiltin (_, builtin_id.KPRINTF) ->
                            let k = frame.values.[frame.i + 1]
                            if frame.i + 2 = frame.values.Length then
                                // Only k is applied to kprintf.
                                accu <- Vpartial (-1, Array.sub frame.values frame.i (frame.values.Length - frame.i))
                                stack_discard_top()
                            else
                                let cmds = match frame.values.[frame.i + 2] with Vformat cmds -> cmds | _ -> dontcare()
                                let cmds_arity = MalPrintf.arity_of_cmds cmds
                                let arity_remain = 3 + cmds_arity - (frame.values.Length - frame.i)
                                if arity_remain > 0 then
                                    // Number of arguments is not enough to execute kprintf.
                                    accu <- Vpartial (arity_remain, Array.sub frame.values frame.i (frame.values.Length - frame.i))
                                    stack_discard_top()
                                else
                                    let s = MalPrintf.exec_cmds cmds (Array.sub frame.values (frame.i + 3) cmds_arity)
                                    let j = frame.i + 3 + cmds_arity - 2
                                    for k = frame.i to j - 1 do
                                        frame.values.[k] <- Unchecked.defaultof<value>
                                    frame.i <- j
                                    frame.values.[j] <- k
                                    frame.values.[j + 1] <- of_string rt s
                        | Vbuiltin (_, builtin_id.LEXING) ->
                            let block_get b i =
                                match b with
                                | Vblock (_, ary, _) -> ary.[i]
                                | _ -> dontcare()
                            let block_set b i x =
                                match b with
                                | Vblock (_, ary, _) -> ary.[i] <- x
                                | _ -> dontcare()
                            let alphabets, dfa, closures = match frame.values.[frame.i + 1] with Vobj o -> o :?>  HashSet<int> * DfaNode * value array | _ -> dontcare()
                            let lexbuf = frame.values.[frame.values.Length - 1]
                            let (source, start_pos, end_pos, scan_start_pos, eof) =
                                match lexbuf with
                                | Vblock (_, [| Vstring (source, _); Vint (start_pos, _); Vint (end_pos, _); Vint (scan_start_pos, _); Vint (eof, _) |], _) ->
                                    (source, start_pos, end_pos, scan_start_pos, eof <> 0)
                                | _ -> dontcare()
                            if (scan_start_pos = source.Length && eof) || (scan_start_pos > source.Length) then
                                do_raise mal_MatchFailure
                            else
                                match MalLex.Exec alphabets dfa source scan_start_pos with
                                | Some (end_pos, action_idx, eof) ->
                                    block_set lexbuf 1 (of_int dummy_runtime scan_start_pos)
                                    block_set lexbuf 2 (of_int dummy_runtime end_pos)
                                    block_set lexbuf 3 (of_int dummy_runtime end_pos)
                                    block_set lexbuf 4 (of_bool eof)
                                    frame.values.[frame.i + 1] <- closures.[action_idx]
                                    frame.i <- frame.i + 1
                                | None ->
                                    do_raise mal_MatchFailure
                        | Vbuiltin (_, builtin_id.SLEEP) ->
                            state <- State.Sleeping
                            wakeup <- DateTime.UtcNow.AddSeconds(to_float(frame.values.[frame.i + 1]))
                            accu <- unit
                            stack_discard_top()
                        | Vfunc (arity, f) ->
                            let argv = Array.sub frame.values (frame.i + 1) arity
                            try
                                let result = f rt argv
                                if frame.i + 1 + arity = frame.values.Length then
                                    accu <- result
                                    stack_discard_top()
                                else
                                    let j = frame.i + arity
                                    for k = frame.i to j - 1 do
                                        frame.values.[k] <- Unchecked.defaultof<value>
                                    frame.i <- j
                                    frame.values.[j] <- result
                            with e ->
                                match e with
                                | MALException v -> do_raise v
                                | Value.InsufficientMemory ->
                                    error <- Error.MALInsufficientMemory
                                    state <- State.StoppedDueToError
                                | _ -> raise e
                        | Vclosure (arity = arity; env_size = env_size; captures = captures; offsets = offsets; code = code) ->
                            // Start evaluation of the closure
                            frame.oldenv <- env
                            env <- Array.zeroCreate<value> env_size
                            for j = 0 to offsets.Length - 1 do
                                env.[offsets.[j]] <- captures.[j]
                            for j = 0 to arity - 1 do
                                env.[j] <- frame.values.[frame.i + 1 + j]
                            let n = frame.i + 1 + arity
                            for m = frame.i to n - 1 do
                                frame.values.[m] <- Unchecked.defaultof<value>
                            frame.pc <- Tag.Apply_Closure
                            frame.i <- n
                            start_code code
                        | _ -> dontcare()
                | Tag.Apply_Closure ->
                    if frame.i = frame.values.Length then
                        stack_discard_top()
                    else
                        env <- frame.oldenv
                        frame.i <- frame.i - 1
                        frame.values.[frame.i] <- accu
                        frame.pc <- Tag.Apply_Apply
                | Tag.Apply_Return ->
                    // applying compare/try_compare/sleep
                    stack_discard_top()
                | _ -> dontcare()
            | UEbegin cmdl ->
                let frame = frame :?> BeginFrame
                match frame.pc with
                | Tag.Start ->
                    if cmdl.Length = 0 then
                        accu <- unit
                        stack_discard_top()
                    else
                        frame.pc <- Tag.Begin_Eval
                        start_code cmdl.[0]
                | Tag.Begin_Eval ->
                    frame.i <- frame.i + 1
                    if frame.i < cmdl.Length then
                        start_code cmdl.[frame.i]
                    else stack_discard_top()
                | _ -> dontcare()
            | UEcase (test, cases) ->
                let frame = frame :?> CaseFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Case_EvalTest
                    start_code test
                | Tag.Case_EvalTest ->
                    frame.testvalue <- accu
                    frame.pc <- Tag.Case_Match
                | Tag.Case_Match ->
                    let pat, when_clause, result = cases.[frame.i]
                    if do_match true pat frame.testvalue then
                        match when_clause with
                        | Some code ->
                            frame.pc <- Tag.Case_EvalWhen
                            start_code code // ew
                        | None ->
                            frame.pc <- Tag.Case_EvalResult
                            start_code result
                    else
                        frame.i <- frame.i + 1
                        if frame.i = cases.Length then
                            do_raise mal_MatchFailure
                | Tag.Case_EvalWhen ->
                    let _, _, result = cases.[frame.i]
                    if to_bool accu then
                        frame.pc <- Tag.Case_EvalResult
                        start_code result
                    else
                        frame.i <- frame.i + 1
                        if frame.i < cases.Length then
                            frame.pc <- Tag.Case_Match
                        else
                            do_raise mal_MatchFailure
                | Tag.Case_EvalResult ->
                    stack_discard_top()
                | _ -> dontcare()
            | UEtry (expr_try, _) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.Try_EvalTry
                    start_code expr_try
                | Tag.Try_EvalTry
                | Tag.Try_EvalCatch ->
                    stack_discard_top()
                | _ -> ()
            | UEif (code_test, code_true, code_false) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.If_EvalTest
                    start_code code_test
                |  Tag.If_EvalTest ->
                    frame := Tag.If_EvalResult
                    if to_bool accu
                    then start_code code_true
                    else start_code code_false
                | Tag.If_EvalResult ->
                    stack_discard_top()
                | _ -> dontcare()
            | UEsetenvvar (ofs, code) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.Setenvref_Eval
                    start_code code
                | Tag.Setenvref_Eval ->
                    match env.[ofs] with
                    | Vvar r -> r := accu
                    | _ -> dontcare()
                    stack_discard_top()
                | _ -> dontcare()
            | UEfor (ofs, first, dir, last, body) ->
                let frame = frame :?> ForloopFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Forloop_EvalFirst
                    start_code first
                | Tag.Forloop_EvalFirst ->
                    frame.i <- to_int accu
                    frame.pc <- Tag.Forloop_EvalLast
                    start_code last
                | Tag.Forloop_EvalLast ->
                    frame.j <- to_int accu
                    if dir = dirflag.Upto && frame.i <= frame.j then
                        frame.pc <- Tag.Forloop_To
                        env.[ofs] <- of_int rt frame.i
                        start_code body
                    elif dir = dirflag.Downto && frame.i >= frame.j then
                        frame.pc <- Tag.Forloop_Downto
                        env.[ofs] <- of_int rt frame.i
                        start_code body
                    else stack_discard_top()
                | Tag.Forloop_To ->
                    if frame.i < frame.j then
                        frame.i <- frame.i + 1
                        env.[ofs] <- of_int rt frame.i
                        start_code body
                    else
                        accu <- unit
                        stack_discard_top()
                | Tag.Forloop_Downto ->
                    if frame.i > frame.j then
                        frame.i <- frame.i - 1
                        env.[ofs] <- of_int rt frame.i
                        start_code body
                    else
                        accu <- unit
                        stack_discard_top()
                | _ -> dontcare()
            | UEwhile (cond, body) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.While_EvalCond
                    start_code cond
                | Tag.While_EvalCond ->
                    if to_bool accu then
                        frame := Tag.While_EvalBody
                        start_code body
                    else
                        accu <- unit
                        stack_discard_top()
                | Tag.While_EvalBody ->
                    frame := Tag.While_EvalCond
                    start_code cond
                | _ -> ()
            | UCval l ->
                let frame = frame :?> ValVarFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Val_Eval
                    let _, code = l.[0]
                    start_code code
                | Tag.Val_Eval ->
                    let pat, _ = l.[frame.i]
                    if do_match true pat accu then
                        frame.i <- frame.i + 1
                        if frame.i < l.Length then
                            let _, code = l.[frame.i]
                            start_code code
                        else
                            stack_discard_top()
                    else
                        do_raise mal_MatchFailure
                | _ -> dontcare()
            | UCvar defs ->
                let frame = frame :?> ValVarFrame
                match frame.pc with
                | Tag.Start ->
                    frame.pc <- Tag.Var_Eval
                    start_code (snd defs.[0])
                | Tag.Var_Eval ->
                    env.[fst defs.[frame.i]] <- Vvar (ref accu)
                    frame.i <- frame.i + 1
                    if frame.i < defs.Length then
                        start_code (snd defs.[frame.i])
                    else stack_discard_top()
                | _ -> dontcare()
            | _ -> dontcare()

            if state = State.Running then
                if stack_topidx + 1 = 0 then
                    state <- State.Finished
                elif stack_topidx + 1 >= config.maximum_stack_depth then
                    state <- State.StoppedDueToError
                    error <- Error.MALStackOverflow
                elif not (check_free_memory rt 0) then
                    state <- State.StoppedDueToError
                    error <- Error.MALInsufficientMemory

            rt.cycles <- rt.cycles + 1L

    let alias_exn new_name orig_name =
        let vi = Option.get (Types.try_get_value tyenv orig_name)
        tyenv <- Types.add_value tyenv new_name vi
        let orig_ofs, _ = alloc.Get(orig_name)
        let new_ofs = alloc.Add(new_name, Immutable)
        env <- array_ensure_capacity_exn config.maximum_array_length (new_ofs + 1) env
        env.[new_ofs] <- env.[orig_ofs]
    
    let obj_of_value_cache = Dictionary<Type, HashSet<value> -> value -> obj>()
    let value_of_obj_cache = Dictionary<Type, runtime -> obj -> value>()

    let set (name : string) (value : value) (ty : type_expr) =
        tyenv <- Types.add_value tyenv name { vi_access = access.Immutable; vi_type = ty }
        let ofs = alloc.Add(name, Immutable)
        env <- array_ensure_capacity_exn config.maximum_array_length (ofs + 1) env
        env.[ofs] <- value

    do
        start Prelude.prelude
        run Int64.MaxValue
        if state <> State.Finished then dontcare()
        alias_exn "@" "list_append"
        alias_exn "!" "ref_get"
        alias_exn ":=" "ref_set"

    new() = Interpreter(config.Default)

    member this.State with get() = state
    member this.Run(ticks : int64) = run ticks
    member this.Accu = accu
    member this.Error = error
    member this.Wakeup = wakeup
    member this.Cols with get() = cols and set n = cols <- n
    member this.TypeEnv = tyenv
    member this.Result = result
    member this.PrintString with get() = rt.print_string and set ps = rt.print_string <- ps
    member this.Runtime = rt
    member this.Cancel() = cancel()
    member this.StringOfError(lang, cols, err) = string_of_error lang cols err

    /// Returns true when interpreter state is Running or Sleeping.
    member this.IsRunning
        with get() =
            match state with
            | State.Running 
            | State.Sleeping -> true 
            | _ -> false
    
    /// Internally calls Cancel()    
    member this.Start(s) = start s

    /// Internally calls Cancel()    
    member this.StartApply(values : value array) =
        cancel()
        let code = UEapply (Array.map (fun v -> UEconst v) values)
        start_code code
        state <- State.Running

    /// Internally calls Cancel()    
    member this.Do(s) =
        start s
        run Int64.MaxValue

    /// Internally calls Cancel()        
    member this.Set(name : string, value : value, ty : type_expr) =
        cancel()
        set name value ty

    /// Internally calls Cancel()    
    member this.Val<'T>(name : string, x : 'T) =
        cancel()
        let v = Value.value_of_obj value_of_obj_cache tyenv typeof<'T> Value.dummy_runtime x
        let ty = Types.typeexpr_of_type tyenv (Dictionary()) typeof<'T>
        set name v ty
    
    /// Internally calls Cancel()    
    member this.Fun<'T, 'U>(name : string, f : runtime -> 'T -> 'U) =
        cancel()
        let v = Value.wrap_fsharp_func tyenv obj_of_value_cache value_of_obj_cache typeof<runtime -> 'T -> 'U> f
        let ty = Types.typeexpr_of_type tyenv (Dictionary()) typeof<'T -> 'U>
        set name v ty

    /// Internally calls Cancel()    
    member this.RegisterAbstractType(name : string, ty : Type) =
        cancel()
        let tyenv', id = Types.register_abstract_type tyenv name ty
        tyenv <- tyenv'
        id

    /// Internally calls Cancel()
    member this.RegisterFsharpTypes(types : (string * Type) array) =
        cancel()
        let tyenv', id = Types.register_fsharp_types tyenv types
        tyenv <- tyenv'
        id