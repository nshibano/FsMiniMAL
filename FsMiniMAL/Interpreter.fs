namespace FsMiniMAL

open System
open System.Collections.Generic
open System.Text
open Printf

open FsMiniMAL.Lexing
open Syntax
open Types
open Typechk
open Value
open Stdlib
open Translate

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

exception MALStackOverflow

type Error =
    //| LexicalError of LexHelper.lexical_error_desc * location
    | SyntaxError
    | TypeError of tyenv * Typechk.type_error_desc * location
    | UncaughtException of value
    | UncatchableException of exn
    | Other

type Interpreter(config : config) as this =

    let mutable state = State.Finished
    
    let rt =
        { memory_counter = ref 0
          stopwatch = 0L
          print_string = ignore
          config = config }
        
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
            // Doing this in two steps because closure capture itself from env for recursive function.
            // Step 1: create closures with dummy captures, and set it to env.
            for ofs, fn in defs do
                match fn with
                | UEfn (env_size, argc, ofss_from, ofss_to, body) ->
                    env.[ofs] <- Vclosure (captures = Array.zeroCreate<value> ofss_from.Length, // dummy
                                           offsets = ofss_to,
                                           arity = argc,
                                           env_size = env_size,
                                           code = body)
                | _ -> dontcare()
            // Step 2: fill captures.
            for k = 0 to defs.Length - 1 do
                let ofs, fn = defs.[k]
                let cl = env.[ofs]
                match fn, cl with
                | UEfn (_, _, ofss_from, _, _), Vclosure ( captures = captures ) ->
                    for l = 0 to ofss_from.Length - 1 do
                        captures.[l] <- env.[ofss_from.[l]]
                | _ -> dontcare()
        | UTCtype (dl, _) -> List.iter (fun d -> pfn "type %s defined." d.sd_name) dl
        | UTChide (name, _) -> pfn "type %s is now abstract." name
        | UTChideval name -> pfn "Value %s is now hidden." name
        | UTCexn (name, _) -> pfn "exception %s defined." name
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
            pfn "%s" (Printer.print_value tyenv cols ty this.Accu)
        | UTCprint_new_values new_values ->
            let new_values = List.map (fun (name, info) ->
                let ofs, kind = alloc.Get(name)
                let value =
                    match env.[ofs], kind with
                    | (Vvar v) as r, Mutable -> r
                    | _, Mutable -> dontcare()
                    | x, Immutable -> x
                (name, value, info)) new_values
            for name, value, info in new_values do
                pfn "%s" (Printer.print_definition tyenv cols name info value)
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
                rt.stopwatch <- rt.stopwatch + int64 s0.Length + int64 s1.Length
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
            cmds
        with
        | LexHelper.Lexical_error lex_err ->
            let st, ed = lexbuf.Range
            let loc = { src = src; st = st; ed = ed }
            failwithf "> %s\r\n  Lexical error (%A)." (Syntax.describe_location loc) lex_err
        | Failure "parse error" ->
            let st, ed = lexbuf.Range
            let loc = { src = src; st = st; ed = ed }
            failwithf "> %s\r\n  Syntax error." (Syntax.describe_location loc)

    let start src =
        cancel()
        match attempt parse src with
        | Error (Failure msg) ->
            rt.print_string (msg + "\r\n")
            state <- State.StoppedDueToError
            error <- Error.SyntaxError
        | Error _ -> dontcare()
        | Ok cmds ->
            match attempt (Typechk.type_command_list rt.print_string tyenv) cmds with
            | Error (Type_error (err, loc)) ->
                pfn "> %s" (Syntax.describe_location loc)
                pfn "%s." (Printer.print_typechk_error lang cols err)
                state <- State.StoppedDueToError
                error <- TypeError (tyenv, err, loc)
            | Error (InvalidTypeHideRequest msg) ->
                pfn "> Invalid type hide request. (%s.)" msg
                state <- State.StoppedDueToError
                error <- Error.Other
            | Error x -> dontcare()
            | Ok (tyenvs, ccmds) ->
                let genv_size, tcmds = Translate.translate_command_list alloc tyenvs ccmds
                if genv_size > config.maximum_array_length then
                    pfn "> Size of the global env hits the limit."
                    state <- State.StoppedDueToError
                    error <- Other
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

    let run (slice_ticks : int64) =
        
        if state = State.Sleeping then state <- State.Running
        rt.stopwatch <- 0L

        while state = State.Running && rt.stopwatch < slice_ticks do
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
                                error <- Error.UncatchableException e
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
                                    error <- Error.UncatchableException e
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

            rt.stopwatch <- rt.stopwatch + 1L

            if state = State.Running then
                if stack_topidx + 1 = 0 then
                    state <- State.Finished
                elif stack_topidx + 1 >= config.maximum_stack_depth then
                    state <- State.StoppedDueToError
                    error <- Error.UncatchableException MALStackOverflow
                elif not (check_free_memory rt 0) then
                    state <- State.StoppedDueToError
                    error <- Error.UncatchableException InsufficientMemory

        if state = State.StoppedDueToError then
            match error with
            | Error.UncaughtException exn_value ->
                let sb = new StringBuilder()
                sb.Add("UncaughtException: ")
                sb.Add(Printer.print_value_without_type tyenv cols ty_exn exn_value)
                sb.AppendLine() |> ignore
                stacktrace 10 sb
                rt.print_string (sb.ToString())
            | Error.UncatchableException exn ->
                let sb = new StringBuilder()
                sb.Add("UncatchableException: ")
                sb.Add(exn.GetType().Name)
                sb.AppendLine() |> ignore
                stacktrace 10 sb
                rt.print_string (sb.ToString())
            | _ -> ()

    let alias_exn new_name orig_name =
        let vi = tyenv.values.[orig_name]
        tyenv <- Types.add_value tyenv new_name vi
        let orig_ofs, _ = alloc.Get(orig_name)
        let new_ofs = alloc.Add(new_name, Immutable)
        env <- array_ensure_capacity_exn config.maximum_array_length (new_ofs + 1) env
        env.[new_ofs] <- env.[orig_ofs]

    do
        start Prelude.prelude
        run Int64.MaxValue
        if state <> State.Finished then dontcare()
        alias_exn "@" "list_append"
        alias_exn "!" "ref_get"
        alias_exn ":=" "ref_set"

    new() = Interpreter(config.Default)

    member this.State with get() = state
    member this.Run(slice) = run slice
    member this.Accu = accu
    member this.Error = error
    member this.Wakeup = wakeup
    member this.Cols with get() = cols and set n = cols <- n
    member this.TypeEnv = tyenv
    member this.Result = result
    member this.PrintString with get() = rt.print_string and set ps = rt.print_string <- ps
    member this.Runtime = rt
    member this.Cancel() = cancel()

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
    member this.Do(s) =
        start s
        run Int64.MaxValue
