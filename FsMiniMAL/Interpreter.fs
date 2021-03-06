﻿namespace FsMiniMAL

open System
open System.Collections.Generic
open System.Text
open System.Diagnostics

open FsMiniMAL.Lexing
open Syntax
open Types
open Typechk
open Value
open Message

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

    | Tailcall_Eval = 1
    
    | Begin_Eval = 1
    
    | Case_EvalTest = 1
    | Case_Match = 2
    | Case_EvalWhen = 3
    | Case_EvalResult = 4
    
    | Try_EvalTry = 1
    | Try_EvalCatch = 2
    
    | If_EvalTest = 1
    | If_EvalResult = 2
    
    | Setenvvar_Eval = 1
    
    | Setcapturevar_Eval = 1

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

    | TopExpr_Eval = 1

    | TopValVarFun_Eval = 1

type StackItem =
    struct
        val mutable code : code
        val mutable frame : obj
    end

type BlockFrame = { mutable pc : Tag; mutable fields : value array; mutable i : int }
type ArrayFrame = { mutable pc : Tag; mutable ary : value; mutable i : int }
type BlockwithFrame = { mutable pc : Tag; mutable fields : value array; mutable i : int; mutable tag : int }
type CompareFrame = { mode : builtin_id; v0 : value; v1 : value; mutable pc : Tag; mutable i : int }
type ApplyFrame = { mutable pc : Tag; mutable i : int; mutable values : value array; mutable oldenv : value array; mutable oldcaptures : value array; mutable calling_code : code }
type TailcallFrame = { mutable pc : Tag; mutable args : value array; mutable i : int }
type BeginFrame = { mutable pc : Tag; mutable i : int }
type CaseFrame = { mutable pc : Tag; mutable testvalue : value; mutable i : int }
type ForloopFrame = { mutable pc : Tag; mutable i : int; mutable j : int }
type ValVarFrame = { mutable pc : Tag; mutable i : int }

type State =
    | Running = 0
    | Success = 1
    | Failure = 2

type Interpreter(config : config, tyenv : tyenv, alloc : alloc, env : value array) =

    let mutable state = State.Success
    let mutable accu : value = unit
    let mutable env : value array = env
    let mutable captures : value array = null
    let mutable stack = Array.zeroCreate<StackItem> 16
    let mutable stack_topidx = -1
    let mutable tyenv = tyenv
    let mutable alloc = alloc
    let mutable isSleeping = false
    let mutable wakeup  = DateTime.MinValue
    let mutable latestMessage : Message option = None
    let mutable cycles = 0L
    let mutable message_hook : Message -> unit = ignore

    let rt =
        { memory_counter = ref 0
          print_string = ignore
          config = config }
            
    let stack_push (code : code) (frame : obj) =
        stack_topidx <- stack_topidx + 1
        if (stack_topidx + 1) > stack.Length then
            let new_stack = Array.zeroCreate (2 * stack.Length)
            Array.blit stack 0 new_stack 0 stack.Length
            stack <- new_stack
        stack.[stack_topidx].code <- code
        stack.[stack_topidx].frame <- frame

    let stack_discard_top() =
        match stack.[stack_topidx].code with
        | UEapply _ ->
            let frame = stack.[stack_topidx].frame :?> ApplyFrame
            if frame.pc = Tag.Apply_Closure then
                env <- frame.oldenv
                captures <- frame.oldcaptures
        | _ -> ()
        stack.[stack_topidx].code <- Unchecked.defaultof<code>
        stack.[stack_topidx].frame <- null
        stack_topidx <- stack_topidx - 1
        
    let cancel() =
        state <- State.Success
        isSleeping <- false
        accu <- Value.unit
        latestMessage <- None
        wakeup <- DateTime.MinValue
        while stack_topidx > -1 do
            stack_discard_top()

    let send_message (msg : Message) =
        latestMessage <- Some msg
        message_hook msg

    let print_new_values new_values = 
        let new_values = List.map (fun (name, info) ->
            let var_info = alloc.Get(name)
            let value =
                match env.[var_info.ofs], var_info.access with
                | (Vvar v) as r, Mutable -> r
                | _, Mutable -> dontcare()
                | x, Immutable -> x
            (name, value, info)) new_values
        send_message (Message.NewValues (tyenv, new_values))
    
    let start_code (c : code) =
        match c with
        | UEconst v ->
            accu <- v
        | UEgetenv ofs ->
            accu <- env.[ofs]
        | UEgetenvvar ofs ->
            match env.[ofs] with
            | Vvar r -> accu <- !r
            | _ -> dontcare()
        | UEgetcap ofs ->
            accu <- captures.[ofs]
        | UEgetcapvar ofs ->
            match captures.[ofs] with
            | Vvar r -> accu <- !r
            | _ -> dontcare()
        | UEfn (env_size, argc, is_capture_flags, ofss, body) ->
            let capture_values = Array.zeroCreate<value> is_capture_flags.Length
            for i = 0 to is_capture_flags.Length - 1 do
                let ofs = ofss.[i]
                capture_values.[i] <- if is_capture_flags.[i] then captures.[ofs] else env.[ofs] 
            accu <- Vclosure (captures = capture_values, arity = argc, env_size = env_size, code = body)
        | UCfun defs ->
            // Doing this in two steps because recursive function captures itself from env.
            // Step 1: create closures with captures unfilled, and set it to env.
            for ofs, fn in defs do
                match fn with
                | UEfn (env_size, argc, is_capture_flags, _, body) ->
                    env.[ofs] <- Vclosure (captures = Array.zeroCreate<value> is_capture_flags.Length,
                                           arity = argc,
                                           env_size = env_size,
                                           code = body)
                | _ -> dontcare()
            // Step 2: fill captures.
            for ofs, fn in defs do
                match fn, env.[ofs] with
                | UEfn (is_capture_flags = is_capture_flags; ofss = ofss), Vclosure (captures = capture_values) ->
                    for i = 0 to is_capture_flags.Length - 1 do
                        let ofs = ofss.[i]
                        capture_values.[i] <- if is_capture_flags.[i] then captures.[ofs] else env.[ofs]
                | _ -> dontcare()
        | UTCtype (dl, tyenv') -> 
            tyenv <- tyenv'
            message_hook (Message.TypeDefined dl)
        | UTChide (name, tyenv', alloc') ->
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.TypeHidden name)
        | UTCremove (name, ofs, tyenv', alloc') ->
            env.[ofs] <- Value.zero
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.ValueRemoved name)
        | UTCexn (name, tyenv', alloc') ->
            tyenv <- tyenv'
            alloc <- alloc'
            message_hook (Message.ExceptionDefined name)
        | UTClex (defs, tyenv', alloc', shadowed, new_values) ->
            // Step 1
            let actionss =
                Array.map (fun (arity, ofs, alphabets, dfa, codes : code array) ->
                    let closures = Array.zeroCreate<value> codes.Length
                    let lexer_obj : HashSet<int> * DfaNode * value array = (alphabets, dfa, closures)
                    let partial = Vpartial (arity, [| Vbuiltin (2, builtin_id.LEXING); Vobj lexer_obj |])
                    env.[ofs] <- partial
                    (codes, closures)) defs
            // Step 2
            for codes, closures in actionss do
                for i = 0 to codes.Length - 1 do
                    match codes.[i] with
                    | UEfn (env_size, arity, is_capture_flags, ofss, code) ->
                        let capture_values = Array.zeroCreate<value> is_capture_flags.Length
                        for j = 0 to is_capture_flags.Length - 1 do
                            let ofs = ofss.[j]
                            capture_values.[j] <- if is_capture_flags.[j] then captures.[ofs] else env.[ofs]
                        closures.[i] <- Vclosure (arity, env_size, capture_values, code)
                    | _ -> dontcare()
            tyenv <- tyenv'
            alloc <- alloc'
            for ofs in shadowed do
                env.[ofs] <- Value.zero
            print_new_values new_values
        | UTCupd (tyenv', alloc') ->
            tyenv <- tyenv'
            alloc <- alloc'
        | UEblock _ ->
            stack_push c { BlockFrame.pc = Tag.Start; fields = null; i = 0 }
        | UEarray _ ->
            stack_push c { ArrayFrame.pc = Tag.Start; ary = Unchecked.defaultof<value>; i = 0 }
        | UEblockwith _ ->
            stack_push c { BlockwithFrame.pc = Tag.Start; fields = null; i = 0; tag = 0 }
        | UEapply _ ->
            stack_push c { ApplyFrame.pc = Tag.Start; i = 0; values = null; oldenv = null; oldcaptures = null; calling_code = Unchecked.defaultof<code> }
        | UEtailcall _ ->
            stack_push c { TailcallFrame.pc = Tag.Start; args = null; i = 0 }
        | UEbegin _ ->
            stack_push c { BeginFrame.pc = Tag.Start; i = 0 }
        | UEcase _ ->
            stack_push c { CaseFrame.pc = Tag.Start; testvalue = Unchecked.defaultof<value>; i = 0 }
        | UEfor _ ->
            stack_push c { ForloopFrame.pc = Tag.Start; i = 0; j = 0 }
        | UCval _
        | UCvar _ ->
            stack_push c { ValVarFrame.pc = Tag.Start; i = 0 }
        | UEtry _
        | UEif _
        | UEsetenvvar _
        | UEsetcapvar _
        | UEwhile _
        | UTCexpr _
        | UTCvalvarfun _ ->
            stack_push c (ref Tag.Start)
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
        lexbuf.EndPos <- { lexbuf.EndPos with pos_fname = dummy_file_name }
        lexbuf.BufferLocalStore.["src"] <- src
        try
            let cmds, _ = Parser.Program Lexer.main lexbuf
            Ok cmds
        with
        | LexHelper.Lexical_error lex_err ->
            let loc = { src = src; st = lexbuf.StartPos; ed = lexbuf.EndPos }
            Error (LexicalError (lex_err, loc))
        | Failure "parse error" ->
            let loc = { src = src; st = lexbuf.StartPos; ed = lexbuf.EndPos }
            Error (SyntaxError loc)

    let start src =
        cancel()
        match parse src with
        | Error msg ->
            state <- State.Failure
            send_message msg
        | Ok cmds ->
            let warning_sink (err : type_error_desc, loc : location) =
                send_message (Message.TypeError (err, loc))
                
            let tyenvs =
                try Some (Typechk.type_command_list warning_sink tyenv cmds)
                with Type_error (err, loc) ->
                    state <- State.Failure
                    send_message (Message.TypeError (err, loc))
                    None
            match tyenvs with
            | None -> ()
            | Some tyenvs ->
                let genv_size, tcmds = Translate.translate_top_command_list alloc tyenvs (Array.ofList cmds)
                if genv_size > config.maximum_array_length then
                    state <- State.Failure
                    send_message EnvSizeLimit
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
            state <- State.Failure
            send_message (UncaughtException (tyenv, exn_value))

    let run (slice_ticks : int64) =
        
        isSleeping <- false
        let timestamp_at_start = Stopwatch.GetTimestamp()
        
        while state = State.Running && (not isSleeping) && (Stopwatch.GetTimestamp() - timestamp_at_start) < slice_ticks do
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
                        accu <- block_create rt tag frame.fields
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
                                state <- State.Failure
                                send_message Message.MALInsufficientMemory
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
                | _ -> dontcare()
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
                        accu <- block_create rt frame.tag frame.fields
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
                  if false then
                    let arity = expl.Length - 1
                    let rec find_upper_apply_loop i =
                        match stack.[i].code with
                        | UEapply _ ->
                            let frame = stack.[i].frame :?> ApplyFrame
                            if frame.pc = Tag.Apply_Closure
                            then i
                            else find_upper_apply_loop (i - 1)
                        | _ -> find_upper_apply_loop (i - 1)
                    let upper_apply_idx = find_upper_apply_loop stack_topidx
                    while stack_topidx <> upper_apply_idx do
                        stack_discard_top()
                    for j = 0 to arity - 1 do
                        env.[j] <- frame.values.[j + 1]
                    start_code (stack.[stack_topidx].frame :?> ApplyFrame).calling_code
                  else
                    // At this point, frame.values contains function and arguments.
                    // The number of arguments is >= 1.
                    // The function is at frame.values.[frame.i]. The function can be Vbuiltin, Vfunc, Vclosure or Vpartial.
                    // The first argument is frame.values.[frame.i + 1].
                    // The last argument is frame.values.[frame.values.Length - 1].
                    let arity =
                        match frame.values.[frame.i] with
                        | Vclosure (arity = arity)
                        | Vfunc (arity, _)
                        | Vbuiltin (arity, _)
                        | Vpartial (arity, _) -> arity
                        | _ -> dontcare()
                    let argc = frame.values.Length - frame.i - 1
                    if argc < arity then
                        accu <- Vpartial (arity - argc, Array.sub frame.values frame.i (frame.values.Length - frame.i))
                        stack_discard_top()
                    else
                        // if function is partial, expand it into frame.values.
                        match frame.values.[frame.i] with
                        | Vpartial _ ->
                            let rec partial_length_loop (v : value) =
                                match v with
                                | Vpartial (_, values) ->
                                    partial_length_loop values.[0] + values.Length - 1
                                | Vclosure _ | Vfunc _ | Vbuiltin _ -> 1
                                | _ -> dontcare()
                            let partial_length = partial_length_loop frame.values.[frame.i]
                            let ary = Array.zeroCreate<value> (partial_length + frame.values.Length - frame.i - 1)
                            let rec expand_loop ary (v : value) =
                                match v with
                                | Vpartial (_, values) ->
                                    let ofs = expand_loop ary values.[0]
                                    let n = values.Length - 1
                                    Array.blit values 1 ary ofs n
                                    ofs + n
                                | Vfunc _ 
                                | Vclosure _
                                | Vbuiltin _ ->
                                    ary.[0] <- v
                                    1
                                | _ -> dontcare()
                            let ofs = expand_loop ary frame.values.[frame.i]
                            Array.blit frame.values (frame.i + 1) ary ofs (frame.values.Length - frame.i - 1)
                            frame.values <- ary
                            frame.i <- 0
                        | _ -> ()
                        // call actual function
                        match frame.values.[frame.i] with
                        | Vbuiltin (_, id) ->
                            if id <= builtin_id.GREATER_EQUAL then
                                frame.pc <- Tag.Apply_Return
                                start_compare id frame.values.[frame.i + 1] frame.values.[frame.i + 2]
                            else
                                match id with
                                | builtin_id.KPRINTF ->
                                    let k = frame.values.[frame.i + 1]
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
                                | builtin_id.LEXING ->
                                    let alphabets, dfa, closures = match frame.values.[frame.i + 1] with Vobj o -> o :?>  HashSet<int> * DfaNode * value array | _ -> dontcare()
                                    let lexbuf = frame.values.[frame.values.Length - 1]
                                    let lexbuf_fields = get_fields lexbuf
                                    let source = to_string lexbuf_fields.[0]
                                    let scan_start_pos = to_int lexbuf_fields.[3]
                                    let eof = to_bool lexbuf_fields.[4]
                                    if (scan_start_pos = source.Length && eof) || (scan_start_pos > source.Length) then
                                        do_raise mal_MatchFailure
                                    else
                                        match MalLex.Exec alphabets dfa source scan_start_pos with
                                        | Some (end_pos, action_idx, eof) ->
                                            lexbuf_fields.[1] <- of_int rt scan_start_pos
                                            lexbuf_fields.[2] <- of_int rt end_pos
                                            lexbuf_fields.[3] <- of_int rt end_pos
                                            lexbuf_fields.[4] <- of_bool eof
                                            frame.values.[frame.i + 1] <- closures.[action_idx]
                                            frame.i <- frame.i + 1
                                        | None ->
                                            do_raise mal_MatchFailure
                                | builtin_id.SLEEP ->
                                    isSleeping <- true
                                    wakeup <- DateTime.Now.AddSeconds(to_float(frame.values.[frame.i + 1]))
                                    accu <- unit
                                    stack_discard_top()
                                | _ -> dontcare()
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
                                    state <- State.Failure
                                    send_message Message.MALInsufficientMemory
                                | _ -> raise e
                        | Vclosure (arity = arity; env_size = env_size; captures = caps; code = code) ->
                            // Start evaluation of the closure
                            frame.oldenv <- env
                            frame.oldcaptures <- captures
                            env <- Array.zeroCreate<value> env_size
                            captures <- caps
                            for j = 0 to arity - 1 do
                                env.[j] <- frame.values.[frame.i + 1 + j]
                            let n = frame.i + 1 + arity
                            for m = frame.i to n - 1 do
                                frame.values.[m] <- Unchecked.defaultof<value>
                            frame.pc <- Tag.Apply_Closure
                            frame.i <- n
                            frame.calling_code <- code
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
            | UEtailcall args ->
                let frame = frame :?> TailcallFrame
                match frame.pc with
                | Tag.Start ->
                    frame.args <- Array.zeroCreate args.Length
                    frame.pc <- Tag.Tailcall_Eval
                    start_code args.[0]
                | Tag.Tailcall_Eval ->
                    frame.args.[frame.i] <- accu
                    frame.i <- frame.i + 1
                    if frame.i < args.Length then
                        start_code args.[frame.i]
                    else
                        let rec find_upper_apply_loop i =
                            match stack.[i].code with
                            | UEapply _ ->
                                let frame = stack.[i].frame :?> ApplyFrame
                                if frame.pc = Tag.Apply_Closure
                                then i
                                else find_upper_apply_loop (i - 1)
                            | _ -> find_upper_apply_loop (i - 1)
                        let upper_apply_idx = find_upper_apply_loop stack_topidx
                        while stack_topidx <> upper_apply_idx do
                            stack_discard_top()
                        for j = 0 to frame.args.Length - 1 do
                            env.[j] <- frame.args.[j]
                        start_code (stack.[stack_topidx].frame :?> ApplyFrame).calling_code
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
                | _ -> dontcare()
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
                    frame := Tag.Setenvvar_Eval
                    start_code code
                | Tag.Setenvvar_Eval ->
                    match env.[ofs] with
                    | Vvar r -> r := accu
                    | _ -> dontcare()
                    stack_discard_top()
                | _ -> dontcare()
            | UEsetcapvar (ofs, code) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.Setcapturevar_Eval
                    start_code code
                | Tag.Setcapturevar_Eval ->
                    match captures.[ofs] with
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
                | _ -> dontcare()
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
            | UTCexpr (code, tyenv', alloc', ty) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.TopExpr_Eval
                    start_code code
                | Tag.TopExpr_Eval ->
                    tyenv <- tyenv'
                    alloc <- alloc'
                    send_message (Message.EvaluationComplete (tyenv, accu, ty))
                    stack_discard_top()
                | _ -> dontcare()
            | UTCvalvarfun (code, tyenv', alloc', shadowed, new_values) ->
                let frame = frame :?> ref<Tag>
                match !frame with
                | Tag.Start ->
                    frame := Tag.TopValVarFun_Eval
                    start_code code
                | Tag.TopValVarFun_Eval ->
                    tyenv <- tyenv'
                    alloc <- alloc'
                    for ofs in shadowed do
                        env.[ofs] <- Value.zero
                    print_new_values new_values
                    stack_discard_top()
                | _ -> dontcare()
            | _ -> dontcare()

            if state = State.Running then
                if stack_topidx + 1 = 0 then
                    state <- State.Success
                elif stack_topidx + 1 >= config.maximum_stack_depth then
                    state <- State.Failure
                    send_message Message.MALStackOverflow
                elif not (check_free_memory rt 0) then
                    state <- State.Failure
                    send_message Message.MALInsufficientMemory

            cycles <- cycles + 1L

    let alias new_name orig_name =
        cancel()
        let vi = Option.get (Types.try_get_value tyenv orig_name)
        tyenv <- Types.add_value tyenv new_name vi
        let { ofs = orig_ofs } = alloc.Get(orig_name)
        let new_ofs = alloc.Add(new_name, Immutable)
        env <- array_ensure_capacity_exn config.maximum_array_length (new_ofs + 1) env
        env.[new_ofs] <- env.[orig_ofs]
    
    let obj_of_value_cache = Dictionary<Type, HashSet<value> -> value -> obj>()
    let value_of_obj_cache = Dictionary<Type, runtime -> obj -> value>()


    let set (name : string) (value : value) (ty : type_expr) (access : access) =
        tyenv <- Types.add_value tyenv name { vi_access = access; vi_type = ty }
        let ofs = alloc.Add(name, access)
        env <- array_ensure_capacity_exn config.maximum_array_length (ofs + 1) env
        env.[ofs] <-
            match access with
            | Immutable -> value
            | Mutable -> Vvar (ref value)
        ofs

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
            | UEsetenvvar _ -> pfni "Setvar"
            | UEsetcapvar _ -> pfni "Setcapturevar"
            | UEblock _ -> pfni "Block"
            | UEblockwith _ -> pfni "Blockwith"
            | UEarray _ -> pfni "Array"
            | UEapply _ -> pfni "Apply"
            | UEtailcall _ -> pfni "UEtailcall"
            | UEbegin _ -> pfni "Begin"
            | UEcase _ -> pfni "Case"
            | UEtry _ -> pfni "Try"
            | UEif _ -> pfni "If"
            | UEfor _ -> pfni "For"
            | UEwhile _ -> pfni "While"
            | UEcompare _ -> pfni "Compare"
            | UCval _ -> pfni "Val"
            | UCvar _ -> pfni "Var"
            | UTCexpr _ -> pfni "TopExpr"
            | UTCvalvarfun _ -> pfni "TopValVarFun"
            | _ -> dontcare()

    member this.State with get() = state
    member this.Run(ticks : int64) = run ticks
    member this.Accu = accu
    member this.Wakeup = wakeup
    member this.Tyenv = tyenv
    member this.Alloc = alloc
    member this.Cycles = cycles
    member this.LatestMessage = latestMessage
    member this.MessageHook with get() = message_hook and set f = message_hook <- f
    member this.PrintString with get() = rt.print_string and set f = rt.print_string <- f
    member this.Runtime = rt
    member this.IsSleeping = isSleeping
    member this.Result =
        match latestMessage with
        | Some (Message.EvaluationComplete (tyenv, ty, value)) -> (tyenv, ty, value)
        | _ -> raise (InvalidOperationException())
    member this.Cancel() = cancel()
    
    member this.Alias newName origName =
        alias newName origName
    
    member this.GEnv =
        if stack_topidx <> -1 then dontcare()
        env

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
        set name value ty Immutable |> ignore

    /// Internally calls Cancel()    
    member this.Val<'T>(name : string, x : 'T) =
        cancel()
        let v = Value.value_of_obj value_of_obj_cache tyenv typeof<'T> Value.dummy_runtime x
        let ty = Types.typeexpr_of_type tyenv (Dictionary()) typeof<'T>
        set name v ty Immutable |> ignore

    /// Internally calls Cancel()    
    member this.Var<'T>(name : string, x : 'T) =
        cancel()
        let v = Value.value_of_obj value_of_obj_cache tyenv typeof<'T> Value.dummy_runtime x
        let ty = Types.typeexpr_of_type tyenv (Dictionary()) typeof<'T>
        set name v ty Mutable


    /// Internally calls Cancel()    
    member this.GetVar(name : string) : value ref =
        cancel()
        let { ofs = ofs; access = access } = alloc.Get(name)
        match access with
        | Immutable -> dontcare()
        | Mutable ->
            match env.[ofs] with
            | Vvar r -> r
            | _ -> dontcare()

    /// Internally calls Cancel()    
    member this.GetValue(name : string) : value =
        cancel()
        let { ofs = ofs; access = access } = alloc.Get(name)
        match access with
        | Immutable -> env.[ofs]
        | Mutable -> match env.[ofs] with Vvar r -> !r | _ -> dontcare()

    /// Internally calls Cancel()    
    member this.Get<'T>(name : string) =
        let value = this.GetValue(name)
        let obj = Value.obj_of_value obj_of_value_cache tyenv (touch_create()) typeof<'T> value
        obj :?> 'T
    
    member this.GetFromOfs<'T>(ofs : int) =
        cancel()
        let value =
            match env.[ofs] with
            | Vvar r -> !r
            | v -> v
        let obj = Value.obj_of_value obj_of_value_cache tyenv (touch_create()) typeof<'T> value
        obj :?> 'T

    /// Internally calls Cancel()    
    member this.Fun<'T, 'U>(name : string, f : runtime -> 'T -> 'U) =
        cancel()
        let v = Value.wrap_fsharp_func tyenv obj_of_value_cache value_of_obj_cache typeof<runtime -> 'T -> 'U> f
        let ty = Types.typeexpr_of_type tyenv (Dictionary()) typeof<'T -> 'U>
        set name v ty Immutable |> ignore

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

    member this.Stacktrace(limit, sb) = stacktrace limit sb

    member this.ObjOfMal<'T>(value : value) = Value.obj_of_value obj_of_value_cache tyenv (touch_create()) typeof<'T> value
    member this.ValueOfObj<'T>(obj : 'T) = Value.value_of_obj value_of_obj_cache tyenv typeof<'T> Value.dummy_runtime obj
