module FsMiniMAL.Translate

open System.Collections.Generic

open Syntax
open Types
open Value
   
let rec pattern (alloc : alloc) (leftmost : bool) (pat : Syntax.pattern) : Value.pattern = 
    match pat.sp_desc with
    | SPid s ->
        let ofs =
            if leftmost
            then alloc.Add(s, access.Immutable)
            else alloc.Get(s).ofs
        UPid ofs
    | SPas (p, ident) ->
        let ofs =
            if leftmost
            then alloc.Add(ident, access.Immutable)
            else alloc.Get(ident).ofs
        let up = pattern alloc leftmost p
        UPas (up, ofs)
    | SPint i -> UPint(int i)
    | SPchar c -> UPchar c
    | SPfloat x -> UPfloat x
    | SPstring s -> UPstring s
    | SPtuple [] -> UPint 0
    | SPtuple l -> 
        let ul = List.map (pattern alloc leftmost) l
        UPblock(0, Array.ofSeq ul)
    | SParray l -> 
        let ul = List.map (pattern alloc leftmost) l
        UParray(Array.ofSeq ul)
    | SPblock(tag, args) ->
        if args.Length = 0 then
            UPint tag
        else
            let upatl = List.map (pattern alloc leftmost) args
            UPblock(tag, Array.ofList upatl)
    | SPapply _ -> dontcare ()
    | SPrecord _ -> dontcare ()
    | SPany -> UPany
    | SPtype(pat, _) -> pattern alloc leftmost pat
    | SPor (p1, p2) ->
        let up1 = pattern alloc leftmost p1
        let up2 = pattern alloc false    p2
        UPor (up1, up2)

let rec command (alloc : alloc) (tailcall_info : (string * int) option) (cmd : Syntax.command) : Value.code = 
    match cmd.sc_desc with
    | SCexpr e -> expression alloc tailcall_info e
    | SCval l ->
        let uel = List.map (fun (_, e) -> expression alloc None e) l
        let upatl = List.map (fun (pat, _) -> pattern alloc true pat) l
        UCval(Array.ofList (List.zip upatl uel))
    | SCfun l -> 
        let arityl = List.map (fun (_, (e : expression)) -> match e with { se_desc = SEfn (patl, _) } -> patl.Length | _ -> dontcare()) l
        // Allocate location beforehand, to allow recursive definition.
        let ofss = List.map (fun (name, _) -> alloc.Add(name, Immutable)) l
        let uel =
            List.map2 (fun (name, e) arity ->
                let ue = expression alloc (Some (name, arity)) e
                ue) l arityl
        UCfun(Array.ofSeq (List.zip ofss uel))
    | SCvar l -> 
        let uel = List.map (fun (_, e) -> expression alloc None e) l
        let ofsl = List.map (fun (name, _) -> alloc.Add(name, access.Mutable)) l
        UCvar(Array.ofSeq (List.zip ofsl uel))
    | _ -> dontcare()

and expression (alloc : alloc) (tailcall_info : (string * int) option) (se : Syntax.expression) : Value.code =
    let env_at_begin = alloc.Begin()

    let ue = 
        match se.se_desc with
        | SEid s ->
            let info = alloc.Get(s)
            match info.is_capture, info.access with
            | false, Immutable -> UEgetenv info.ofs
            | false, Mutable -> UEgetenvvar info.ofs
            | true, Immutable -> UEgetcap info.ofs
            | true, Mutable -> UEgetcapvar info.ofs
        | SEconstr (tag, l) ->
            if l.Length = 0 then
                UEconst(of_int dummy_runtime tag)
            else
                let uel = List.map (expression alloc None) l
                UEblock(tag, Array.ofSeq uel)
        | SEint s -> UEconst(Value.of_int dummy_runtime (int s))
        | SEchar c -> UEconst(Value.of_char dummy_runtime c)
        | SEfloat x -> UEconst (Value.of_float dummy_runtime x)
        | SEtuple [] -> UEconst(Value.unit)
        | SEtuple l -> UEblock(0, Array.ofSeq (Seq.map (expression alloc None) l))
        | SElist (LKarray, l) -> UEarray(Array.ofSeq(Seq.map (expression alloc None) l))
        | SElist (LKlist, l) ->
            let rec loop l =
                match l with
                | [] -> UEconst Value.zero
                | hd :: tl -> UEblock (1, [| expression alloc None hd; loop tl |])
            loop l
        | SEstring s -> UEconst (of_string dummy_runtime s)
        | SEurecord (l, None) ->
            let ary = Array.zeroCreate (List.length l)
            for (index, _, e) in l do
                let ue = expression alloc None e
                ary.[index] <- ue
            UEblock(0, ary)
        | SEurecord (l, Some orig) ->
            let u_orig = expression alloc None orig
            let indexes = Array.ofList (List.map (fun (i, _, _) -> i) l)
            let uexprs = Array.ofList (List.map (fun (_, _, e) -> expression alloc None e) l)
            UEblockwith (u_orig, indexes, uexprs)
        | SErecord _ -> dontcare ()
        | SEapply({ se_desc = SEid "&&" }, [ e1; e2 ]) ->
             let ue1 = expression alloc None e1
             let ue2 = expression alloc tailcall_info e2
             UEif(ue1, ue2, UEconst(Value.``false``))
        | SEapply({ se_desc = SEid "||" }, [ e1; e2 ]) ->
             let ue1 = expression alloc None e1
             let ue2 = expression alloc tailcall_info e2
             UEif(ue1, UEconst(Value.``true``), ue2)
        | SEapply(e, l) ->
            let rec is_ident (e : expression) =
                match e with
                | { se_desc = SEid ident } -> Some ident
                | { se_desc = SEtype (e, _) } -> is_ident e
                | _ -> None
            let is_tailcall =
                match is_ident e, tailcall_info with
                | Some name, Some (name', arity) ->
                    name = name' && l.Length = arity && not (alloc.EnvBindings.ContainsKey(name))
                | _ -> false
            if is_tailcall then
                UEtailcall (Array.ofList (List.map (expression alloc None) l))
            else
                let ue = expression alloc None e
                let uargs = List.map (expression alloc None) l
                UEapply(Array.ofList (ue :: uargs))
        | SEfn(patl, e) -> 
            let patl = Array.ofList patl
            let alloc' = alloc.CreateNewEnv()

            // Allocate locations for argumemts at head of the env.
            for i = 0 to patl.Length - 1 do
                alloc'.Allocate() |> ignore
            
            let argmatch_commands =
                let accu = List()

                let rec strip_sptype (pat : Syntax.pattern) =
                    match pat with
                    | { sp_desc = SPtype (pat, _)} -> strip_sptype pat
                    | _ -> pat

                for i = 0 to patl.Length - 1 do
                    match strip_sptype patl.[i] with
                    | { sp_desc = SPany } -> ()
                    | { sp_desc = SPid s } ->
                        // There is no need to evaluate pattern.
                        alloc'.EnvBindings <- alloc'.EnvBindings.Add(s, { alloc_info.ofs = i; access = Immutable; is_capture = false })
                    | _ -> 
                        // Compile the pattern.
                        let upat = pattern alloc' true patl.[i]
                        // Create command to perform the match for pattern and argument.
                        accu.Add(UCval ([| (upat, UEgetenv i) |]))
                accu.ToArray()

            // Compile the function body
            let ue = expression alloc' tailcall_info e
            
            // Create table for captured variables
            let is_capture_flags, ofss =
                let pairs = Array.map (fun (info_from : alloc_info, info_to : alloc_info) -> (info_to.ofs, (info_from.is_capture, info_from.ofs))) (Array.ofSeq alloc'.Captures.Values)
                Array.sortInPlace pairs
                Array.unzip (Array.map snd pairs)

            
            // Create function body with argument pattern evaluation at start.
            let body =
                if argmatch_commands.Length = 0 then ue
                else
                    match ue with
                    | UEbegin cmds -> UEbegin (Array.append argmatch_commands cmds)
                    | _ -> UEbegin (Array.append argmatch_commands [| ue |])

            UEfn(alloc'.MaxEnvSize, patl.Length, is_capture_flags, ofss, body)
        | SEbegin cl ->
            let len = cl.Length
            let ucl = List.mapi (fun i c -> command alloc (if i = len - 1 then tailcall_info else None) c) cl
            UEbegin(Array.ofList (ucl))
        | SEcase(e, cases) -> 
            let ue = expression alloc None e
            let ucases = 
                List.map (fun (pat, ew, e) ->
                    let env_at_begin = alloc.Begin()
                    let upat = pattern alloc true pat
                    let uew = Option.map (expression alloc None) ew
                    let ue = expression alloc tailcall_info e
                    alloc.End(env_at_begin)
                    (upat, uew, ue)) cases
            UEcase(ue, Array.ofSeq ucases)
        | SEtry (e, cases) ->
            let ue = expression alloc None e
            let ucases = 
                List.map (fun (pat, _, e) ->
                    let env_at_begin = alloc.Begin()
                    let upat = pattern alloc true pat
                    let ue = expression alloc tailcall_info e
                    alloc.End(env_at_begin)
                    (upat, ue)) cases
            UEtry(ue, Array.ofList ucases)
        | SEifthenelse(e1, e2, e3) ->
            let ue1 = expression alloc None e1
            let ue2 = expression alloc tailcall_info e2
            let ue3 = match e3 with Some e3 -> expression alloc tailcall_info e3 | None -> UEconst (Value.unit)
            UEif(ue1, ue2, ue3)
        | SEset(s, e) -> 
            let ue = expression alloc None e
            match alloc.Get(s) with
            | { ofs = ofs; access = Mutable; is_capture = false } -> UEsetenvvar(ofs, ue)
            | { ofs = ofs; access = Mutable; is_capture = true  } -> UEsetcapvar(ofs, ue)
            | _ -> dontcare()
        | SEgetfield _ | SEsetfield _ -> dontcare ()
        | SEfor(s, e1, dir, e2, e3) -> 
            let ue1 = expression alloc None e1
            let ue2 = expression alloc None e2
            let loopvar = alloc.Add(s, access.Immutable)
            let ue3 = expression alloc None e3
            UEfor (loopvar, ue1, dir, ue2, ue3)
        | SEwhile(e1, e2) -> 
            let ue1 = expression alloc None e1
            let ue2 = expression alloc None e2
            UEwhile(ue1, ue2)
        | SEtype(e, _) -> expression alloc tailcall_info e
        | SEformat fmt -> UEconst (Vformat fmt)

    alloc.End(env_at_begin)
    ue

let translate_top_command_list (alloc : alloc) (tyenvs : tyenv array) (ccmds : command array) =
    let mutable alloc = alloc.Clone()
    let tcmds = ResizeArray()

    let find_shadowed_offsets old_alloc new_values =
        let shadowed = ResizeArray<int>()
        for new_name, _ in new_values do
            match old_alloc.EnvBindings.TryGetValue(new_name) with
            | true, { ofs = ofs } -> shadowed.Add(ofs)
            | false, _ -> ()
        shadowed.ToArray()

    tcmds.Add(UTCupd (tyenvs.[0], alloc.Clone()))

    for i = 0 to ccmds.Length - 1 do
        let cmd = ccmds.[i]
        match cmd.sc_desc with
        | SCCexpr (e, ty) ->
            let ue = expression alloc None e
            tcmds.Add(UTCexpr (ue, tyenvs.[i+1], alloc.Clone(), ty))
        | SCCval (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc None { sc_desc = SCval l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCCvar (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc None { sc_desc = SCvar l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCCfun (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc None { sc_desc = SCfun l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCtype defs ->
            let names = List.map (fun (td : typedef) -> td.sd_name) defs
            tcmds.Add(UTCtype(names, tyenvs.[i+1]))
        | SChide name ->
            tcmds.Add(UTChide (name, tyenvs.[i+1], alloc.Clone()))
        | SCremove name ->
            let ofs = alloc.Get(name).ofs
            alloc.EnvBindings <- alloc.EnvBindings.Remove(name)
            tcmds.Add(UTCremove (name, ofs, tyenvs.[i+1], alloc.Clone()))
        | SCexn (name, _) ->
            tcmds.Add(UTCexn(name, tyenvs.[i+1], alloc.Clone()))
        | SCClex rules ->
            let new_values = List.init rules.Length (fun i ->
                let (name, _, _, _, _, _, vi) = rules.[i]
                (name, vi))

            let shadowed = find_shadowed_offsets alloc new_values

            // Allocate location beforehand to allow recursive definition.
            let ofss = Array.map (fun (name, _, _, _, _, _, _) -> alloc.Add(name, access.Immutable)) rules

            let accu = List()
            for i = 0 to rules.Length - 1 do
                let (_, args, alphabets, dfa, actions, _, _) = rules.[i]
                let actions_accu = List()
                for action in actions do
                    let args = (List.map (fun arg -> { sp_desc = SPid arg; sp_loc = action.se_loc }) args) @ [{ sp_desc = SPid "lexbuf"; sp_loc = action.se_loc }]
                    let ue = expression alloc None ({ se_desc = SEfn (args, action); se_loc = action.se_loc })
                    actions_accu.Add(ue)
                accu.Add(args.Length + 1, ofss.[i], alphabets, dfa, actions_accu.ToArray())
            
            tcmds.Add(UTClex (accu.ToArray(), tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | _ -> dontcare()

    alloc.MaxEnvSize, tcmds.ToArray()