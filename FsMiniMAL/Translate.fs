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
            else fst (alloc.Get(s))
        UPid ofs
    | SPas (p, ident) ->
        let ofs =
            if leftmost
            then alloc.Add(ident, access.Immutable)
            else fst (alloc.Get(ident))
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

let rec command (alloc : alloc) (cmd : Syntax.command) : Value.code = 
    match cmd.sc_desc with
    | SCexpr e -> expression alloc e
    | SCval l ->
        let uel = List.map (fun (_, e) -> expression alloc e) l
        let upatl = List.map (fun (pat, _) -> pattern alloc true pat) l
        UCval(Array.ofList (List.zip upatl uel))
    | SCfun l -> 
        let sl, el = List.unzip l
        // Allocate location beforehand, to allow recursive definition.
        let ofss = List.map (fun s -> alloc.Add(s, access.Immutable)) sl
        let uel = List.map (fun e -> expression alloc e) el
        UCfun(Array.ofSeq (List.zip ofss uel))
    | SCvar l -> 
        let uel = List.map (fun (_, e) -> expression alloc e) l
        let ofsl = List.map (fun (name, _) -> alloc.Add(name, access.Mutable)) l
        UCvar(Array.ofSeq (List.zip ofsl uel))
    | _ -> dontcare()

and expression (alloc : alloc) (se : Syntax.expression) : Value.code = 
    let locals_at_start = alloc.Locals
    
    let ue = 
        match se.se_desc with
        | SEid s ->
            match alloc.Get(s) with
            | (ofs, Immutable) -> UEenv ofs
            | (ofs, Mutable) -> UEenvvar ofs
        | SEconstr (tag, l) ->
            if l.Length = 0 then
                UEconst(of_int dummy_runtime tag)
            else
                let uel = List.map (expression alloc) l
                UEblock(tag, Array.ofSeq uel)
        | SEint s -> UEconst(Value.of_int dummy_runtime (int s))
        | SEchar c -> UEconst(Value.of_char dummy_runtime c)
        | SEfloat x -> UEconst (Value.of_float dummy_runtime x)
        | SEtuple [] -> UEconst(Value.unit)
        | SEtuple l -> UEblock(0, Array.ofSeq (Seq.map (expression alloc) l))
        | SEarray l -> UEarray(Array.ofSeq(Seq.map (expression alloc) l))
        | SEstring s -> UEconst (of_string dummy_runtime s)
        | SEurecord (l, None) ->
            let ary = Array.zeroCreate (List.length l)
            for (index, _, e) in l do
                let ue = expression alloc e
                ary.[index] <- ue
            UEblock(0, ary)
        | SEurecord (l, Some orig) ->
            let u_orig = expression alloc orig
            let indexes = Array.ofList (List.map (fun (i, _, _) -> i) l)
            let uexprs = Array.ofList (List.map (fun (_, _, e) -> expression alloc e) l)
            UEblockwith (u_orig, indexes, uexprs)
        | SErecord _ -> dontcare ()
        | SEapply({ se_desc = SEid "&&" }, [ e1; e2 ]) ->
             let ue1 = expression alloc e1
             let ue2 = expression alloc e2
             UEif(ue1, ue2, UEconst(Value.``false``))
        | SEapply({ se_desc = SEid "||" }, [ e1; e2 ]) ->
             let ue1 = expression alloc e1
             let ue2 = expression alloc e2
             UEif(ue1, UEconst(Value.``true``), ue2)
        | SEapply(e, l) -> 
            let ue = expression alloc e
            let uargs = List.map (expression alloc) l
            UEapply(Array.ofList (ue :: uargs))
        | SEfn(patl, e) -> 
            let patl = Array.ofList patl
            let alloc' = alloc.CreateNewEnv()

            // Allocate locations for argumemts at head of the frame.
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
                        alloc'.Locals <- alloc'.Locals.Add(s, (i, access.Immutable))
                    | _ -> 
                        // Compile the pattern.
                        let upat = pattern alloc' true patl.[i]
                        // Create command to perform the match for pattern and argument.
                        accu.Add(UCval ([| (upat, UEenv i) |]))
                accu.ToArray()

            // Compile the function body
            let ue = expression alloc' e
            
            // Create table for captured variables
            let capture_ofs_from, capture_ofs_to =
                let captures = Array.ofSeq alloc'.Captured
                let pairs =
                    Array.map (fun (kv : KeyValuePair<string, (int * access)>) ->
                            let ofs, kind = alloc.Get(kv.Key)
                            let ofs', kind' = kv.Value
                            if kind <> kind' then dontcare()
                            (ofs, ofs')) captures
                Array.sortInPlaceBy (fun (i, j) -> (j, i)) pairs
                Array.unzip pairs

            // Create function body with argument pattern evaluation at start.
            let body =
                if argmatch_commands.Length = 0 then ue
                else
                    match ue with
                    | UEbegin cmds -> UEbegin (Array.append argmatch_commands cmds)
                    | _ -> UEbegin (Array.append argmatch_commands [| ue |])

            UEfn(alloc'.EnvSize, patl.Length, capture_ofs_from, capture_ofs_to, body)
        | SEbegin cl ->
            let ucl = List.map (command alloc) cl
            UEbegin(Array.ofList (ucl))
        | SEcase(e, cases) -> 
            let ue = expression alloc e
            let ucases = 
                List.map (fun (pat, ew, e) ->
                    let locals_at_start = alloc.Locals
                    let upat = pattern alloc true pat
                    let uew = Option.map (expression alloc) ew
                    let ue = expression alloc e
                    alloc.Locals <- locals_at_start
                    (upat, uew, ue)) cases
            UEcase(ue, Array.ofSeq ucases)
        | SEtry (e, cases) ->
            let ue = expression alloc e
            let ucases = 
                List.map (fun (pat, _, e) -> 
                    let locals_at_start = alloc.Locals
                    let upat = pattern alloc true pat
                    let ue = expression alloc e
                    alloc.Locals <- locals_at_start
                    (upat, ue)) cases
            UEtry(ue, Array.ofList ucases)
        | SEifthenelse(e1, e2, e3) ->
            let ue1 = expression alloc e1
            let ue2 = expression alloc e2
            let ue3 = match e3 with Some e3 -> expression alloc e3 | None -> UEconst (Value.unit)
            UEif(ue1, ue2, ue3)
        | SEset(s, e) -> 
            let ue = expression alloc e
            match alloc.Get(s) with
            | (ofs, Mutable) -> UEsetenvvar(ofs, ue)
            | _ -> dontcare()
        | SEgetfield _ | SEsetfield _ -> dontcare ()
        | SEfor(s, e1, dir, e2, e3) -> 
            let ue1 = expression alloc e1
            let ue2 = expression alloc e2
            let loopvar = alloc.Add(s, access.Immutable)
            let ue3 = expression alloc e3
            UEfor (loopvar, ue1, dir, ue2, ue3)
        | SEwhile(e1, e2) -> 
            let ue1 = expression alloc e1
            let ue2 = expression alloc e2
            UEwhile(ue1, ue2)
        | SEtype(e, _) -> expression alloc e
        | SEformat fmt -> UEconst (Vformat fmt)
    alloc.Locals <- locals_at_start
    ue

let translate_top_command_list (alloc : alloc) (tyenvs : tyenv array) (ccmds : command array) =
    let mutable alloc = alloc.Clone()
    let tcmds = ResizeArray()

    let find_shadowed_offsets old_alloc new_values =
        let shadowed = ResizeArray<int>()
        for new_name, _ in new_values do
            match old_alloc.Locals.TryGetValue(new_name) with
            | true, (ofs, _) -> shadowed.Add(ofs)
            | false, _ -> ()
        shadowed.ToArray()

    tcmds.Add(UTCupd (tyenvs.[0], alloc.Clone()))

    for i = 0 to ccmds.Length - 1 do
        let cmd = ccmds.[i]
        match cmd.sc_desc with
        | SCCexpr (e, ty) ->
            let ue = expression alloc e
            tcmds.Add(UTCexpr (ue, tyenvs.[i+1], alloc.Clone(), ty))
        | SCCval (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc { sc_desc = SCval l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCCvar (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc { sc_desc = SCvar l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCCfun (l, new_values) ->
            let shadowed = find_shadowed_offsets alloc new_values
            let uc = command alloc { sc_desc = SCfun l; sc_loc = cmd.sc_loc }
            tcmds.Add(UTCvalvarfun (uc, tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | SCtype defs ->
            let names = List.map (fun (td : typedef) -> td.sd_name) defs
            tcmds.Add(UTCtype(names, tyenvs.[i+1]))
        | SChide name ->
            tcmds.Add(UTChide (name, tyenvs.[i+1], alloc.Clone()))
        | SCremove name ->
            let ofs, _ = alloc.Get(name)
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
                    let ue = expression alloc ({ se_desc = SEfn (args, action); se_loc = action.se_loc })
                    actions_accu.Add(ue)
                accu.Add(args.Length + 1, ofss.[i], alphabets, dfa, actions_accu.ToArray())
            
            tcmds.Add(UTClex (accu.ToArray(), tyenvs.[i+1], alloc.Clone(), shadowed, new_values))
        | _ -> dontcare()

    alloc.EnvSize, tcmds.ToArray()