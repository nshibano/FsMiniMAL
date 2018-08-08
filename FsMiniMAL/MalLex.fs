module FsMiniMAL.MalLex
// Derived from https://github.com/fsprojects/FsLexYacc/blob/master/src/FsLex/fslexast.fs
// This file is licensed in Apache License 2.0.
// (c) Microsoft Corporation 2005-2008.
// (c) Nozomi Shibano 2018

open System.Collections.Generic
open Syntax

type MultiMap<'a, 'b> = Dictionary<'a, List<'b>>

type NfaNode = 
    { Id : int
      Transitions : MultiMap<int, NfaNode>
      Accepted : int option }

type DfaNode = 
    { Id : int
      Transitions : Dictionary<int, DfaNode>
      Accepted : int option }


let AddToMultiMap (map : MultiMap<'a, 'b>) (a : 'a) (b : 'b) =
    match map.TryGetValue a with
    | true, l -> l.Add(b)
    | false, _ ->
        let l = List<'b>()
        l.Add(b)
        map.[a] <- l

type NfaNodeMap() = 
    let map = new Dictionary<int, NfaNode>()
    member x.Item with get(nid) = map.[nid]
    member x.Count = map.Count

    member x.NewNfaNode(trs, ac) = 
        let nodeId = map.Count

        let trDict = new Dictionary<_, _>()
        for (a, b) in trs do
           AddToMultiMap trDict a b
           
        let node : NfaNode = { Id = nodeId; Transitions = trDict; Accepted = ac }
        map.[nodeId] <- node
        node

let LexerStateToNfa (alphabets : HashSet<int>) (macros: Dictionary<string, regexp>) (clauses: (regexp * expression) list) = 

    /// Table allocating node ids 
    let nfaNodeMap = new NfaNodeMap()
    
    /// Compile a regular expression into the NFA
    let rec CompileRegexp re dest = 
        match re with 
        | Alt res -> 
            let trs = List.map (fun re -> (Alphabet_Epsilon, CompileRegexp re dest)) res
            nfaNodeMap.NewNfaNode(trs, None)
        | Seq res -> 
            List.foldBack CompileRegexp res dest 
        | Inp (Alphabet c) -> 
            nfaNodeMap.NewNfaNode([(c, dest)], None)
        | Star re -> 
            let nfaNode = nfaNodeMap.NewNfaNode([(Alphabet_Epsilon, dest)], None)
            let sre = CompileRegexp re nfaNode
            AddToMultiMap nfaNode.Transitions Alphabet_Epsilon sre
            nfaNodeMap.NewNfaNode([(Alphabet_Epsilon,sre); (Alphabet_Epsilon,dest)], None)
        | Macro m -> 
            if not (macros.ContainsKey(m)) then failwith ("The macro "+m+" is not defined");
            CompileRegexp (macros.[m]) dest 
        | Inp Any -> 
            let re = Alt([ for c in alphabets do
                             yield Inp (Alphabet c)
                           yield Inp (Alphabet Alphabet_Others)])
            CompileRegexp re dest
        | Inp (NotCharSet chars) ->
            let re = Alt [for c in alphabets do
                            if not (chars.Contains(c)) then
                              yield Inp (Alphabet c)
                          yield Inp (Alphabet Alphabet_Others)]
            CompileRegexp re dest
    
    let actions = List<expression>()

    /// Compile an acceptance of a regular expression into the NFA
    let sTrans (regexp, code) =
        let actionIndex = actions.Count
        actions.Add(code)
        let sAccept = nfaNodeMap.NewNfaNode([], Some actionIndex)
        CompileRegexp regexp sAccept

    let trs = List.map (fun clause -> (Alphabet_Epsilon, sTrans clause)) clauses
    let nfaStartNode = nfaNodeMap.NewNfaNode(trs, None)
    nfaStartNode, actions.ToArray(), nfaNodeMap

type NfaNodeIdSetBuilder = HashSet<int>
type NfaNodeIdSet = int array

let createNfaNodeIdSet (builder : NfaNodeIdSetBuilder) : NfaNodeIdSet =
    let ary = Array.zeroCreate<int> builder.Count
    let mutable ofs = 0
    for id in builder do
        ary.[ofs] <- id
        ofs <- ofs + 1
    Array.sortInPlace ary
    ary

let array_chooseFirst (f : 'a -> 'b option) (ary : 'a array) =
    let rec loop i =
        if i < ary.Length then
            match f ary.[i] with
            | Some y -> Some y
            | None -> loop (i + 1)
        else None
    loop 0

let NfaToDfa (nfaNodeMap : NfaNodeMap) (nfaStartNode : NfaNode) = 
    let rec EClosure1 (acc : NfaNodeIdSetBuilder) (n : NfaNode) = 
        if not (acc.Contains(n.Id)) then 
            acc.Add(n.Id) |> ignore
            match n.Transitions.TryGetValue(Alphabet_Epsilon) with
            | true, tr -> Seq.iter (EClosure1 acc) tr
            | false, _ -> ()

    let EClosure (moves : seq<int>) = 
        let acc = new NfaNodeIdSetBuilder(HashIdentity.Structural)
        for i in moves do
            EClosure1 acc nfaNodeMap.[i]
        createNfaNodeIdSet acc

    // Compute all the immediate one-step moves for a set of NFA states, as a dictionary
    // mapping inputs to destination lists
    let ComputeMoves (nset : NfaNodeIdSet) = 
        let moves = new MultiMap<_, _>()
        Array.iter (fun nodeId -> 
            for KeyValue(inp, dests) in nfaNodeMap.[nodeId].Transitions do
                if inp <> Alphabet_Epsilon then
                    Seq.iter (fun (dest : NfaNode) -> AddToMultiMap moves inp dest.Id) dests) nset
        moves

    let acc = new NfaNodeIdSetBuilder(HashIdentity.Structural)
    EClosure1 acc nfaStartNode
    let nfaSet0 = createNfaNodeIdSet acc

    let dfaNodes = Dictionary<NfaNodeIdSet, DfaNode>(HashIdentity.Structural)

    let GetDfaNode (nfaSet : NfaNodeIdSet) =
        match dfaNodes.TryGetValue(nfaSet) with
        | true, dfaNode -> dfaNode
        | false, _ ->
            let dfaNode =
                { Id = dfaNodes.Count
                  Transitions = Dictionary()
                  Accepted = array_chooseFirst (fun nid -> nfaNodeMap.[nid].Accepted) nfaSet }
            dfaNodes.[nfaSet] <- dfaNode
            dfaNode
    
    let workList = Queue<_>([| nfaSet0 |])
    let doneSet = HashSet<NfaNodeIdSet>(HashIdentity.Structural)

    while workList.Count > 0 do
        let nfaSet = workList.Dequeue()
        if not (doneSet.Contains(nfaSet)) then
            let moves = ComputeMoves nfaSet
            for KeyValue(inp, movesForInput) in moves do
                assert (inp <> Alphabet_Epsilon)
                let moveSet = EClosure movesForInput
                if moveSet.Length <> 0 then 
                    let dfaNode = GetDfaNode nfaSet
                    dfaNode.Transitions.[inp] <- GetDfaNode moveSet
                    workList.Enqueue(moveSet)
            doneSet.Add(nfaSet) |> ignore

    let ruleStartNode = GetDfaNode nfaSet0
    let ruleNodes =
        let ary = Array.ofSeq (dfaNodes.Values)
        Array.sortInPlaceBy (fun (s : DfaNode) -> s.Id) ary
        ary
    ruleStartNode, ruleNodes

let GetAlphabets (macros : Dictionary<string, regexp>) (clauses : (regexp * expression) list) =
    let accu = HashSet<int>()
    let rec loop (re : regexp) =
        match re with
        | Alt l -> List.iter loop l
        | Seq l -> List.iter loop l
        | Inp (Alphabet c) ->
            if c >= 0 then
                accu.Add(c) |> ignore
        | Inp Any -> ()
        | Inp (NotCharSet set) ->
            for c in set do
                accu.Add(c) |> ignore
        | Star re -> loop re
        | Macro name ->
            match macros.TryGetValue(name) with
            | true, re -> loop re
            | false, _ -> failwithf "Macro %s is not defined." name
    
    for re, _ in clauses do
        loop re
    accu

let Compile (defs : lex_def list) =
    let macros = Dictionary<string, regexp>()
    macros.Add("eof", Inp (Alphabet (Alphabet_Eof)))
    let accu = List()
    for def in defs do
        match def with
        | Macro_def (name, regexp) -> macros.Add(name, regexp)
        | Rules_def rules ->
            let perRuleData = List<_>()
            for (name, args, clauses) in rules do
                let alphabets = GetAlphabets macros clauses
                let nfa, actions, nfaNodeMap = LexerStateToNfa alphabets macros clauses
                let ruleStartNode, ruleNodes = NfaToDfa nfaNodeMap nfa
                perRuleData.Add((name, args, alphabets, ruleStartNode, actions))
                //System.Console.WriteLine(sprintf "%s %d %d %d" name alphabets.Count nfaNodeMap.Count ruleNodes.Length)
            accu.Add((perRuleData.ToArray()))
    accu.ToArray()
