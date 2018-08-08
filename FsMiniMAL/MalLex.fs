﻿module FsMiniMAL.MalLex
// Derived from https://github.com/fsprojects/FsLexYacc/blob/master/src/FsLex/fslexast.fs
// This file is licensed in Apache License 2.0.
// (c) Microsoft Corporation 2005-2008.
// (c) Nozomi Shibano 2018

open System.Collections.Generic
open Syntax

type NfaNode = 
    { Id : int
      Transitions : Dictionary<int, NfaNode list>
      Accepted : expression option }

type DfaNode = 
    { Id : int
      Transitions : Dictionary<int, DfaNode>
      Accepted : expression option }

type MultiMap<'a,'b> = Dictionary<'a,'b list>

let AddToMultiMap (map : MultiMap<'a, 'b>) (a : 'a) (b : 'b) =
    map.[a] <- b :: (if map.ContainsKey(a) then map.[a] else [])

type NfaNodeMap() = 
    let map = new Dictionary<int, NfaNode>()
    member x.Item with get(nid) = map.[nid]
    member x.Count = map.Count

    member x.NewNfaNode(trs, ac) = 
        let nodeId = map.Count+1 // ID zero is reserved

        let trDict = new Dictionary<_,_>()
        for (a, b) in trs do
           AddToMultiMap trDict a b
           
        let node : NfaNode = { Id=nodeId; Transitions=trDict; Accepted=ac }
        map.[nodeId] <- node
        node

let LexerStateToNfa (alphabets : HashSet<int>) (macros: Map<string, regexp>) (clauses: (regexp * expression) list) = 

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
    
    /// Compile an acceptance of a regular expression into the NFA
    let sTrans (regexp, code) = 
        let sAccept = nfaNodeMap.NewNfaNode([], Some code)
        CompileRegexp regexp sAccept 

    let trs = List.map (fun clause -> (Alphabet_Epsilon, sTrans clause)) clauses
    let nfaStartNode = nfaNodeMap.NewNfaNode(trs, None)
    nfaStartNode, nfaNodeMap

type NfaNodeIdSetBuilder = HashSet<int>
type NfaNodeIdSet = int array

let CreateDfaState (builder : NfaNodeIdSetBuilder) : NfaNodeIdSet =
    let ary = Array.zeroCreate<int> builder.Count
    let mutable ofs = 0
    for id in builder do
        ary.[ofs] <- id
        ofs <- ofs + 1
    Array.sortInPlace ary
    ary

type NodeSetSet = HashSet<NfaNodeIdSet>

let newDfaNodeId = 
    let i = ref 0 
    fun () -> let res = !i in incr i; res

let array_chooseFirst (f : 'a -> 'b option) (ary : 'a array) =
    let rec loop i =
        if i < ary.Length then
            match f ary.[i] with
            | Some y -> Some y
            | None -> loop (i + 1)
        else None
    loop 0

let NfaToDfa (nfaNodeMap:NfaNodeMap) nfaStartNode = 
    let rec EClosure1 (acc:NfaNodeIdSetBuilder) (n:NfaNode) = 
        if not (acc.Contains(n.Id)) then 
            acc.Add(n.Id) |> ignore;
            if n.Transitions.ContainsKey(Alphabet_Epsilon) then
                match n.Transitions.[Alphabet_Epsilon] with 
                | [] -> () // this Clause is an optimization - the list is normally empty
                | tr -> 
                    //printfn "n.Id = %A, #Epsilon = %d" n.Id tr.Length
                    tr |> List.iter (EClosure1 acc) 

    let EClosure (moves : list<int>) = 
        let acc = new NfaNodeIdSetBuilder(HashIdentity.Structural)
        for i in moves do
            EClosure1 acc nfaNodeMap.[i];
        CreateDfaState acc

    // Compute all the immediate one-step moves for a set of NFA states, as a dictionary
    // mapping inputs to destination lists
    let ComputeMoves (nset : NfaNodeIdSet) = 
        let moves = new MultiMap<_,_>()
        Array.iter (fun nodeId -> 
            for (KeyValue(inp,dests)) in nfaNodeMap.[nodeId].Transitions do
                if inp <> Alphabet_Epsilon then 
                    match dests with 
                    | [] -> ()  // this Clause is an optimization - the list is normally empty
                    | tr -> tr |> List.iter(fun dest -> AddToMultiMap moves inp dest.Id)) nset
        moves

    let acc = new NfaNodeIdSetBuilder(HashIdentity.Structural)
    EClosure1 acc nfaStartNode;
    let nfaSet0 = CreateDfaState acc

    let dfaNodes = ref (Map.empty<NfaNodeIdSet,DfaNode>)

    let GetDfaNode nfaSet = 
        if (!dfaNodes).ContainsKey(nfaSet) then 
            (!dfaNodes).[nfaSet]
        else 
            let dfaNode =
                { Id= newDfaNodeId(); 
                  Transitions = Dictionary();
                  Accepted = array_chooseFirst (fun nid -> nfaNodeMap.[nid].Accepted) nfaSet }
            //Printf.printfn "id = %d" dfaNode.Id;

            dfaNodes := (!dfaNodes).Add(nfaSet, dfaNode); 
            dfaNode
            
    let workList = ref [nfaSet0]
    let doneSet = ref Set.empty

    //let count = ref 0 
    let rec Loop () = 
        match !workList with 
        | [] -> ()
        | nfaSet ::t -> 
            workList := t;
            if (!doneSet).Contains(nfaSet) then 
                Loop () 
            else
                let moves = ComputeMoves nfaSet
                for (KeyValue(inp,movesForInput)) in moves do
                    assert (inp <> Alphabet_Epsilon);
                    let moveSet = EClosure movesForInput;
                    if moveSet.Length <> 0 then 
                        //incr count
                        let dfaNode = GetDfaNode nfaSet
                        dfaNode.Transitions.[inp] <- GetDfaNode moveSet
                        (* Printf.printf "%d (%s) : %s --> %d (%s)\n" dfaNode.Id dfaNode.Name (match inp with EncodeChar c -> String.make 1 c | LEof -> "eof") moveSetDfaNode.Id moveSetDfaNode.Name;*)
                        workList := moveSet :: !workList;

                doneSet := (!doneSet).Add(nfaSet);


                Loop()
    Loop();
    //Printf.printfn "count = %d" !count;
    let ruleStartNode = GetDfaNode nfaSet0
    let ruleNodes = 
        (!dfaNodes) 
        |> Seq.map (fun kvp -> kvp.Value) 
        |> Seq.toList
        |> List.sortBy (fun s -> s.Id)
    ruleStartNode,ruleNodes

let GetAlphabets (lex_defs : lex_def list) =
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
        | Macro _ -> ()

    for lex_def in lex_defs do
        match lex_def with
        | Macro_def (_, re) -> loop re
        | Rules_def rules ->
            for _, _, clauses in rules do
                for re, _ in clauses do
                    loop re
    accu

let Compile (defs : lex_def list) =
    let alphabets = GetAlphabets defs
    let mutable macros = Map<string, regexp>([("eof", Inp (Alphabet (Alphabet_Eof)))])
    let accu = List()
    for def in defs do
        match def with
        | Macro_def (name, regexp) -> macros <- macros.Add(name, regexp)
        | Rules_def rules ->
            let perRuleData = List<_>()
            let dfaNodes = List<_>()
            for (name, args, clauses) in rules do
                let nfa, nfaNodeMap = LexerStateToNfa alphabets macros clauses
                let ruleStartNode, ruleNodes = NfaToDfa nfaNodeMap nfa
                perRuleData.Add((name, args, ruleStartNode))
                dfaNodes.Add(ruleNodes)
            accu.Add((perRuleData.ToArray(), dfaNodes.ToArray()))
    accu.ToArray()
