[<AutoOpen>]
module FsMiniMAL.Misc

open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Text
open System.Text.RegularExpressions
open FsMiniMAL.Lexing

type FsMiniMAL.Lexing.LexBuffer<'T> with
    member lexbuf.Range = (lexbuf.StartPos, lexbuf.EndPos)
    member lexbuf.NewLine() = lexbuf.EndPos <- lexbuf.EndPos.NextLine

type System.Text.StringBuilder with
    member sb.Add(c : char) = sb.Append(c) |> ignore
    member sb.Add(c : char, n : int) = sb.Append(c, n) |> ignore
    member sb.Add(s : string) = sb.Append(s) |> ignore

type dirflag = 
    | Upto
    | Downto

type access = 
    | Mutable
    | Immutable

exception DontCareException
let dontcare () =
    raise DontCareException

let split_last l = 
    match List.rev l with
    | last :: rl -> List.rev rl, last
    | [] -> dontcare()

let rec do_list3 f l1 l2 l3 = 
    match l1, l2, l3 with
    | [], [], [] -> ()
    | a :: l1, b :: l2, c :: l3 -> 
        f a b c |> ignore
        do_list3 f l1 l2 l3
    | _ -> dontcare()

let rec assoc x = function
    | (a, b) :: _ when a = x -> b
    | _ :: tl -> assoc x tl
    | [] -> dontcare()

let rec tryAssoc x = function
    | (a, b) :: _ when a = x -> Some b
    | _ :: tl -> tryAssoc x tl
    | [] -> None

let rec mem_assoc x = function
    | (a, b) :: _ when a = x -> true
    | _ :: tl -> mem_assoc x tl
    | [] -> false

let rec remove_assoc x =
    function
    | (k, _) :: tl when k = x -> tl
    | kv :: tl -> kv :: (remove_assoc x tl)
    | [] -> []

let rec assqo x l =
    match l with
    | (a, b) :: t ->
        if LanguagePrimitives.PhysicalEquality a x 
        then Some b 
        else assqo x t
    | [] -> None

/// raises InvalidOperatonException when not found
let find_next_capacity_exn maxlen needed =
    if needed = 0 then 0
    elif needed <= maxlen && needed <= (1 <<< 30) then
        let mutable n = 1
        while n < needed do
            n <- 2 * n
        min maxlen n
    else raise (InvalidOperationException())

/// raises InvalidOperatonException when impossible
let array_ensure_capacity_exn<'T> (maxlen : int) (needed : int) (ary : 'T array) =
    if ary.Length < needed then
        let next = find_next_capacity_exn maxlen needed // exn
        let new_ary = Array.zeroCreate<'T> next
        Array.blit ary 0 new_ary 0 ary.Length
        new_ary
    else ary

let rec list_removefirst_exn pred =
    function
    | [] -> raise (KeyNotFoundException())
    | hd :: tl ->
        if pred hd
        then tl
        else hd :: list_removefirst_exn pred tl

let list_foldi f init l =
    let rec loop accu i =
        function
        | [] -> accu
        | hd :: tl -> loop (f accu i hd) (i + 1) tl
    loop init 0 l

let list_mapFold f init l =
    let rec loop accu =
        function
        | [] -> [], accu
        | x :: tl ->
            let y, accu = f accu x
            let ys, accu = loop accu tl
            (y :: ys), accu
    loop init l

let rec list_last =
    function
    | [] -> raise (KeyNotFoundException())
    | x :: [] -> x
    | hd :: tl -> list_last tl

let re_float_looks_like_int = Regex(@"\A\-?[0-9]+\Z")

let string_of_float x =
    if System.Double.IsNaN x then "nan"
    elif System.Double.IsPositiveInfinity x then "infinity"
    elif System.Double.IsNegativeInfinity x then "-infinity"
    else
        let s =
            let s = x.ToString("g")
            if Double.Parse(s) = x then s
            else x.ToString("g17")
        if re_float_looks_like_int.IsMatch(s) then
            s + ".0"
        else s

let PhysicalEqualityComparer =
    { new IEqualityComparer<'T> with
        member x.Equals(a, b) = LanguagePrimitives.PhysicalEquality a b
        member x.GetHashCode(a) = LanguagePrimitives.PhysicalHash a }

[<Struct>]
type MultiStrMap<'T> =
    | MultiStrMap of ImmutableDictionary<string, 'T list>

    static member Empty = MultiStrMap ImmutableDictionary<string, 'T list>.Empty
    
    member this.Item
        with get name =
            let l = match this with MultiStrMap storage -> storage.[name] // KeyNotFoundException
            List.head l
    
    member this.TryFind name =
        match this with
        | MultiStrMap storage ->
            match storage.TryGetValue(name) with
            | true, l -> Some (List.head l)
            | false, _ -> None

    member this.FindAll name =
        match this with
        | MultiStrMap storage ->
            match storage.TryGetValue(name) with
            | true, l -> l
            | false, _ -> []

    member this.Add(name, value : 'T) =
        match this with
        | MultiStrMap storage -> 
            match storage.TryGetValue(name) with
            | true, l -> MultiStrMap (storage.SetItem(name, value :: l))
            | false, _ -> MultiStrMap (storage.SetItem(name, [value]))

    member this.Remove(name : string, pred : 'T -> bool) =
        match this with
        | MultiStrMap storage ->
            let l = storage.[name] // KeyNotFoundException
            let l = list_removefirst_exn pred l // KeyNotFoundException
            if List.length l <> 0
            then MultiStrMap (storage.SetItem(name, l))
            else MultiStrMap (storage.Remove(name))
