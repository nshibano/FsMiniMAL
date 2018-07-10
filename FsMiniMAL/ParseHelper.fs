module FsMiniMAL.ParseHelper

open System.Collections.Generic
open FsMiniMAL.Parsing
open FsMiniMAL.Lexing

open Syntax

let get_loc (ps : IParseState) =
    let st, ed = ps.ResultRange
    let src = (ps.ParserLocalStore.["LexBuffer"] :?> LexBuffer<char>).BufferLocalStore.["src"] :?> string
    { src = src; st = st; ed = ed }

let get_term_loc (ps : IParseState) (i : int) =
    let st, ed = ps.InputRange i
    let src = (ps.ParserLocalStore.["LexBuffer"] :?> LexBuffer<char>).BufferLocalStore.["src"] :?> string
    { src = null; st = st; ed = ed }

let make_typ (ps : IParseState) desc = 
    { st_desc = desc
      st_loc = get_loc ps }

let make_pat (ps : IParseState) desc = 
    { sp_desc = desc
      sp_loc = get_loc ps }

let make_cmd (ps : IParseState) desc = 
    { sc_desc = desc
      sc_loc = get_loc ps }

let make_expr (ps : IParseState) desc = 
    { se_desc = desc
      se_loc = get_loc ps }

let make_typedef (ps : IParseState) prms name kind = 
    { sd_name = name
      sd_params = prms
      sd_kind = kind
      sd_loc = get_loc ps
      sd_nameloc =  get_term_loc ps 2 }

let make_ident (ps : IParseState) s = 
    { se_desc = SEid s
      se_loc = get_loc ps }

let make_string (ps : IParseState) s = make_expr ps (SEstring s)
let make_unop (ps : IParseState) s e = make_expr ps (SEapply(make_ident ps s, [ e ]))
let make_binop (ps : IParseState) s e1 e2 = make_expr ps (SEapply(make_ident ps s, [ e1; e2 ]))
let make_ternop (ps : IParseState) s e1 e2 e3 = make_expr ps (SEapply(make_ident ps s, [ e1; e2; e3 ]))
let make_pat_string (ps : IParseState) (s : string) = make_pat ps (SPstring s)
let make_cons_pat (ps : IParseState) a l = make_pat ps (SPapply ("::", make_pat ps (SPtuple [ a; l ])))

// "100" -> "-100"
// "-100" -> "100"
let make_minus (s : string) = 
    if s.[0] = '-' then s.Substring(1)
    else "-" + s

let make_minus_expr (ps : IParseState) op e = 
    match op, e with
    | "-", { se_desc = SEint i } -> make_expr ps (SEint(make_minus i))
    | _ -> 
        make_unop ps (match op with
                      | "-" -> "~"
                      | "-." -> "~."
                      | _ -> dontcare ()) e


let mark_as_typename (ps : IParseState) i =
    if not (ps.ParserLocalStore.ContainsKey("typenames")) then
        ps.ParserLocalStore.["typenames"] <- new List<Position * Position>()
    let accu = ps.ParserLocalStore.["typenames"] :?> List<Position * Position>
    accu.Add(ps.InputRange i)

let type_expr_of_type_star_list parseState l =
    match List.rev l with [ty] -> ty | l -> make_typ parseState (STtuple l)
