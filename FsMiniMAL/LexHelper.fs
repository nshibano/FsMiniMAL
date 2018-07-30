module FsMiniMAL.LexHelper

open System
open System.Numerics
open FsMiniMAL.Lexing
open Parser
open System.Collections.Generic
open System.Text.RegularExpressions

type lexical_error_desc =
  | Unterminated_string
  | Unterminated_comment
  | Illegal_character
  | Invalid_char_literal

exception Lexical_error of lexical_error_desc

let lexeme_string (lexbuf : LexBuffer<char>) = String(lexbuf.Lexeme)

let ident_or_keyword : LexBuffer<char> -> token =
    let d = Dictionary<string, token>()
    d.Add("and", AND)
    d.Add("as", AS)
    d.Add("begin", BEGIN)
    d.Add("case", CASE)
    d.Add("catch", CATCH)
    d.Add("do", DO)
    d.Add("downto", DOWNTO)
    d.Add("else", ELSE)
    d.Add("end", END)
    d.Add("exception", EXCEPTION)
    d.Add("fn", FN)
    d.Add("for", FOR)
    d.Add("fun", FUN)
    d.Add("funct" , FUNCT)
    d.Add("hide", HIDE)
    d.Add("hideval", HIDEVAL)
    d.Add("if", IF)
    d.Add("infinity", FLOAT infinity)
    d.Add("mutable", MUTABLE)
    d.Add("nan", FLOAT nan)
    d.Add("of", OF)
    d.Add("then", THEN)
    d.Add("to", TO)
    d.Add("try", TRY)
    d.Add("type", TYPE)
    d.Add("val", VAL)
    d.Add("var", VAR)
    d.Add("when", WHEN)
    d.Add("while", WHILE)
    d.Add("with", WITH)
    (fun (lexbuf : LexBuffer<char>) ->
        let s = lexeme_string lexbuf
        match d.TryGetValue(s) with
        | true, x -> x
        | false, _ -> IDENT s)

///To translate escape sequences
let char_for_backslash = function
  | 'n' -> '\010'
  | 't' -> '\009'
  | 'b' -> '\008'
  | 'r' -> '\013'
  | c   -> c

let char_for_dec3_code (lexbuf : LexBuffer<char>) =
    let code = Int32.Parse(String([| lexbuf.LexemeChar 1; lexbuf.LexemeChar 2; lexbuf.LexemeChar 3 |]))
    if 255 < code then raise (Lexical_error Invalid_char_literal)
    Char.ConvertFromUtf32(code).[0]

let char_for_hex4_code (lexbuf : LexBuffer<char>) =
    let code = Int32.Parse(String([| lexbuf.LexemeChar 2; lexbuf.LexemeChar 3; lexbuf.LexemeChar 4; lexbuf.LexemeChar 5 |]), Globalization.NumberStyles.HexNumber)
    Char.ConvertFromUtf32(code).[0]

let mark_as_comments (lexbuf : LexBuffer<char>) (st : Position) (ed : Position) =
    let accu =
        match lexbuf.BufferLocalStore.TryGetValue("comments") with
        | true, x -> x :?> List<Position * Position>
        | false, _ ->
            let accu = List<Position * Position>()
            lexbuf.BufferLocalStore.["comments"] <- accu
            accu
    accu.Add(st, ed)
