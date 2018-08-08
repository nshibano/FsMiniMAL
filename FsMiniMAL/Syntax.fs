module FsMiniMAL.Syntax

open System.Numerics
open FsMiniMAL.Lexing

type location = { src : string; st : Position; ed : Position }

type type_expr = 
    { st_desc : type_desc
      st_loc : location }

and type_desc = 
    | STvar of string
    | STarrow of type_expr * type_expr
    | STtuple of type_expr list
    | STconstr of string * type_expr list

type typedef = 
    { sd_name : string
      sd_params : string list
      sd_kind : type_kind
      sd_loc : location }

and type_kind = 
    | SKabbrev of type_expr
    | SKvariant of (string * type_expr list) list
    | SKrecord of (string * type_expr * access) list

type pattern = 
    { mutable sp_desc : pattern_desc
      sp_loc : location }

and pattern_desc =
    | SPid of string
    | SPint of string
    | SPfloat of float
    | SPchar of char
    | SPstring of string
    | SPtuple of pattern list
    | SParray of pattern list
    | SPas of pattern * string
    | SPany
    | SPtype of pattern * type_expr
    | SPor of pattern * pattern
    // before typecheck only
    | SPapply of string * pattern
    | SPrecord of (string * pattern) list
    // after typecheck only
    | SPblock of int * pattern list

type regexp = 
    | Alt of regexp list
    | Seq of regexp list
    | Inp of input
    | Star of regexp
    | Macro of string

and input =
    | Alphabet of int
    | Any 
    | NotCharSet of Set<int>

let Alphabet_Epsilon = -1
let Alphabet_Eof = -2
let Alphabet_Others = -3

type expression = 
    { mutable se_desc : expression_desc
      se_loc : location }

and expression_desc = 
    | SEid of string
    | SEint of string
    | SEfloat of float
    | SEchar of char
    | SEtuple of expression list
    | SEarray of expression list
    | SEstring of string
    | SEapply of expression * expression list
    | SEfn of pattern list * expression
    | SEbegin of command list
    | SEcase of expression * (pattern * expression option * expression) list
    | SEtry of expression * (pattern * expression option * expression) list // In try expression, when clause is not supported. But parser recognize it for better error reporting.
    | SEifthenelse of expression * expression * expression option
    | SEset of string * expression
    | SEfor of string * expression * dirflag * expression * expression
    | SEwhile of expression * expression
    | SEtype of expression * type_expr
    // before typecheck only
    | SErecord of orig : expression option * fields : (string * expression) list
    | SEgetfield of expression * string
    | SEsetfield of expression * string * expression
    // after typecheck only
    | SEurecord of (int * access * expression) list * expression option
    | SEugetfield of expression * int
    | SEusetfield of expression * int * expression
    | SEconstr of int * expression list
    | SEformat of PrintfFormat.PrintfCommand list

and command = 
    { sc_desc : command_desc
      sc_loc : location }

and command_desc = 
    | SCexpr of expression
    | SCval of (pattern * expression) list
    | SCfun of (string * expression) list // The expression for this case is always SEfn
    | SCvar of (string * expression) list
    | SCtype of typedef list
    | SChide of string
    | SCremove of string
    | SCexn of string * type_expr list
    | SClex of lex_def list

and lex_def =
    | Macro_def of string * regexp
    | Rules_def of (string * string list * (regexp * expression) list) list

let describe_location (loc : location) =
    let {src = input; st = st; ed = ed} = loc
    let filename = Some (st.FileName)
    let sb = System.Text.StringBuilder()
    let pf fmt = Printf.bprintf sb fmt

    match filename with
        | Some filename -> pf "In \"%s\", line " filename
        | None -> pf "Line "

    if not (st.AbsoluteOffset < input.Length) then
        pf "%d, unexpected EOF" (st.Line + 1)
    elif st.Line = ed.Line then
        // when range is in one line, display char range
        pf "%d, char %d-%d: \"%s\"" (st.Line + 1) (st.AbsoluteOffset - st.StartOfLineAbsoluteOffset + 1) (ed.AbsoluteOffset - ed.StartOfLineAbsoluteOffset) (input.Substring(st.AbsoluteOffset, (ed.AbsoluteOffset - st.AbsoluteOffset)))
    else             
        let is_nonwhitespace c = not (System.Char.IsWhiteSpace(c))

        let end_of_first_token =
            let mutable i = st.AbsoluteOffset
            while is_nonwhitespace input.[i] && (i + 1) < ed.AbsoluteOffset do
                i <- i + 1
            i
             
        let start_of_last_token =
            let mutable i = ed.AbsoluteOffset
            while is_nonwhitespace input.[i - 1] && st.AbsoluteOffset <= i do
                i <- i - 1
            i

        let first_token = input.Substring(st.AbsoluteOffset, end_of_first_token - st.AbsoluteOffset)
        let last_token = input.Substring(start_of_last_token, ed.AbsoluteOffset - start_of_last_token)
        
        pf "%d, char %d to line %d, char %d: \"%s ... %s\"" (st.Line + 1) (st.AbsoluteOffset - st.StartOfLineAbsoluteOffset + 1) (ed.Line + 1) (ed.AbsoluteOffset - ed.StartOfLineAbsoluteOffset + 1) first_token last_token
        
    sb.ToString()