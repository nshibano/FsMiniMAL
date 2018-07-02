// This is re-implementation of Format module of OCaml.
module FsMiniMAL.Printer

open System
open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions

open Types
open Unify
open Value
open Typechk
open Printf
open System.Collections.Immutable

let create_tvar_assoc_table () = 
    let dict = Dictionary<type_var, string>(Misc.PhysicalEqualityComparer)
    (fun tv ->
        match dict.TryGetValue(tv) with
        | true, name -> name
        | false, _ ->
            let name = 
                let n = dict.Count / 26
                let c = dict.Count % 26
                if n > 0
                then System.Char.ConvertFromUtf32(c + 97) + string n
                else System.Char.ConvertFromUtf32(c + 97)
            dict.Add(tv, name)
            name)

let print_list p sep = 
    function 
    | [] -> ()
    | hd :: tl -> 
        p hd
        List.iter (fun a -> sep(); p a) tl
    
type Element = 
    | Etext of string // print text
    | Ebreak of Break // print n spaces or newline
    | Esection of Section // print elements in specifield layout (Flow or Vertical) with indentation

and Break = //
    { spaces : int // number of spaces to print when decided not to break hare
      mutable size : int // number of characters which will be printed without newline after this break when decided to not break here
    }

and Section = 
    { kind : SectionKind
      offset : int
      elements : List<Element>
      mutable size : int // number of characters when printed as single line
    }

    static member Create(kind, indent) = 
        { kind = kind
          offset = indent
          elements = List()
          size = 0 }

    member this.Add(x) = this.elements.Add(x)
    member this.AddBreak(n) = this.Add(Ebreak { spaces = n; size = 0 })
    member this.AddSpace() = this.AddBreak(1)
    member this.AddText(s) = this.Add(Etext s)

and SectionKind =
    | Flow // single line, or newline and then single line, or newline and then flow layout
    | Vertical // single line, or newline and then single line, or newline and then vertical layout

let escaped_char c =
    match c with
    | '\n' -> @"\n"
    | '\t' -> @"\t"
    | '\b' -> @"\b"
    | '\r' -> @"\r"
    | '\\' -> @"\\"
    | '"'  -> @"\"""
    | _ ->
        if System.Char.IsControl c
        then sprintf "\\%03d" (int c)
        else System.String(c, 1)

exception InvalidValue

let seq_of_mallist mallist =
    seq {
        let mutable x = mallist
        while (match x with
               | Vblock (1, _, _) -> true
               | Vint (0, _) -> false
               | _ -> raise InvalidValue) do
            match x with
            | Vblock (1, [| hd; tl |], _) ->
                yield hd
                x <- tl
            | _ -> raise InvalidValue }
 
type value_loop_runtime =
    { tyenv : tyenv
      mutable char_counter : int
      limit : int }

let elem_of_str (rt : value_loop_runtime)  (s : string) =
    rt.char_counter <- rt.char_counter + s.Length
    Etext s

let rec value_loop (rt : value_loop_runtime) (path : ImmutableHashSet<value>) (prio : int) (ty : type_expr) (value : value) : Element =
    match repr ty, value with
    | Tarrow _, _ -> elem_of_str rt "<fun>"
    | Ttuple [], _ -> elem_of_str rt "()"
    | Tconstr(type_id.INT, []), Vint (i, _) ->
        let s = i.ToString()
        if 0 < prio && s.[0] = '-' then
            elem_of_str rt ("(" + s + ")")
        else
            elem_of_str rt s
    | Tconstr(type_id.CHAR, []), Vint(i, _) when int Char.MinValue <= i && i <= int Char.MaxValue ->
        elem_of_str rt ("'" + escaped_char (char i) + "'")
    | Tconstr(type_id.FLOAT, []), Vfloat (x, _) ->
        let s = string_of_float x
        if 0 < prio && s.[0] = '-' then
            elem_of_str rt ("(" + s + ")")
        else
            elem_of_str rt s
    | Tconstr (type_id.STRING, []), Vstring (s, _) ->
        if 40 < s.Length then
            let sb = StringBuilder()
            let limit = 40
            for i = 0 to limit - 1 do
                let ec = escaped_char s.[i]
                sb.Add(ec)
            elem_of_str rt (sprintf "<string len=%d \"%s\"...>" s.Length (sb.ToString()))
        else
            let sb = StringBuilder()
            sb.Add('"')
            for i = 0 to s.Length - 1 do
                let ec = escaped_char s.[i]
                sb.Add(ec)
            sb.Add('"')
            elem_of_str rt (sb.ToString())
    | _ when path.Contains(value) ->
            elem_of_str rt "..."        
    | Ttuple l, _ ->
        list_loop rt (path.Add(value)) "(" ")" (Seq.zip l (getfields value))
    | Tconstr(type_id.ARRAY, [a]), Varray ary ->
        let items =
            match ary with
            | { count = count; storage = storage } -> seq { for i = 0 to count - 1 do yield storage.[i] }
        list_loop rt (path.Add(value)) "[|" "|]" (Seq.map (fun v -> (a, v)) items)
    | Tconstr(type_id.LIST, [a]), _ ->
        let items = 
            seq {
                let mutable x = value
                let mutable path = path
                while (match x with
                        | Vblock (1, _, _) -> true
                        | Vint (0, _) -> false
                        | _ -> raise InvalidValue) do
                    match x with
                    | Vblock (1, [| hd; tl |], _) ->
                        path <- path.Add(x)
                        yield (path, hd)
                        x <- tl
                    | _ -> raise InvalidValue }
        box_loop rt "[" "]" items (fun (path, v) -> value_loop rt path 0 a v)
    | Tconstr(type_id.EXN, _), _ ->
        let tag = gettag value
        let fields = getfields value
        let name, info = rt.tyenv.exn_constructors.[tag]
        if fields.Length <> info.ci_args.Length then raise InvalidValue

        if fields.Length = 0 then
            elem_of_str rt name
        else
            let name, info = rt.tyenv.exn_constructors.[tag]
            let accu1 = List()
            if prio > 0 then accu1.Add(elem_of_str rt "(")
            let accu2 = List()
            accu2.Add(elem_of_str rt name)
            accu2.Add(Ebreak { spaces = 1; size = 0 })
            let sl = []
            let tyl' = []
            let box3 =
                match info.ci_args with
                | [ ty_arg ] -> value_loop rt (path.Add(value)) 1 ty_arg fields.[0]
                | args ->
                    list_loop rt (path.Add(value)) "(" ")" (Seq.zip args fields)
            accu2.Add(box3)
            let box2 = Esection { kind = Flow; offset = 0; elements = accu2; size = 0 }
            accu1.Add(box2)
            if prio > 0 then accu1.Add(elem_of_str rt ")")
            let box1 = Esection { kind = Flow; offset = 0; elements = accu1; size = 0 }
            box1
    | Tconstr(id, tyl), _ ->
        match rt.tyenv.types_of_id.TryFind id with
        | None -> elem_of_str rt "<unknown type>"
        | Some info ->
            let sl = List.zip info.ti_params tyl
            match info.ti_kind with
            | Kbasic -> elem_of_str rt "<abstract>"           
            | Kabbrev ty -> value_loop rt path prio (subst sl ty) value
            | Kvariant casel ->
                match value with
                | Vint (i, _) ->
                    let tag = i
                    let case = List.find (fun (_, tag', _) -> tag = tag') casel
                    let name, _, _ = case
                    elem_of_str rt name
                | Vblock (tag, fields, _) ->
                    let case = List.find (fun (_, tag', _) -> tag = tag') casel
                    let name, _, tyl' = case
                    let accu1 = List()
                    if prio > 0 then accu1.Add(elem_of_str rt "(")
                    let accu2 = List()
                    accu2.Add(elem_of_str rt name)
                    accu2.Add(Ebreak { spaces = 1; size = 0 })
                    let box3 =
                        (match tyl' with
                        | [ ty' ] -> value_loop rt (path.Add(value)) 1 (subst sl ty') fields.[0]
                        | _ -> list_loop rt (path.Add(value)) "(" ")" (Seq.zip (Seq.map (subst sl) tyl') fields))
                    accu2.Add(box3)
                    let box2 = Esection { kind = Flow; offset = 0; elements = accu2; size = -1 }
                    accu1.Add(box2)
                    if prio > 0 then accu1.Add(elem_of_str rt ")")
                    let box1 = Esection { kind = Flow; offset = 0; elements = accu1; size = -1 }
                    box1
                | _ -> elem_of_str rt "<invalid value>"
            | Krecord l ->
                match value with
                | Vblock (_, fields, _) ->
                    let items = Seq.zip l fields
                    let path = path.Add(value)
                    let p ((name : string, ty_gen, _ : access), value) =
                        let accu2 = Section.Create(Flow, 0)
                        accu2.Add(elem_of_str rt (name + " ="))
                        accu2.Add(Ebreak { spaces = 1; size = 0 })
                        accu2.Add(value_loop rt path 0 (subst sl ty_gen) value)
                        Esection accu2
                    box_loop rt "{" "}" items p
                | _ -> elem_of_str rt "<invalid value>"
    | _ -> raise InvalidValue

and box_loop<'a> (rt : value_loop_runtime) (lp : string) (rp : string) (items :  'a seq) (p : 'a -> Element) : Element =
    let accu = Section.Create(Flow, lp.Length)
    accu.Add(elem_of_str rt lp)

    let mutable first = true
    let comma() =
        if not first then
            accu.Add(elem_of_str rt ",")
            accu.Add(Ebreak { spaces = 1; size = 0 });
        first <- false

    let enum = items.GetEnumerator()
    while
        (match enum.MoveNext(), rt.char_counter < rt.limit with
            | true, true ->
                comma()
                accu.Add(p enum.Current)
                true
            | true, false ->
                comma()
                accu.Add(elem_of_str rt "...")
                false
            | false, _ -> false) do ()

    accu.Add(elem_of_str rt rp)
    Esection accu

and list_loop (rt : value_loop_runtime) (path : ImmutableHashSet<value>) lp rp (items : (type_expr * value) seq) : Element =
    box_loop rt lp rp items (fun (ty, v) -> value_loop rt path 0 ty v)

let element_of_value (tyenv : tyenv) ty value =
    try
        value_loop { tyenv = tyenv; char_counter = 0; limit = 1000} (ImmutableHashSet.Create<value>(Misc.PhysicalEqualityComparer)) 0 ty value
    with InvalidValue ->
        Etext "<invalid value>"

let parenthesize elem =
    let accu = Section.Create(Flow, 1)
    accu.Add(Etext "(")
    accu.Add(elem)
    accu.Add(Etext ")")
    Esection accu

let element_of_type_expr (tyenv : tyenv) name_of_var is_scheme prio ty =
    
    let rec loop top prio ty =
        match repr ty with
        | Tvar tv ->
            let prefix = 
                if tv.level <> generic_level && is_scheme
                then "'_"
                else "'"
            Etext (prefix + name_of_var tv)
        | Tarrow(name, ty1, ty2) ->
            let accu = Section.Create(Vertical, 0)
            if name <> "" && top then
                accu.AddText(name + ":")
            accu.Add(loop top 1 ty1)
            accu.Add(Etext " ->")
            accu.Add(Ebreak { spaces = 1; size = -1 })
            accu.Add(loop top 0 ty2)
            let elem = Esection accu
            if prio > 0 then
                parenthesize elem
            else
                elem
        | Ttuple [] -> Etext "unit"
        | Ttuple l ->
            let accu = Section.Create(Flow, 0)
            let star() =
                accu.Add(Etext " *")
                accu.Add(Ebreak { spaces = 1; size = 0 })
            print_list (fun ty -> accu.Add(loop false 2 ty)) star l
            let elem = Esection accu
            if prio > 1 then
                parenthesize elem
            else
                elem
        | Tconstr(type_id.EXN, []) -> Etext "exn"
        | Tconstr(id, []) ->
            match tyenv.types_of_id.TryFind id with
            | Some ty -> Etext ty.ti_name
            | None -> dontcare()
        | Tconstr(id, ([ ty ])) ->
            match tyenv.types_of_id.TryFind id with
            | Some ti ->
                let accu = Section.Create(Vertical, 0) 
                accu.Add(loop false 2 ty)
                accu.Add(Ebreak { spaces = 1; size = 0 })
                accu.Add(Etext ti.ti_name)
                Esection accu
            | None -> dontcare()
        | Tconstr(id, l) ->
            match tyenv.types_of_id.TryFind id with
            | Some ti ->
                let accu1 = Section.Create(Vertical, 0)
                let accu2 = Section.Create(Flow, 1)
                accu2.Add(Etext "(")
                let comma() = 
                    accu2.Add(Etext ",")
                    accu2.Add(Ebreak { spaces = 1; size = 0 })
                print_list (fun ty -> accu2.Add(loop false 0 ty)) comma l
                accu2.Add(Etext ")")
                accu1.Add(Esection accu2)
                accu1.Add(Ebreak { spaces = 1; size = 0 })
                accu1.Add(Etext ti.ti_name)
                Esection accu1
            | None -> dontcare()
    loop true prio ty

let element_of_scheme (tyenv : tyenv) ty =
    let name_of_var = create_tvar_assoc_table()
    element_of_type_expr tyenv name_of_var true 0 ty

let element_of_type (tyenv : tyenv) name_of_var ty =
    element_of_type_expr tyenv name_of_var false 0 ty

let update_sizes (elem : Element) =

    let rec loop (sect : Section) =
        sect.size <- 0
        let mutable latest_brk = { spaces = 0; size = 0 } // dummy

        for elem in sect.elements do
            match elem with
            | Etext s -> 
                let size = String.length s
                latest_brk.size <- latest_brk.size + size
                sect.size <- sect.size + size
            | Ebreak brk ->
                latest_brk <- brk
                let size = brk.spaces
                brk.size <- size
                sect.size <- sect.size + size
            | Esection subsect ->
                loop subsect
                let size = subsect.size
                latest_brk.size <- latest_brk.size + size
                sect.size <- sect.size + size
    
    let dummy_section = { kind = Flow; offset = 0; elements = List([|elem|]); size = 0 }   
    loop dummy_section

let string_of_elem cols elem =
    let buf = StringBuilder()
    let mutable col = 0

    let spaces n =
        buf.Add(' ', n)
        col <- col + n
    
    let rec loop indent vertical =
        function
        | Etext s ->
            buf.Add(s)
            col <- col + s.Length
        | Ebreak brk ->
            if vertical || cols - col < brk.size
            then
                buf.Add("\r\n")
                col <- 0
                spaces indent
            else spaces brk.spaces
        | Esection box ->
            let vertical = box.kind = Vertical && cols - col < box.size
            let new_indent = col + box.offset
            for elem in box.elements do
                loop new_indent vertical elem
    
    loop 0 false elem
    buf.ToString()

let print_value_without_type define cols ty value =
    let accu = Section.Create(Flow, 1)
    accu.Add(element_of_value define ty value)
    let elem = Esection accu
    update_sizes elem
    string_of_elem cols elem

let print_value define cols ty value =
    let accu = Section.Create(Flow, 1)
    accu.Add(Etext "- : ")
    accu.Add(element_of_scheme define ty)
    accu.Add(Etext " =")
    accu.Add(Ebreak { spaces = 1; size = -1 })
    accu.Add(element_of_value define ty value)
    let elem = Esection accu
    update_sizes elem
    string_of_elem cols elem

let print_definition (define : tyenv) cols name (info : value_info) value =
    let accu = Section.Create(Flow, 1)
    accu.Add(Etext (match info.vi_access with access.Mutable -> "var " | access.Immutable -> "val "))
    accu.Add(Etext name)
    accu.Add(Etext " :")
    accu.AddSpace()
    accu.Add(element_of_scheme define info.vi_type)
    accu.Add(Etext " =")
    accu.AddSpace()
    let bare_value =
        match info.vi_access, value with
        | Immutable, _ -> value
        | Mutable, Vvar r -> !r
        | _ -> dontcare()
    accu.Add(element_of_value define info.vi_type bare_value)

    let elem = Esection accu
    update_sizes elem
    string_of_elem cols elem

let string_of_kind lang kind upper =
    match lang with
    | En ->
        let s =
            match kind with
            | Expression -> "Expression"
            | Pattern -> "Pattern"
            | Variable -> "Variable"
            | Type -> "Type"
            | Constructor -> "Constructor"
            | Label -> "Label"
            | Record_expression -> "Record expression"
            | Function_name -> "Function name"
            | Type_parameter -> "Type parameter"
            | Variable_name -> "Variable name"
            | Function_definition -> "Function definition"
            | Variable_definition -> "Variable definition"
            | Type_definition -> "Type definition"
            | Type_name -> "Type name"
            | Exception_name -> "Exception name"
        if upper then s
        else
            let ary = s.ToCharArray()
            ary.[0] <- Char.ToLowerInvariant ary.[0]
            String(ary)
    | Ja ->
        match kind with
        | Expression -> "式"
        | Pattern -> "パターン"
        | Variable -> "変数"
        | Type -> "型"
        | Constructor -> "コンストラクタ"
        | Label -> "ラベル"
        | Record_expression -> "レコード式"
        | Function_name -> "関数名"
        | Type_parameter -> "型パラメータ"
        | Variable_name -> "変数名"
        | Function_definition -> "関数定義"
        | Variable_definition -> "変数定義"
        | Type_definition -> "型定義"
        | Type_name -> "型名"
        | Exception_name -> "例外名"

let print_typechk_error lang cols desc =
    match lang with
    | En ->
        match desc with
        | Type_mismatch (tyenv, kind, ty1, ty2) ->
            let name_of_var = create_tvar_assoc_table()
            let accu = Section.Create(Flow, 2)
            accu.AddText (sprintf "%s has type" (string_of_kind lang kind true))
            accu.AddSpace()
            accu.Add(element_of_type tyenv name_of_var ty1)
            accu.AddSpace()
            accu.AddText "where"
            accu.AddSpace()
            accu.Add(element_of_type tyenv name_of_var ty2)
            accu.AddSpace()
            accu.AddText "was expected"
    
            let elem = Esection accu
            update_sizes elem
            string_of_elem cols elem
        | Multiple_occurence (kind, name, defkind) -> sprintf "%s %s occurs multiply in %s" (string_of_kind lang kind true) name (string_of_kind lang defkind false)
        | Constructor_undefined name -> sprintf "Variant %s is not defined" name
        | Constructor_requires_argument name -> sprintf "Variant %s requires argument" name
        | Constructor_takes_no_argument name -> sprintf "Variant %s takes no argument" name
        | Constructor_used_with_wrong_number_of_arguments (name, n, m) -> sprintf "Variant %s takes %d argument(s) but used with %d argument(s)." name n m
        | Label_undefined name -> sprintf "Undefined label %s" name
        | Label_undefined_for_type (tyenv, name, ty) -> sprintf "Label %s is undefined for type %s" name (string_of_elem cols (element_of_type tyenv (create_tvar_assoc_table()) ty))
        | Unbound_identifier name -> sprintf "Unbound identifier %s" name
        | Binding_names_are_inconsistent -> "Types of bindings are inconsistent"
        | Binding_types_are_inconsistent -> "Names of bindings are inconsistent"
        | Unbound_type_variable name -> sprintf "Unbound type variable %s" name
        | Undefined_type_constructor name -> sprintf "Undefined type constructor %s" name
        | Wrong_arity_for_type name -> sprintf "Wrong arity for type %s" name
        | Must_start_with_lowercase kind -> sprintf "%s must start with lowercase." (string_of_kind lang kind true)
        | Must_start_with_uppercase kind -> sprintf "%s must start with uppercase." (string_of_kind lang kind true)
        | Type_definition_contains_immediate_cyclic_type_abbreviation -> "Type definition contains immediate cyclic type abbreviation"
        | Integer_literal_overflow -> "Integer literal overflow"
        | Some_labels_are_missing -> "Some labels are missing"
        | Multiple_arguments_to_constructor_must_be_tupled -> "Multiple arguments to constructor must be tupled"
        | This_expression_is_not_a_function -> "This expression is not a function"
        | Too_many_arguments_for_this_function -> "Too many arguments for this function"
        | Cannot_use_this_command_inside_an_expression -> "Cannot use this command inside an expression"
        | Cannot_use_when_clause_in_try_construct -> "Cannot use when clause in try construct"
        | Invalid_printf_format -> "Invalid printf format"
        | Not_mutable (kind, name) -> sprintf "%s %s is not mutable" (string_of_kind lang kind true) name
        | Invalid_identifier -> "Invalid identifier"
        | This_expression_is_not_a_record -> "This expression is not a record"

    | Ja ->
        match desc with
        | Type_mismatch (tyenv, kind, ty1, ty2) ->
            let name_of_var = create_tvar_assoc_table()
            let accu = Section.Create(Flow, 2)
            accu.AddText (sprintf "この%sは" (string_of_kind lang kind true))
            accu.AddSpace()
            accu.Add(element_of_type tyenv name_of_var ty1)
            accu.AddSpace()
            accu.AddText "型ですが"
            accu.AddSpace()
            accu.Add(element_of_type tyenv name_of_var ty2)
            accu.AddSpace()
            accu.AddText "型である必要があります"
    
            let elem = Esection accu
            update_sizes elem
            string_of_elem cols elem
        | Multiple_occurence (kind, name, defkind) -> sprintf "%s %s が%s中で複数回使われています" (string_of_kind lang kind true) name (string_of_kind lang defkind false)
        | Constructor_undefined name -> sprintf "コンストラクタ %s は未定義です" name
        | Constructor_requires_argument name -> sprintf "コンストラクタ %s は引数が必要ですが、引数なしで使われています" name
        | Constructor_takes_no_argument name -> sprintf "コンストラクタ %s は引数を取りませんが、引数とともに使われています" name
        | Constructor_used_with_wrong_number_of_arguments (name, n, m) -> sprintf "コンストラクタ %s は%d個の引数を取りますが%d個の引数と共に使われています" name n m
        | Label_undefined name -> sprintf "ラベル名 %s は未定義です" name
        | Label_undefined_for_type (tyenv, name, ty) -> sprintf "Label %s is undefined for type %s" name (string_of_elem cols (element_of_type tyenv (create_tvar_assoc_table()) ty))
        | Unbound_identifier name -> sprintf "変数 %s は未定義です" name
        | Binding_names_are_inconsistent -> "束縛変数の名前が一致しません"
        | Binding_types_are_inconsistent -> "束縛変数の型が一致しません"
        | Unbound_type_variable name -> sprintf "束縛されていない型変数 %s が使われています" name
        | Undefined_type_constructor name -> sprintf "定義されていない型構築子 %s が使われています" name
        | Wrong_arity_for_type name -> sprintf "多相型 %s が間違った数の引数とともに使われています" name
        | Must_start_with_lowercase kind -> sprintf "%sは小文字で始まる必要があります" (string_of_kind lang kind true)
        | Must_start_with_uppercase kind -> sprintf "%sは大文字で始まる必要があります" (string_of_kind lang kind true)
        | Type_definition_contains_immediate_cyclic_type_abbreviation -> "型定義が直接に再帰的な型略称を含んでいます"
        | Integer_literal_overflow -> "整数リテラルの値が表現可能な範囲を超えています"
        | Some_labels_are_missing -> "いくつかのラベルについて値が指定されていません"
        | Multiple_arguments_to_constructor_must_be_tupled -> "コンストラクタへの複数の引数はタプルとして与える必要があります"
        | This_expression_is_not_a_function -> "この式は関数ではありません"
        | Too_many_arguments_for_this_function -> "関数に与える引数の数が多すぎます"
        | Cannot_use_this_command_inside_an_expression -> "式の内部ではこのコマンドを使用できません"
        | Cannot_use_when_clause_in_try_construct -> "try構文ではwhen節を使用できません"
        | Invalid_printf_format -> "無効な printf フォーマット文字列です"
        | Not_mutable (kind, name) -> sprintf "%s %s は変更可能ではありません" (string_of_kind lang kind true) name
        | Invalid_identifier -> "識別子が妥当ではありません"
        | This_expression_is_not_a_record -> "この式はレコードではありません"