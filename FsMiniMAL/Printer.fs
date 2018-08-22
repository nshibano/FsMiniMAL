// This is re-implementation of Format module of OCaml.
module FsMiniMAL.Printer

open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Text
open Printf

open Types
open Unify
open Typechk
open Value
open Message

type lang =
    | En
    | Ja

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
    
type Node = 
    | Text of StringBuilder
    | Section of Section

and Section = 
    { Kind : SectionKind
      Indent : int
      Items : List<Node>
      mutable Size : int }

    static member Create(kind, indent) = 
        { Kind = kind
          Indent = indent
          Items = List()
          Size = 0 }

    member this.Add(s : string) = this.Items.Add(Text (StringBuilder(s)))
    member this.Add(e : Node) = this.Items.Add(e)
    member this.Weld(s : string) =
        if this.Items.Count = 0 then
            this.Items.Add(Text (StringBuilder s))
        else
            match this.Items.[this.Items.Count - 1] with
            | Text sb -> sb.Add(s)
            | Section sub -> sub.Weld(s)
    member this.PreWeld(s : string) =
        if this.Items.Count = 0 then
            this.Items.Add(Text (StringBuilder s))
        else
            match this.Items.[0] with
            | Text sb -> sb.Insert(0, s) |> ignore
            | Section sub -> sub.PreWeld(s)

and SectionKind =
    | Flow
    | Vertical

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
 
type value_loop_runtime =
    { tyenv : tyenv
      mutable char_counter : int
      limit : int }

let textNode (rt : value_loop_runtime)  (s : string) =
    rt.char_counter <- rt.char_counter + s.Length
    Text (StringBuilder(s))

let parenthesize (node : Node) =
    let section = Section.Create(Flow, 1)
    section.Add(node)
    section.PreWeld("(")
    section.Weld(")")
    Section section

let textInvalid = "<invalid>"

let rec value_loop (rt : value_loop_runtime) (path : ImmutableHashSet<value>) (level : int) (ty : type_expr) (value : value) : Node =
    match repr ty, value with
    | Tarrow _, _ -> textNode rt "<fun>"
    | Ttuple [], _ -> textNode rt "()"
    | Tconstr(type_id.INT, []), Vint (i, _) ->
        let s = i.ToString()
        let s =
            if 0 < level && s.[0] = '-' then
                "(" + s + ")"
            else
                s
        textNode rt s
    | Tconstr(type_id.CHAR, []), Vint(i, _) when int Char.MinValue <= i && i <= int Char.MaxValue ->
        textNode rt ("'" + escaped_char (char i) + "'")
    | Tconstr(type_id.FLOAT, []), Vfloat (x, _) ->
        let s = string_of_float x
        let s =
            if 0 < level && s.[0] = '-' then
                "(" + s + ")"
            else
                s
        textNode rt s
    | Tconstr (type_id.STRING, []), Vstring (s, _) ->
        let limit = 40
        if limit < s.Length then
            let sb = StringBuilder()
            for i = 0 to limit - 1 do
                let ec = escaped_char s.[i]
                sb.Add(ec)
            textNode rt (sprintf "<string len=%d \"%s\"...>" s.Length (sb.ToString()))
        else
            let sb = StringBuilder()
            sb.Add('"')
            for i = 0 to s.Length - 1 do
                let ec = escaped_char s.[i]
                sb.Add(ec)
            sb.Add('"')
            textNode rt (sb.ToString())
    | _ when path.Contains(value) ->
            textNode rt "..."
    | Ttuple l, _ ->
        list_loop rt (path.Add(value)) "(" ")" (Seq.zip l (get_fields value))
    | Tconstr(type_id.ARRAY, [a]), Varray ary ->
        let items = seq { for i = 0 to ary.count - 1 do yield (a, ary.storage.[i]) }
        list_loop rt (path.Add(value)) "[|" "|]" items
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
                        yield value_loop rt path 0 a hd
                        x <- tl
                    | _ -> raise InvalidValue }
        seq_loop rt "[" "]" items
    | Tconstr(type_id.EXN, _), _ ->
        let tag = get_tag value
        let fields = get_fields value
        let name, info = rt.tyenv.exn_constructors.[tag]
        if fields.Length <> info.ci_args.Length then textNode rt textInvalid
        else
            if fields.Length = 0 then
                textNode rt name
            else
                let name, info = rt.tyenv.exn_constructors.[tag]
                let section = Section.Create(Flow, 0)
                section.Add(textNode rt name)
                let fields =
                    match info.ci_args with
                    | [ ty_arg ] -> value_loop rt (path.Add(value)) 1 ty_arg fields.[0]
                    | args -> list_loop rt (path.Add(value)) "(" ")" (Seq.zip args fields)
                section.Add(fields)
                let node = Section section
                if level > 0 then parenthesize node else node
    | Tconstr(id, tyl), _ ->
        match rt.tyenv.types_of_id.TryFind id with
        | None -> textNode rt textInvalid
        | Some info ->
            let sl = List.zip info.ti_params tyl
            match info.ti_kind with
            | Kbasic -> textNode rt "<abstr>"           
            | Kabbrev ty -> value_loop rt path level (subst sl ty) value
            | Kvariant casel ->
                match value with
                | Vint (tag, _) ->
                    let name, _, _ = List.find (fun (_, tag', _) -> tag = tag') casel
                    textNode rt name
                | Vblock (tag, fields, _) ->
                    let name, _, tyl' = List.find (fun (_, tag', _) -> tag = tag') casel
                    let section = Section.Create(Flow, 0)
                    section.Add(textNode rt name)
                    let fields =
                        (match tyl' with
                        | [ ty' ] -> value_loop rt (path.Add(value)) 1 (subst sl ty') fields.[0]
                        | _ -> list_loop rt (path.Add(value)) "(" ")" (Seq.zip (Seq.map (subst sl) tyl') fields))
                    section.Add(fields)
                    let node = Section section
                    if level > 0 then parenthesize node else node
                | _ -> textNode rt textInvalid
            | Krecord l ->
                match value with
                | Vblock (_, fields, _) ->
                    let path = path.Add(value)
                    let items =
                        Seq.zip l fields
                        |> Seq.map (fun ((name : string, ty_gen, _ : access), value) ->
                            let section = Section.Create(Flow, 0)
                            section.Add(textNode rt (name + " ="))
                            section.Add(value_loop rt path 0 (subst sl ty_gen) value)
                            Section section)
                    seq_loop rt "{" "}" items
                | _ -> textNode rt textInvalid
    | _ -> raise InvalidValue

and seq_loop (rt : value_loop_runtime) (lp : string) (rp : string) (items : Node seq) : Node =
    let section = Section.Create(Flow, lp.Length)

    let mutable first = true

    let comma() =
        if not first then
            section.Weld ","
        first <- false

    let enum = items.GetEnumerator()
    while
        (match enum.MoveNext(), rt.char_counter < rt.limit with
            | true, true ->
                comma()
                section.Add(enum.Current)
                true
            | true, false ->
                comma()
                section.Add(textNode rt "...")
                false
            | false, _ -> false) do ()
    
    section.PreWeld(lp)
    section.Weld rp
    Section section

and list_loop (rt : value_loop_runtime) (path : ImmutableHashSet<value>) lp rp (items : (type_expr * value) seq) : Node =
    seq_loop rt lp rp (Seq.map (fun (ty, v) -> value_loop rt path 0 ty v) items)

let node_of_value (tyenv : tyenv) ty value =
    try
        value_loop { tyenv = tyenv; char_counter = 0; limit = 1000} (ImmutableHashSet.Create<value>(Misc.PhysicalEqualityComparer)) 0 ty value
    with InvalidValue ->
        Text (StringBuilder(textInvalid))

let node_of_type_expr (tyenv : tyenv) name_of_var is_scheme prio ty =
    
    let rec loop top prio ty =
        match repr ty with
        | Tvar tv ->
            let prefix = 
                if tv.level <> generic_level && is_scheme
                then "'_"
                else "'"
            Text (StringBuilder(prefix + name_of_var tv))
        | Tarrow _ ->
            let rec flatten ty =
                match ty with
                | Tarrow (name, ty1, ty2) -> (name, ty1) :: flatten ty2
                | _ -> [("", ty)]
            let tyl = Array.ofList (flatten ty)
            let sxn = Section.Create(Flow, 0)
            for i = 0 to tyl.Length - 2 do
                let ty_sxn = Section.Create(Flow, 0)
                let name_i, ty_i = tyl.[i]
                ty_sxn.Add(loop top 1 ty_i)
                if name_i <> "" && top then ty_sxn.PreWeld(name_i + ":")
                ty_sxn.Weld(" ->")
                sxn.Add(Section ty_sxn)
            let _, ty_final = tyl.[tyl.Length - 1]
            sxn.Add(loop top 0 ty_final)
            let node = Section sxn
            if prio > 0 then
                parenthesize node
            else node
        | Ttuple [] -> Text (StringBuilder "unit")
        | Ttuple l ->
            let accu = Section.Create(Flow, 0)
            let star() =
                accu.Weld(" *")
            print_list (fun ty -> accu.Items.Add(loop false 2 ty)) star l
            let elem = Section accu
            if prio > 1 then
                parenthesize elem
            else elem
        | Tconstr(type_id.EXN, []) -> Text (StringBuilder "exn")
        | Tconstr(id, []) ->
            match tyenv.types_of_id.TryFind id with
            | Some ty -> Text (StringBuilder ty.ti_name)
            | None -> dontcare()
        | Tconstr(id, ([ ty ])) ->
            match tyenv.types_of_id.TryFind id with
            | Some ti ->
                let s = Section.Create(Flow, 0) 
                s.Add(loop false 2 ty)
                s.Add(Text (StringBuilder ti.ti_name))
                Section s
            | None -> dontcare()
        | Tconstr(id, l) ->
            match tyenv.types_of_id.TryFind id with
            | Some ti ->
                let section1 = Section.Create(Flow, 0)
                let comma() = 
                    section1.Weld(",")
                print_list (fun ty -> section1.Items.Add(loop false 0 ty)) comma l
                
                let section2 = parenthesize (Section section1)

                let section3 = Section.Create(Flow, 0)
                section3.Add(section2)
                section3.Add(ti.ti_name)

                Section section3
            | None -> dontcare()
    loop true prio ty

let node_of_scheme (tyenv : tyenv) ty =
    let name_of_var = create_tvar_assoc_table()
    node_of_type_expr tyenv name_of_var true 0 ty

let node_of_type (tyenv : tyenv) name_of_var ty =
    node_of_type_expr tyenv name_of_var false 0 ty

let update_sizes (elem : Node) =

    let rec loop (sect : Section) =
        sect.Size <- 0

        for elem in sect.Items do
            match elem with
            | Text s -> 
                sect.Size <- sect.Size + s.Length
            | Section sub ->
                loop sub
                sect.Size <- sect.Size + sub.Size
        
        sect.Size <- sect.Size + sect.Items.Count - 1
    
    match elem with
    | Section s -> loop s
    | Text _ -> ()

let string_of_node cols node =
    let buf = List<struct (char * int16)>()

    let mutable col = 0

    let add_spaces (level : int16) (n : int) =
        for i = 0 to n - 1 do
            buf.Add(struct (' ', ~~~level))
        col <- col + n
    
    let add_string (level : int16) (s : string) =
        for c in s do
            buf.Add(struct (c, level))
        col <- col + s.Length

    let rec loop level indent vertical =
        function
        | Text sb ->
            add_string level (sb.ToString())
        | Section box ->
            let vertical = box.Kind = Vertical && cols - col < box.Size
            let indent = indent + box.Indent
            for i = 0 to box.Items.Count - 1 do
                if i <> 0 then
                    if vertical || cols - col < (1 + match box.Items.[i] with Text sb -> sb.Length | Section s -> s.Size)
                    then
                        add_string level "\r\n"
                        col <- 0
                        add_spaces (level + 1s) indent
                    else add_spaces (level + 1s) 1
                loop (level + 1s) indent vertical box.Items.[i]
    
    loop 0s 0 false node

    let buf = buf.ToArray()
    let s = String(Array.map (fun struct (c, _) -> c) buf)
    let colors = Array.map (fun struct (_, color) -> color) buf
    (s, colors)

let print_value_without_type_colored define cols ty value =
    let e = node_of_value define ty value
    update_sizes e
    string_of_node cols e

let print_value_without_type define cols ty value = fst (print_value_without_type_colored define cols ty value)

let print_value_colored define cols ty value =
    let s1 = Section.Create(Flow, 0)
    s1.Add("- :")
    s1.Add(node_of_scheme define ty)
    s1.Weld(" =")
    let s2 = Section.Create(Flow, 1)
    s2.Add(Section s1)
    s2.Add(node_of_value define ty value)
    let node = Section s2
    update_sizes node
    string_of_node cols node

let print_value define cols ty value = fst (print_value_colored define cols ty value)

let print_definition (define : tyenv) cols name (info : value_info) value =
    let sxn1 = Section.Create(Flow, 0)
    let valvar = match info.vi_access with Immutable -> "val" | Mutable -> "var"
    sxn1.Add(sprintf "%s %s :" valvar name)
    sxn1.Add(node_of_scheme define info.vi_type)
    sxn1.Weld(" =")
    let sxn2 = Section.Create(Flow, 1)
    sxn2.Add(Section sxn1)
    let value =
        match info.vi_access, value with
        | Immutable, _ -> value
        | Mutable, Vvar r -> !r
        | _ -> dontcare()
    sxn2.Add(node_of_value define info.vi_type value)
    let node = Section sxn2
    update_sizes node
    fst (string_of_node cols node)

let string_of_kind lang kind upper =
    match lang with
    | En ->
        let s =
            match kind with
            | Expression -> "Expression"
            | Pattern -> "Pattern"
            | Variable -> "Variable"
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
        if upper then s
        else s.ToLowerInvariant()
    | Ja ->
        match kind with
        | Expression -> "式"
        | Pattern -> "パターン"
        | Variable -> "変数"
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

let print_typechk_error lang cols desc =
    match lang with
    | En ->
        match desc with
        | Type_mismatch (tyenv, kind, ty1, ty2) ->
            let name_of_var = create_tvar_assoc_table()
            let s = Section.Create(Vertical, 0)
            s.Add(sprintf "%s has type" (string_of_kind lang kind true))
            s.Add(node_of_type tyenv name_of_var ty1)
            s.Add "where"
            s.Add(node_of_type tyenv name_of_var ty2)
            s.Add "was expected."
            let node = Section s
            update_sizes node
            fst (string_of_node cols node)
        | Multiple_occurence (kind, name, defkind) -> sprintf "%s %s occurs multiply in %s." (string_of_kind lang kind true) name (string_of_kind lang defkind false)
        | Constructor_undefined name -> sprintf "Variant %s is not defined." name
        | Constructor_requires_argument name -> sprintf "Variant %s requires argument." name
        | Constructor_takes_no_argument name -> sprintf "Variant %s takes no argument." name
        | Constructor_used_with_wrong_number_of_arguments (name, n, m) -> sprintf "Variant %s takes %d argument(s) but used with %d argument(s)." name n m
        | Label_undefined name -> sprintf "Undefined label %s." name
        | Label_undefined_for_type (label, type_name) -> sprintf "Label %s is not defined in type %s." label type_name
        | Unbound_identifier name -> sprintf "Unbound identifier %s." name
        | Binding_names_are_inconsistent -> "Types of bindings are inconsistent."
        | Binding_types_are_inconsistent -> "Names of bindings are inconsistent."
        | Unbound_type_variable name -> sprintf "Unbound type variable %s." name
        | Undefined_type_constructor name -> sprintf "Undefined type constructor %s." name
        | Wrong_arity_for_type name -> sprintf "Wrong arity for type %s." name
        | Type_definition_contains_immediate_cyclic_type_abbreviation -> "Type definition contains immediate cyclic type abbreviation."
        | Integer_literal_overflow -> "Integer literal overflow."
        | Some_labels_are_missing -> "Some labels are missing."
        | Multiple_arguments_to_constructor_must_be_tupled -> "Multiple arguments to constructor must be tupled."
        | This_expression_is_not_a_function -> "This expression is not a function."
        | Too_many_arguments_for_this_function -> "Too many arguments for this function."
        | Cannot_use_this_command_inside_an_expression -> "Cannot use this command inside an expression."
        | Cannot_use_when_clause_in_try_construct -> "Cannot use when clause in try construct."
        | Invalid_printf_format -> "Invalid printf format."
        | Not_mutable (kind, name) -> sprintf "%s %s is not mutable." (string_of_kind lang kind true) name
        | Invalid_identifier -> "Invalid identifier."
        | Invalid_type_name -> "Invalid type name."
        | Invalid_label_name -> "Invalid label name."
        | Invalid_constructor_name -> "Invalid constructor name."
        | This_expression_is_not_a_record -> "This expression is not a record."
        | Partially_applied -> "Beware, this function is partially applied."
        | Useless_with_clause -> "All the fields are explicitly listed in this record: the 'with' clause is useless."
        | Already_abstract name -> sprintf "Type %s is already abstract." name
        | Basic_types_cannot_be_hidden -> "Basic types cannot be hidden."

    | Ja ->
        match desc with
        | Type_mismatch (tyenv, kind, ty1, ty2) ->
            let name_of_var = create_tvar_assoc_table()
            let s = Section.Create(Vertical, 0)
            s.Add (sprintf "この%sは" (string_of_kind lang kind true))
            s.Add(node_of_type tyenv name_of_var ty1)
            s.Add "型ですが"
            s.Add(node_of_type tyenv name_of_var ty2)
            s.Add "型である必要があります。"
            let node = Section s
            update_sizes node
            fst (string_of_node cols node)
        | Multiple_occurence (kind, name, defkind) -> sprintf "%s %s が%s中で複数回使われています。" (string_of_kind lang kind true) name (string_of_kind lang defkind false)
        | Constructor_undefined name -> sprintf "コンストラクタ %s は未定義です。" name
        | Constructor_requires_argument name -> sprintf "コンストラクタ %s は引数が必要ですが、引数なしで使われています。" name
        | Constructor_takes_no_argument name -> sprintf "コンストラクタ %s は引数を取りませんが、引数とともに使われています。" name
        | Constructor_used_with_wrong_number_of_arguments (name, n, m) -> sprintf "コンストラクタ %s は%d個の引数を取りますが%d個の引数と共に使われています。" name n m
        | Label_undefined name -> sprintf "ラベル名 %s は未定義です。" name
        | Label_undefined_for_type (label, type_name) -> sprintf "型 %s について、ラベル名 %s は定義されていません。" label type_name
        | Unbound_identifier name -> sprintf "変数 %s は未定義です。" name
        | Binding_names_are_inconsistent -> "束縛変数の名前が一致しません。"
        | Binding_types_are_inconsistent -> "束縛変数の型が一致しません。"
        | Unbound_type_variable name -> sprintf "束縛されていない型変数 %s が使われています。" name
        | Undefined_type_constructor name -> sprintf "定義されていない型構築子 %s が使われています。" name
        | Wrong_arity_for_type name -> sprintf "多相型 %s が間違った数の引数とともに使われています。" name
        | Type_definition_contains_immediate_cyclic_type_abbreviation -> "型定義が直接に再帰的な型略称を含んでいます。"
        | Integer_literal_overflow -> "整数リテラルの値が表現可能な範囲を超えています。"
        | Some_labels_are_missing -> "いくつかのラベルについて値が指定されていません。"
        | Multiple_arguments_to_constructor_must_be_tupled -> "コンストラクタへの複数の引数はタプルとして与える必要があります。"
        | This_expression_is_not_a_function -> "この式は関数ではありません。"
        | Too_many_arguments_for_this_function -> "関数に与える引数の数が多すぎます。"
        | Cannot_use_this_command_inside_an_expression -> "式の内部ではこのコマンドを使用できません。"
        | Cannot_use_when_clause_in_try_construct -> "try構文ではwhen節を使用できません。"
        | Invalid_printf_format -> "無効な printf フォーマット文字列です。"
        | Not_mutable (kind, name) -> sprintf "%s %s は変更可能ではありません。" (string_of_kind lang kind true) name
        | Invalid_identifier -> "識別子が非妥当です。"
        | Invalid_type_name -> "型名が非妥当です。"
        | Invalid_label_name -> "ラベル名が非妥当です。"
        | Invalid_constructor_name -> "コンストラクタ名が非妥当です。"
        | This_expression_is_not_a_record -> "この式はレコードではありません。"
        | Partially_applied -> "この式は部分適用されています。ご注意ください。"
        | Useless_with_clause -> "全てのフィールドが明示的に与えられているため、 with 節は不要です。"
        | Already_abstract name -> sprintf "型 %s は既に抽象型です。" name
        | Basic_types_cannot_be_hidden -> "基本型は隠蔽できません。"
    
let print_message lang cols (msg : Message) =
    match msg with
    | LexicalError (err, loc) -> sprintf "> %s\r\n  Lexical error (%A).\r\n" (Syntax.describe_location loc) err
    | SyntaxError loc ->  sprintf "> %s\r\n  Syntax error.\r\n" (Syntax.describe_location loc)
    | TypeError (err, loc) ->
        let sb = StringBuilder()
        bprintf sb "> %s\r\n" (Syntax.describe_location loc)
        bprintf sb "%s\r\n" (print_typechk_error lang cols err)
        sb.ToString()
    | EvaluationComplete (tyenv, value, ty)->
        print_value tyenv cols ty value + "\r\n"
    | NewValues (tyenv, new_values) ->
        let sb = new StringBuilder()
        for name, value, info in new_values do
            sb.Add (print_definition tyenv cols name info value)
            sb.Add("\r\n")
        sb.ToString()
    | TypeDefined names ->
        let sb = StringBuilder()
        List.iter (fun name -> bprintf sb "Type %s defined.\r\n" name) names
        sb.ToString()
    | ExceptionDefined name -> sprintf "Exception %s is defined.\r\n" name
    | TypeHidden name -> sprintf "Type %s is now abstract.\r\n" name
    | ValueRemoved name -> sprintf "Value %s has been removed.\r\n" name
    | UncaughtException (tyenv, exn_value) ->
        let buf = StringBuilder()
        buf.Add("UncaughtException: ")
        buf.Add(print_value_without_type tyenv cols ty_exn exn_value)
        buf.AppendLine() |> ignore
        buf.ToString()
        //stacktrace 10 buf
    | MALInsufficientMemory -> "Insufficient memory.\r\n"
    | MALStackOverflow -> "Stack overflow.\r\n"
    | EnvSizeLimit -> "Reached limit of environment size.\r\n"
