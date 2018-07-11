module FsMiniMAL.Typechk

open System
open System.Text.RegularExpressions
open System.Collections.Generic
open System.Collections.Immutable

open Syntax
open Types
open Unify

type kind =
    | Expression
    | Pattern
    | Variable
    | Type
    | Constructor
    | Label
    | Record_expression
    | Variable_name
    | Function_name
    | Type_parameter
    | Function_definition
    | Variable_definition
    | Type_definition
    | Type_name
    | Exception_name

type type_error_desc =
    | Type_mismatch of tyenv * kind * type_expr * type_expr
    | Multiple_occurence of kind : kind * name : string * definition_kind : kind
    | Constructor_undefined of string
    | Constructor_requires_argument of string
    | Constructor_takes_no_argument of string
    | Constructor_used_with_wrong_number_of_arguments of name : string * expected : int * given : int
    | Label_undefined of string
    | Label_undefined_for_type of tyenv : tyenv * label : string * ty : type_expr
    | Unbound_identifier of string
    | Binding_names_are_inconsistent
    | Binding_types_are_inconsistent
    | Unbound_type_variable of string
    | Wrong_arity_for_type of string
    | Undefined_type_constructor of string
    | Must_start_with_lowercase of kind
    | Must_start_with_uppercase of kind
    | Type_definition_contains_immediate_cyclic_type_abbreviation
    | Integer_literal_overflow
    | Some_labels_are_missing
    | Multiple_arguments_to_constructor_must_be_tupled
    | This_expression_is_not_a_function
    | Too_many_arguments_for_this_function
    | Cannot_use_this_command_inside_an_expression
    | Cannot_use_when_clause_in_try_construct
    | Invalid_printf_format
    | Invalid_identifier
    | Not_mutable of kind * string
    | This_expression_is_not_a_record

exception Type_error of type_error_desc * location
 
/// Throws Type_error if name list contains duplicated name.
let rec all_differ loc kind definition_kind names =
    let set = HashSet<string>()
    for name in names do
        if set.Contains name then
            raise (Type_error (Multiple_occurence (kind, name, definition_kind), loc))
        else set.Add name |> ignore

let generic_level = -1
let global_level = 1

let new_tvar level = Tvar { link = None; level = level; }

let re_constructor = Regex(@"\A[A-Z][A-Za-z0-9_']*\Z")
let is_constructor s =
    match s with
        | "true"
        | "false"
        | "::"
        | "[]" -> true
        | _ -> re_constructor.IsMatch(s)

let rec get_pattern_name (pat : Syntax.pattern) =
    match pat.sp_desc with
    | SPid s when s <> "$" && (not (is_constructor s)) -> s
    | SPtype (p, _) -> get_pattern_name p
    | _ -> ""

/// Unifies ty with 'a -> 'b where 'a and 'b are new type variable at current_level. Then returns ('a, 'b).
/// If impossible, raises Unify.
let filter_arrow tyenv current_level ty = 
    match repr ty with
    | Tarrow(_, ty1, ty2) -> ty1, ty2 // fast path
    | ty -> 
        let ty1 = new_tvar current_level
        let ty2 = new_tvar current_level
        unify tyenv ty (Tarrow ("", ty1, ty2))
        ty1, ty2

/// Unifies ty with 'a -> 'b ... -> 'result where 'a, 'b, ... are new type variable at current_level.
/// Then returns ['a, 'b, ..., 'result] where length of resultant list is n + 1.
/// If impossible, raises Unify.
let filter_arrow_n tyenv current_level n ty =
    let rec loop n ty =
        if n = 0 then [ty]
        else
            let ty1, ty2 = filter_arrow tyenv current_level ty
            ty1 :: (loop (n - 1) ty2)
    loop n ty

let is_tvar (ty : type_expr) =
    match repr ty with
    | Tvar _ -> true
    | _ -> false

let rec is_record (tyenv : tyenv) (ty : type_expr) =
    match repr ty with
    | Tconstr (id, _) ->
        match tyenv.types_of_id.TryFind(id) with
        | Some ti ->
            match ti.ti_kind with
            | Krecord _ -> Some id
            | Kabbrev _ ->
                match expand tyenv ty with
                | Some ty -> is_record tyenv ty
                | _ -> dontcare()
            | _ -> None
        | _ -> dontcare()
    | _ -> None

/// Creates Types.type_expr from Syntax.type_expr.
/// When unknown type var was found in Syntax.type_expr, throws error or assign new type var depending on is_typedef.
let rec type_expr tyenv is_typedef (type_vars : Dictionary<string, type_expr>) sty =
    match sty.st_desc with
    | STvar s ->
        match type_vars.TryGetValue s with
        | true, ty -> ty
        | false, _ ->
            if is_typedef then
                raise (Type_error (Unbound_type_variable s, sty.st_loc))
            let ty = new_tvar global_level
            type_vars.Add(s, ty)
            ty
    | STarrow (st1, st2) -> Tarrow ("", (type_expr tyenv is_typedef type_vars st1), (type_expr tyenv is_typedef type_vars st2))
    | STtuple stl -> Ttuple (List.map (type_expr tyenv is_typedef type_vars) stl)
    | STconstr (s, stl, _) ->
        match tyenv.types.TryFind s with
        | Some info ->
            if (List.length stl) <> (List.length info.ti_params) then
                raise (Type_error ((Wrong_arity_for_type s), sty.st_loc))
            subst (List.zip info.ti_params (List.map (type_expr tyenv is_typedef type_vars) stl)) info.ti_res
        | None -> raise (Type_error ((Undefined_type_constructor s), sty.st_loc))

/// Define new type from Syntax.typedef
let add_typedef tyenv loc dl =
    
    // Checks new type names are lowercase.
    for d in dl do
        if not (Char.IsLower(d.sd_name, 0)) then
            raise (Type_error (Must_start_with_lowercase Type_name, d.sd_loc))
    
    // Checks duplicate in new type names.
    all_differ loc kind.Type_name kind.Type_definition (List.map (fun td -> td.sd_name) dl)

    // Checks variant is uppercase and record label is lowercase.
    for d in dl do
        match d.sd_kind with
        | SKrecord fields ->
            for name, _, _ in fields do
                if not (Char.IsLower name.[0]) then
                    raise (Type_error (Must_start_with_lowercase Label, d.sd_loc))

        | SKvariant cases ->
            for name, _ in cases do
                if not (Char.IsUpper name.[0]) then
                    raise (Type_error (Must_start_with_uppercase Constructor, d.sd_loc))

        | _ -> ()
                
    // Checks duplicates in variant names.
    for d in dl do
        match d.sd_kind with
        | SKvariant cl ->
            let constructors = List.map fst cl
            all_differ d.sd_loc Constructor Type_definition constructors
        | _ -> ()
    
    // Checks duplicates in record labels.
    for d in dl do
        match d.sd_kind with
        | SKrecord fl ->
            let labels = List.map (fun (labels, _, _) -> labels) fl
            all_differ d.sd_loc Label Type_definition labels
        | _ -> ()
        
    // Checks duplicates in type var name.
    List.iter (fun td -> all_differ td.sd_loc kind.Type_parameter kind.Type_definition td.sd_params) dl

    // Checks there is no circular type abbreviation.
    let abbrev_defs = List.choose (function { Syntax.sd_kind = SKabbrev ty } as sd -> Some (sd, sd.sd_name, ty) | _ -> None) dl
    let abbrev_defs_map = Map.ofList (List.map (fun (_, name, ty) -> (name, ty)) abbrev_defs)
    let check_cyclic_abbrev (d : typedef) =
        let name, ty = match d.sd_kind with SKabbrev ty -> d.sd_name, ty | _ -> dontcare()
        let mutable visited = Set.ofArray [| name |]
        let rec visit (ty : Syntax.type_expr) =
            match ty.st_desc with
            | STvar _ -> ()
            | STarrow (ty1, ty2) -> visit ty1; visit ty2
            | STtuple l -> List.iter visit l
            | STconstr (name, args, _) ->
                if abbrev_defs_map.ContainsKey name then
                    if visited.Contains name then
                        raise (Type_error (Type_definition_contains_immediate_cyclic_type_abbreviation, loc))
                    else
                        visited <- Set.add name visited
                        visit abbrev_defs_map.[name]
                List.iter visit args
        visit ty
    List.iter (fun (def, _, _) -> check_cyclic_abbrev def) abbrev_defs

    // Create tyenv with dummy definitions.
    let dl, tyenv_with_dummy_defs = list_mapFold (fun tyenv td ->
        let id = type_id_new ()
        // Create type var instance for type parameters.
        let params' = List.map (fun _ -> { link = None; level = 0 }) td.sd_params
        // Set the dummy type to the global table.
        let ti = make_ti id td.sd_name params' Kbasic
        (td, id, ti), Types.add_type tyenv ti) tyenv dl

    /// Evaluate the type expressions syntax tree in environment with dummy types. 
    let dl =
        List.map (fun (td, id, ti_dummy) ->
            // Craete type information from syntax tree.
            // When type constructor is used in syntax tree, arity matching is checked.
            // For recursive type definitions, arity is checked using dummy type info.
            let type_vars = Dictionary<string, type_expr>()
            List.iter2 (fun name tv -> type_vars.Add(name, (Tvar tv))) td.sd_params ti_dummy.ti_params
            let kind = 
                match td.sd_kind with
                | SKabbrev sty -> Kabbrev (type_expr tyenv_with_dummy_defs true type_vars sty)
                | SKvariant cl -> Kvariant (List.mapi (fun i (s, stl) -> (s, i, (List.map (type_expr tyenv_with_dummy_defs true type_vars) stl))) cl)
                | SKrecord fl -> Krecord (List.map (fun (s, sty, access) -> (s, (type_expr tyenv_with_dummy_defs true type_vars sty), access)) fl)
            let ti = { ti_dummy with ti_kind = kind }
            (td, id, ti_dummy, ti)) dl
    
    // Create tyenv with real type information.
    List.fold (fun tyenv (_, _, _, ti) -> Types.add_type tyenv ti) tyenv dl

/// Copy the type expression. When generic level type var is found, replace it with newly created type var at current level.
let instanciate_scheme current_level ty =
    let vars = ref [] in
    let rec inst ty =
        match repr ty with
        | Tvar tv when tv.level = generic_level ->
            match assqo tv !vars with
            | Some ty' -> ty'
            | None ->
                let ty' = new_tvar current_level
                vars := (tv, ty') :: !vars
                ty'
        | ty -> map_type inst ty
    inst ty

/// Take constr_info, and copy the argument type expression and resultant type expression.
/// When type var is found, replace it with newly created type var at current level.
let instanciate_constr current_level info = 
    let s = List.map (fun tv -> (tv, new_tvar current_level)) info.ci_params
    let args = List.map (subst s) info.ci_args
    let res = subst s info.ci_res
    args, res

/// Take label_info, and copy the field type expression and resultant type expression.
/// When type var is found, replace it with newly created type var at current level.
let instanciate_label current_level info =
    let s = List.map (fun tv -> (tv, new_tvar current_level)) info.li_params
    let ty_field = subst s info.li_arg
    let ty_rec = subst s info.li_res
    ty_field, ty_rec

let instanciate_record tyenv current_level id_record =
    let info = tyenv.types_of_id.[id_record]
    let s = List.map (fun tv -> (tv, new_tvar current_level)) info.ti_params
    let record_fields = List.mapi (fun i (name, ty, access) -> (name, (i, subst s ty, access))) (match info.ti_kind with Krecord l -> l | _ -> dontcare())
    let ty_res = subst s info.ti_res
    record_fields, ty_res

/// Unify two types. If failed, throws type error for the pattern.
let unify_pat tyenv pat ty1 ty2 = 
    try unify tyenv ty1 ty2
    with Unify -> raise (Type_error (Type_mismatch (tyenv, Pattern, ty1, ty2), pat.sp_loc))

/// Unify two types. If failed, throws type error.
let unify_exp tyenv exp ty ty_expected =
    try unify tyenv ty ty_expected
    with Unify -> raise (Type_error (Type_mismatch (tyenv, Expression, ty, ty_expected), exp.se_loc))

/// From constructor name, picks type information of variant type.
/// If expected type is variant type and that type have definition for the used constructor name,
/// pick that type even if the constructor is shadowed.
let pick_constr (tyenv : tyenv) (ty_expected : type_expr) (name : string) =
    match tyenv.constructors.FindAll name with
    | [] -> None
    | constrs ->
        let ci_from_ty_expected =
            match repr ty_expected with
            | Tconstr (id, _) ->
                List.tryFind (function { ci_res = Tconstr (id', _) } -> id = id' | _ -> false) constrs
            | _ -> None
        match ci_from_ty_expected with
        | Some _ -> ci_from_ty_expected
        | None -> Some (List.head constrs)

let rec pattern tyenv (type_vars : Dictionary<string, type_expr>) (current_level : int) (ty_expected : type_expr) (pat : Syntax.pattern) =
    match pat.sp_desc with
    | SPid s ->
        if is_constructor s then
            match pick_constr tyenv ty_expected s with
            | None -> raise (Type_error(Constructor_undefined s, pat.sp_loc))
            | Some info ->
                // If no-argument constr is used with argument, throw type error.
                if not (List.isEmpty info.ci_args) then
                    raise (Type_error(Constructor_requires_argument s, pat.sp_loc))
                let (_, ty_res) = instanciate_constr current_level info
                pat.sp_desc <- SPblock (info.ci_tag, [])
                (ty_res, [])
        else
            // This is identifier, not variant.
            let ty = new_tvar current_level
            (ty, [ (s, { vi_type = ty; vi_access = access.Immutable; }) ])
    | SPas (p, ident) ->
        if System.Char.IsUpper(ident.[0]) then
            raise (Type_error(Must_start_with_lowercase Variable_name, pat.sp_loc))
        else
            let ty, bnds = pattern tyenv type_vars current_level ty_expected p
            let bnds = if mem_assoc ident bnds then remove_assoc ident bnds else bnds
            let bnds = (ident, { vi_type = ty; vi_access = access.Immutable; }) :: bnds
            (ty, bnds)
    | SPint _ -> ty_int, []
    | SPchar _ -> ty_char, []
    | SPfloat _ -> ty_float, []
    | SPstring _ -> ty_string, []
    | SPtuple l ->
        let tyl, bnds = pattern_list tyenv type_vars current_level pat.sp_loc l
        (Ttuple tyl, bnds)
    | SParray l ->
        let tyl, bnds = pattern_list tyenv type_vars current_level pat.sp_loc l
        // Item expressions in array pattern must be same. So unify them.
        let ty_accu = new_tvar current_level
        List.iter2 (fun pat ty -> unify_pat tyenv pat ty ty_accu) l tyl;
        ((Tconstr (type_id.ARRAY, [ ty_accu ])), bnds)
    | SPapply (s, arg) ->
        if not (is_constructor s) then
            raise (Type_error(Must_start_with_uppercase Constructor, pat.sp_loc))
        match pick_constr tyenv ty_expected s with
        | Some info ->
            // Create new type expression using constructor information.
            let ty_args, ty_res = instanciate_constr current_level info
            match ty_args, arg with
            | [], _ ->
                raise (Type_error(Constructor_takes_no_argument s, pat.sp_loc))
            | [ty_arg], _ ->
                // This variant takes one argument. Therefore if argument is syntactically tuple,
                // it is taking single argument in tuple type.
                let ty_pat, bnds = pattern tyenv type_vars current_level ty_arg arg
                unify_pat tyenv arg ty_pat ty_arg
                pat.sp_desc <- SPblock (info.ci_tag, [arg])
                (ty_res, bnds)
            | _, { sp_desc = SPtuple args } ->
                // This variant takes multiple argument, so the argument must be syntactically tuple.
                if List.length args = List.length ty_args then
                    let ty_pats, bnds = pattern_list tyenv type_vars current_level pat.sp_loc args
                    do_list3 (unify_pat tyenv) args ty_pats ty_args
                    pat.sp_desc <- SPblock (info.ci_tag, args)
                    (ty_res, bnds)
                else raise (Type_error (Constructor_used_with_wrong_number_of_arguments (s, List.length ty_args, List.length args), pat.sp_loc))
            | _ -> raise (Type_error (Constructor_used_with_wrong_number_of_arguments (s, List.length ty_args, 1), pat.sp_loc))
        | None -> raise (Type_error (Constructor_undefined s, pat.sp_loc))
    | SPblock _ -> dontcare()
    | SPrecord l ->
        // Try to find record type from ty_expected
        let id_record = is_record tyenv ty_expected

        // If record type is still unknown, decide based on firstly seen record label.
        let id_record =
            match id_record with
            | Some id -> id
            | None ->
                let first_lab = fst (List.head l)
                match tyenv.labels.TryFind first_lab with
                | Some info -> info.li_id
                | None -> raise (Type_error (Label_undefined first_lab, pat.sp_loc))
        
        let fields, ty_res = instanciate_record tyenv current_level id_record

        let used_fields =
            List.map (fun (lab, field_pat) ->
                match tryAssoc lab fields with
                | Some field -> field
                | None -> raise (Type_error (Label_undefined_for_type (tyenv, lab, ty_res), field_pat.sp_loc))) l

        // type argument expressions
        let ty_args, bnds = pattern_list tyenv type_vars current_level pat.sp_loc (List.map snd l)

        // unify record field type and argument type
        do_list3 (fun (_, pat) ty_arg (_, ty_field, _) -> unify_pat tyenv pat ty_arg ty_field) l ty_args used_fields

        let record_len = match tyenv.types_of_id.[id_record].ti_kind with | Krecord l -> List.length l | _ -> dontcare ()

        // translate record to untyped block pattern
        let ary = Array.create record_len { sp_desc = SPany; sp_loc = pat.sp_loc }
        List.iter2 (fun (_, pat) (i, _, _) -> ary.[i] <- pat) l used_fields
        pat.sp_desc <- SPblock (0, List.ofArray ary)
        (ty_res, bnds)
    | SPany -> (new_tvar current_level, [])
    | SPtype (pat, sty) ->
        let ty_res = type_expr tyenv false type_vars sty
        let ty_pat, bnds = pattern tyenv type_vars current_level ty_res pat
        unify_pat tyenv pat ty_pat ty_res
        (ty_res, bnds)
    | SPor (a, b) ->
        let ty_a, bnds_a = pattern tyenv type_vars current_level (ty_expected) a
        let ty_b, bnds_b = pattern tyenv type_vars current_level (ty_expected) b
        let sorted_names bnds = Array.sort (Array.map fst (Array.ofList bnds))
        if sorted_names bnds_a <> sorted_names bnds_b then
            raise (Type_error (Binding_names_are_inconsistent, pat.sp_loc))
        for name, vi1 in bnds_a do
            let vi2 = (Misc.assoc name bnds_b)
            try unify tyenv vi1.vi_type vi2.vi_type
            with Unify -> raise (Type_error (Binding_types_are_inconsistent, pat.sp_loc))
        unify_pat tyenv b ty_b ty_a
        (ty_a, bnds_a)
/// Type list of patterns. If there was duplicated name, throw type error.
and pattern_list tyenv (type_vars : Dictionary<string, type_expr>) current_level loc patl =
    let tyl, bndss = List.unzip (List.map (fun pat -> pattern tyenv type_vars current_level (new_tvar current_level) pat) patl)
    let bnds =
        List.foldBack (fun bnd bnds ->
            (List.iter (fun (s, _) ->
                if mem_assoc s bnds then
                    raise (Type_error ((Multiple_occurence (kind.Variable_name , s, kind.Pattern)), loc))) bnd;
            bnd @ bnds)) bndss []
    (tyl, bnds)

/// Returns true if all objects which will be created in evaluation of this expression are immutable and there is no side-effects to external objects.
let rec is_nonexpansive (e : Syntax.expression) =
    match e.se_desc with
    | SEid _ | SEint _ | SEchar _ | SEfloat _ | SEstring _ | SEformat _ | SEfn _ -> true
    | SEarray _ | SEapply _ | SEset _ | SEusetfield _ -> false
    | SEconstr (_, l) -> List.forall is_nonexpansive l
    | SEtuple l -> List.forall is_nonexpansive l
    | SEurecord (fields, orig) ->
        (match orig with None -> true | Some e -> is_nonexpansive e) &&
        List.forall (fun (_, access, e) -> access = Immutable && is_nonexpansive e) fields
    | SEbegin l -> List.forall cmd_nonexpansive l
    | SEcase (e, cases) ->
        is_nonexpansive e &&
        List.forall (fun (_, ew, e) -> (match ew with Some ew -> is_nonexpansive ew | None -> true) && is_nonexpansive e) cases
    | SEtry (e, cases) ->
        is_nonexpansive e &&
        List.forall (fun (_, _, e) -> is_nonexpansive e) cases
    | SEifthenelse (e1, e2, e3) ->
        is_nonexpansive e1 &&
        is_nonexpansive e2 &&
        (match e3 with Some e3 -> is_nonexpansive e3 | None -> true)
    | SEugetfield (e, _) -> is_nonexpansive e
    | SEfor (_, e1, _, e2, e3) -> is_nonexpansive e1 && is_nonexpansive e2 && is_nonexpansive e3
    | SEwhile (e1, e2) -> is_nonexpansive e1 && is_nonexpansive e2
    | SEtype (e, _) -> is_nonexpansive e
    | SErecord _ 
    | SEsetfield _ 
    | SEgetfield _ -> dontcare()

/// Returns true if all objects created in execution of commands are immutable.
and cmd_nonexpansive cmd =
    match cmd.sc_desc with
    | SCexpr e -> is_nonexpansive e
    | SCval l -> List.forall (fun (_, e) -> is_nonexpansive e) l
    | SCfun _ -> true
    | SCvar l -> List.forall (fun (_, e) -> is_nonexpansive e) l
    | SCtype _ | SChide _ | SChideval _ | SCexn _ -> dontcare()

/// Set genelic level to type vars with level > current_level.
let rec generalize current_level ty = 
    match repr ty with
    | Tvar tv -> 
        if tv.level > current_level then
            tv.level <- generic_level
    | ty -> do_type (generalize current_level) ty

/// Set current level to type vars with level > current level.
let rec make_nongen current_level ty = 
    match repr ty with
    | Tvar tv -> 
        if tv.level > current_level then
            tv.level <- current_level
    | ty -> do_type (make_nongen current_level) ty

let type_printf_cmds cmds ty_result = 
    let rec loop = 
        function 
        | PrintfFormat.PrintfCommand.Text _ :: t -> loop t
        | PrintfFormat.PrintfCommand.Spec { TypeChar = 's' } :: t -> Tarrow ("", ty_string, loop t)
        | PrintfFormat.PrintfCommand.Spec { TypeChar = ('d' | 'x' | 'X') } :: t -> Tarrow ("", ty_int, loop t)
        | PrintfFormat.PrintfCommand.Spec { TypeChar = ('f' | 'e' | 'E' | 'g' | 'G' | 'r') } :: t -> Tarrow ("", ty_float, loop t)
        | [] -> ty_result
        | _ -> raise PrintfFormat.InvalidFormatString
    loop cmds

let rec expression (ps : string -> unit) (tyenv : tyenv) (type_vars : Dictionary<string, type_expr>) (current_level : int) (ty_expected : type_expr option) (e : expression) =
    match e.se_desc with
    | SEid (("+" | "-" | "*" | "/" | "~-") as op) ->
        let ty_float_result, ty_int_result = if op = "~-" then ty_ff, ty_ii else ty_fff, ty_iii
        match ty_expected with
        | Some ty_expected when same_type tyenv ty_expected ty_float_result ->
            e.se_desc <- SEid (op + ".")
            ty_float_result
        | _ -> ty_int_result
    | SEid s when is_constructor s ->
        match tyenv.constructors.TryFind(s) with
        | Some info ->
            if not (List.isEmpty info.ci_args) then
                raise (Type_error(Constructor_requires_argument s, e.se_loc))
            let _, ty_res = instanciate_constr current_level info
            e.se_desc <- SEconstr (info.ci_tag, [])
            ty_res
        | None -> raise (Type_error (Constructor_undefined s, e.se_loc))
    | SEid s ->
        match tyenv.values.TryGetValue s with
        | true, info -> instanciate_scheme current_level info.vi_type
        | false, _ -> raise (Type_error (Unbound_identifier s, e.se_loc))
    | SEconstr _ -> dontcare()
    | SEint s ->
        try int s |> ignore
        with :? System.OverflowException -> raise (Type_error (Integer_literal_overflow, e.se_loc))
        ty_int
    | SEchar _ -> ty_char
    | SEfloat _ -> ty_float
    | SEtuple el ->
        let tyl_expected =
            match Option.map repr ty_expected with
            | Some (Ttuple tyl) when tyl.Length = el.Length -> List.map (fun ty -> Some ty) tyl
            | _ -> List.init el.Length (fun _ -> None)
        Ttuple (List.map2 (expression ps tyenv type_vars current_level) tyl_expected el)
    | SEarray el ->
        let ty_accu = new_tvar current_level
        List.iter (expression_expect ps tyenv type_vars current_level ty_accu) el
        Tconstr (type_id.ARRAY, [ ty_accu ])
    | SEstring s ->
        match Option.map repr ty_expected with
        | Some (Tconstr (type_id.FORMAT, _)) ->
            let cmds =
                try PrintfFormat.parse_fmt s
                with PrintfFormat.InvalidFormatString -> raise (Type_error (Invalid_printf_format, e.se_loc))
            e.se_desc <- SEformat cmds
            let ty_res = new_tvar current_level
            let ty_args = type_printf_cmds cmds ty_res
            Tconstr (type_id.FORMAT, [ty_args; ty_res])
        | _ -> ty_string
    | SErecord (orig, fields) ->

        // infer orig of { orig with ... }.
        let ty_orig =
            Option.bind (fun e ->
                let ty = expression ps tyenv type_vars current_level ty_expected e
                // if orig is available but is neither of record nor tvar, report type error
                if not ((is_record tyenv ty).IsSome || is_tvar ty) then
                    raise (Type_error (This_expression_is_not_a_record, e.se_loc))
                Some ty) orig
        
        // get record type id from orig if possible 
        let id_record = Option.bind (is_record tyenv) ty_orig

        // if record type id is still not found, and recoed type is given in ty_expected, use it.   
        let id_record =
            match id_record with
            | Some _ -> id_record
            | None -> Option.bind (is_record tyenv) ty_expected

        // if there is duplicate in labels, report type error
        all_differ e.se_loc kind.Label kind.Record_expression (List.map fst fields)
        
        // if record type is still not found, decide based on label name of firstly given field
        let id_record =
            match id_record with
            | Some id -> id
            | None ->
                let lab = fst (List.head fields)
                match tyenv.labels.TryFind(lab) with
                | Some info -> info.li_id
                | None -> raise (Type_error (Label_undefined lab, e.se_loc))

        // instanciate record type
        let record_fields, ty_res = instanciate_record tyenv current_level id_record
        
        // bind given firld expressions to record fields
        let fields =
            List.map (fun (lab, e) ->
                match tryAssoc lab record_fields with
                | Some (idx, ty, access) ->
                    (lab, idx, ty, access, e)
                | None -> raise (Type_error (Label_undefined lab, e.se_loc))) fields
        
        // this will not fail
        Option.iter (fun ty_orig -> unify tyenv ty_orig ty_res) ty_orig

        // tests for number of given fields
        match orig, List.length fields = List.length record_fields with
        | None, false ->
            raise (Type_error (Some_labels_are_missing, e.se_loc))
        | Some _, true ->
            let { st = st; ed = ed } = e.se_loc
            Printf.kprintf ps "> Char %d-%d : all the fields are explicitly listed in this record: the 'with' clause is useless.\r\n" st.AbsoluteOffset ed.AbsoluteOffset
        | _ -> ()

        // typecheck for field expressions
        List.iter (fun (_, _, ty_field, _, e) -> expression_expect ps tyenv type_vars current_level ty_field e) fields

        e.se_desc <- SEurecord ((List.map (fun (_, idx, _, access, e) -> (idx, access, e)) fields), orig)
        ty_res
    | SEurecord _ -> dontcare ()
    | SEapply ((({ se_desc = SEid s } as e1)), el) when is_constructor s ->
        match pick_constr tyenv (match ty_expected with Some ty -> ty | None -> new_tvar current_level) s with
        | None -> raise (Type_error (Constructor_undefined s, e1.se_loc))
        | Some info ->
            let ty_args, ty_res = instanciate_constr current_level info
            let e_args =
                match el with
                | [e] -> e
                | [] -> dontcare()
                | _ -> raise (Type_error (Multiple_arguments_to_constructor_must_be_tupled, e1.se_loc))
            match ty_args, e_args with
            | [], _ -> raise (Type_error(Constructor_takes_no_argument s, e1.se_loc))
            | [ty_arg], _ ->
                expression_expect ps tyenv type_vars current_level ty_arg e_args
                e.se_desc <- SEconstr (info.ci_tag, [e_args])
                ty_res
            | _, { se_desc = SEtuple el } ->
                if List.length el = List.length ty_args then
                    List.iter2 (expression_expect ps tyenv type_vars current_level) ty_args el
                    e.se_desc <- SEconstr (info.ci_tag, el)
                    ty_res
                else raise (Type_error(Constructor_used_with_wrong_number_of_arguments (s, ty_args.Length, el.Length), e1.se_loc))
            | _, _ -> raise (Type_error(Constructor_used_with_wrong_number_of_arguments (s, ty_args.Length, 1), e1.se_loc))
    | SEapply (({ se_desc = SEid (("+" | "-" | "*" | "/" | "~-") as op) } as e_op), el_args) when let op_arity = if op = "~-" then 1 else 2
                                                                                                 let el_args_len = el_args.Length
                                                                                                 op_arity - el_args_len >= 0 ->
        let op_arity = if op = "~-" then 1 else 2
        let el_args_len = el_args.Length
        let ty_float_res, ty_int_res =
            if op_arity - el_args_len = 0 then
                ty_float, ty_int
            else // = 1
                ty_ff, ty_ii
        match ty_expected with
        | Some ty_expected when same_type tyenv ty_expected ty_float_res ->
            List.iter (expression_expect ps tyenv type_vars current_level ty_float) el_args
            e_op.se_desc <- SEid (op + ".")            
            ty_float_res
        | _ ->
            let tyl_args = List.map (expression ps tyenv type_vars current_level None) el_args
            let mutable float_count = 0
            let mutable tvar_count = 0
            for ty in tyl_args do
                if same_type tyenv ty ty_float then
                    float_count <- float_count + 1
                elif is_tvar ty then
                    tvar_count <- tvar_count + 1
            if float_count > 0 && (float_count + tvar_count) = tyl_args.Length then
                List.iter (expression_expect ps tyenv type_vars current_level ty_float) el_args
                e_op.se_desc <- SEid (op + ".")
                ty_float_res
            else
                List.iter2 (fun e_arg ty_arg -> unify_exp tyenv e_arg ty_arg ty_int) el_args tyl_args
                ty_int_res
    | SEapply ({ se_desc = SEid ".[]"}, [e_arg0; e_arg1]) ->
        let ty_arg0 = expression ps tyenv type_vars current_level None e_arg0
        let ty_result =
            if same_type tyenv ty_arg0 ty_string then
                ty_char
            else
                let ty_item = new_tvar current_level
                let ty_array = Tconstr (type_id.ARRAY, [ty_item])
                unify_exp tyenv e_arg0 ty_arg0 ty_array
                ty_item
        expression_expect ps tyenv type_vars current_level ty_int e_arg1
        ty_result
    | SEapply ({ se_desc = SEid "^" } as e0, [e1; e2]) when same_type tyenv ty_string (expression ps tyenv type_vars current_level None e1) && same_type tyenv ty_string (expression ps tyenv type_vars current_level None e2) ->
            e0.se_desc <- SEid "^^"
            ty_string
    | SEapply (e1, el) ->
        let ty1 = expression ps tyenv type_vars current_level None e1
        try filter_arrow tyenv current_level ty1 |> ignore
        with Unify -> raise (Type_error (This_expression_is_not_a_function, e1.se_loc))
        let ty_args, ty_res =
            try split_last (filter_arrow_n tyenv current_level el.Length ty1)
            with Unify -> raise (Type_error (Too_many_arguments_for_this_function, e1.se_loc))
        List.iter2 (fun ty e -> expression_expect ps tyenv type_vars current_level ty e) ty_args el
        ty_res
    | SEfn (patl, e1) ->
        let ty_args_expected, ty_result_expected =
            match ty_expected with
            | Some ty ->
                try
                    let tyl = filter_arrow_n tyenv current_level patl.Length ty
                    let ty_args, ty_result = split_last tyl
                    Some ty_args, Some ty_result
                with Unify -> None, None
            | None -> None, None
        let loc = { (List.head patl).sp_loc with ed = (list_last patl).sp_loc.ed }
        let ty_args, new_bnds = pattern_list tyenv type_vars current_level loc patl
        Option.iter (fun ty_args_expected -> List.iter2 (fun ty ty_expected -> try unify tyenv ty ty_expected with Unify -> ()) ty_args ty_args_expected) ty_args_expected
        let names = List.map get_pattern_name patl
        let tyenv = add_values tyenv new_bnds
        let ty_res = expression ps tyenv type_vars current_level ty_result_expected e1
        List.foldBack2 (fun name ty1 ty2 -> Tarrow (name, ty1, ty2)) names ty_args ty_res
    | SEbegin cl ->
        if cl.Length = 0 then ty_unit
        else
            let (cl', res) = Misc.split_last cl

            match res.sc_desc with
            | SCexpr e1 ->
                let tyenv = List.fold (fun tyenv c ->
                    let new_bnds = command tyenv ps type_vars current_level c
                    Types.add_values tyenv new_bnds) tyenv cl' 
                expression ps tyenv type_vars current_level None e1
            | _ ->
                List.fold (fun tyenv c ->
                    let new_bnds = command tyenv ps type_vars current_level c
                    Types.add_values tyenv new_bnds) tyenv cl |> ignore
                Ttuple [] // = unit
    | SEcase (e, cases) ->
        let ty_arg = expression ps tyenv type_vars current_level None e
        let ty_res = new_tvar current_level
        List.iter (fun (pat, ew, e) ->
            let ty_pat, new_values = pattern tyenv type_vars current_level ty_arg pat
            unify_pat tyenv pat ty_pat ty_arg
            let tyenv = add_values tyenv new_values
            Option.iter (fun ew -> expression_expect ps tyenv type_vars current_level ty_bool ew) ew
            expression_expect ps tyenv type_vars current_level ty_res e) cases;
        ty_res
    | SEtry (e, cases) ->
        if not (List.forall (function (_, None, _) -> true | (_, Some _, _) -> false) cases) then raise (Type_error (Cannot_use_when_clause_in_try_construct, e.se_loc))
        let ty_arg = expression ps tyenv type_vars current_level None e
        List.iter (fun (pat, _, e) ->
            let ty_pat, new_values = pattern tyenv type_vars current_level (new_tvar current_level) pat
            unify_pat tyenv pat ty_pat ty_exn
            let tyenv = add_values tyenv new_values
            expression_expect ps tyenv type_vars current_level ty_arg e) cases
        ty_arg
    | SEifthenelse (e1, e2, e3) ->
        expression_expect ps tyenv type_vars current_level ty_bool e1
        match e3 with
        | Some e3 ->
            let ty_res = expression ps tyenv type_vars current_level None e2
            expression_expect ps tyenv type_vars current_level ty_res e3
            ty_res
        | None ->
            expression_expect ps tyenv type_vars current_level ty_unit e2
            ty_unit
    | SEset (s, e1) ->
        match tyenv.values.TryGetValue(s) with
        | false, _ -> raise (Type_error (Unbound_identifier s, e.se_loc))
        | true, info ->
            if info.vi_access = access.Immutable then
                raise (Type_error (Not_mutable (Variable, s), e.se_loc))
            expression_expect ps tyenv type_vars current_level info.vi_type e1;
            Ttuple []
    | SEgetfield (e1, s) ->
        let ty1 = expression ps tyenv type_vars current_level None e1
        let candidates = tyenv.labels.FindAll s
        let info_from_ty1 =
            match repr ty1 with
            | Tconstr (id, _) -> List.tryFind (fun (info : label_info) -> info.li_id = id) candidates
            | _ -> None
        let info =
            match info_from_ty1, candidates with
            | Some info, _ -> info
            | None, hd :: _ -> hd
            | None, [] -> raise (Type_error (Label_undefined s, e.se_loc))
        let ty_field, ty_record = instanciate_label current_level info
        unify_exp tyenv e1 ty1 ty_record 
        e.se_desc <- SEugetfield (e1, info.li_index)
        ty_field
    | SEsetfield (e1, s, e2) ->
        let ty1 = expression ps tyenv type_vars current_level None e1
        let candidates = tyenv.labels.FindAll s
        let info_from_ty1 =
            match repr ty1 with
            | Tconstr (id, _) -> List.tryFind (fun (info : label_info) -> info.li_id = id) candidates
            | _ -> None
        let info =
            match info_from_ty1, candidates with
            | Some info, _ -> info
            | None, hd :: _ -> hd
            | None, [] -> raise (Type_error (Label_undefined s, e.se_loc))
        if info.li_access <> access.Mutable then
            raise (Type_error (Not_mutable (Label, s), e.se_loc))
        let ty_field, ty_record = instanciate_label current_level info
        unify_exp tyenv e1 ty1 ty_record 
        expression_expect ps tyenv type_vars current_level ty_field e2
        e.se_desc <- SEusetfield (e1, info.li_index, e2)
        ty_unit
    | SEugetfield _ | SEusetfield _ -> dontcare ()
    | SEfor (s, e1, _, e2, e3) ->
        expression_expect ps tyenv type_vars current_level ty_int e1
        expression_expect ps tyenv type_vars current_level ty_int e2
        let tyenv = add_value tyenv s { vi_type = ty_int; vi_access = access.Immutable }
        statement tyenv ps type_vars current_level e3 |> ignore
        Ttuple []
    | SEwhile (e1, e2) ->
        expression_expect ps tyenv type_vars current_level ty_bool e1
        statement tyenv ps type_vars current_level e2 |> ignore
        Ttuple []
    | SEtype (e1, sty) ->
        let ty = type_expr tyenv false type_vars sty
        expression_expect ps tyenv type_vars current_level ty e1
        ty
    | SEformat _ -> dontcare()

/// Infer the type of expression with expectation. The expectation is used as hint.
/// Returns unit and the result remains in ty_expected.
/// Throws type error if failed.
and expression_expect (ps : string -> unit) (tyenv : tyenv) (type_vars : Dictionary<string, type_expr>) current_level ty_expected e =
    let ty = expression ps tyenv type_vars current_level (Some ty_expected) e
    unify_exp tyenv e ty ty_expected

and statement tyenv ps type_vars current_level e =
    let ty = expression ps tyenv type_vars current_level None e
    match repr ty with
    | Tarrow _ ->
        let {st = st; ed = ed} = e.se_loc
        Printf.kprintf ps "> Char %d-%d : Beware, this function is partially applied.\n" st.AbsoluteOffset ed.AbsoluteOffset
    | _ -> ()
    ty

and command tyenv ps (type_vars : Dictionary<string, type_expr>) current_level (cmd : Syntax.command) =
    match cmd.sc_desc with
    | SCexpr e ->
        statement tyenv ps type_vars current_level e |> ignore
        []
    | SCval l ->
        let ty_patl, new_bnds = pattern_list tyenv type_vars (current_level + 1) cmd.sc_loc (List.map fst l)
        let l = List.map2 (fun (_, e) ty_pat -> (ty_pat, e)) l ty_patl
        List.iter (fun (ty_pat, e) -> expression_expect ps tyenv type_vars (current_level + 1) ty_pat e) l
        List.iter (fun (ty_pat, e) ->
            if not (is_nonexpansive e) then
                make_nongen current_level ty_pat) l
        List.iter (fun (ty_pat, _) -> generalize current_level ty_pat) l
        new_bnds
    | SCfun defs ->
        let names = List.map fst defs
        List.iter (fun name -> if is_constructor name then raise (Type_error (Invalid_identifier, cmd.sc_loc))) names
        all_differ cmd.sc_loc kind.Function_name kind.Function_definition names

        let defs = List.map (fun (name, expr) ->
            let dummy_info = { vi_type = new_tvar (current_level + 1); vi_access = access.Immutable; }
            (name, expr, dummy_info)) defs
        let tyenv_with_dummy_info = add_values tyenv (List.map (fun (name, _, info) -> (name, info)) defs)
        let new_values =
            List.map (fun (name, expr, info) ->
                let ty = expression ps tyenv_with_dummy_info type_vars (current_level + 1) None expr
                unify_exp tyenv_with_dummy_info expr ty info.vi_type
                let info = { vi_type = ty; vi_access = access.Immutable; }
                name, info) defs
        List.iter (fun (_, info) -> generalize current_level info.vi_type) new_values
        new_values
    | SCvar l ->
        let names = List.map fst l
        List.iter (fun (name : string) -> if is_constructor name then raise (Type_error (Invalid_identifier, cmd.sc_loc))) names
        all_differ cmd.sc_loc kind.Variable_name kind.Variable_definition names

        List.map (fun (s, e) ->
            (s, { vi_type = expression ps tyenv type_vars current_level None e; vi_access = access.Mutable })) l
    | SCtype _
    | SChide _
    | SChideval _
    | SCexn _ -> raise (Type_error (Cannot_use_this_command_inside_an_expression, cmd.sc_loc))

let type_expression ps tyenv (e : Syntax.expression) =
    let ty = expression ps tyenv (Dictionary<string, type_expr>()) 1 None e
    if is_nonexpansive e then generalize 0 ty
    ty

let type_command ps tyenv (cmd : Syntax.command) =
    command tyenv ps (Dictionary<string, type_expr>()) 0 cmd

let tyenv_clone (tyenv : tyenv) =
    let tvars = Dictionary<type_var, type_var>(Misc.PhysicalEqualityComparer)

    let tvar_loop (orig : type_var) =
        match tvars.TryGetValue(orig) with
        | true, clone -> clone
        | false, _ ->
            let clone = { type_var.level = orig.level; link = None }
            tvars.[orig] <- clone
            clone
    
    let rec ty_loop (ty : type_expr) =
        let ty = repr ty
        match ty with
        | Tvar tv ->
            if tv.level = generic_level
            then ty
            else Tvar (tvar_loop tv)
        | Tarrow (name, ty1, ty2) ->
            let ty1_clone = ty_loop ty1
            let ty2_clone = ty_loop ty2
            Tarrow (name, ty1_clone, ty2_clone)
        | Ttuple tyl ->
            let tyl_clone = List.map ty_loop tyl
            if List.forall2 LanguagePrimitives.PhysicalEquality tyl tyl_clone
            then ty
            else Ttuple tyl_clone
        | Tconstr (id, tyl) ->
            let tyl_clone = List.map ty_loop tyl
            if List.forall2 LanguagePrimitives.PhysicalEquality tyl tyl_clone
            then ty
            else Tconstr (id, tyl_clone)
    
    let values' = ImmutableDictionary.CreateBuilder()
    for kv in tyenv.values do
        values'.Add(kv.Key, { kv.Value with vi_type = ty_loop kv.Value.vi_type })

    { tyenv with values = values'.ToImmutable() }

type checked_command = 
    | CCexpr of expression * type_expr * location
    | CCval of (pattern * expression) list * (string * value_info) list * location
    | CCfun of (string * expression) list * (string * value_info) list * location
    | CCvar of (string * expression) list * (string * value_info) list * location
    | CCtype of typedef list * location
    | CChide of string * location
    | CChideval of string
    | CCexn of string * location

let type_command_list ps tyenv cmds =
    let mutable tyenv = tyenv_clone tyenv
    let tyenvs = ResizeArray()
    let ccmds = ResizeArray()
    for cmd in cmds do
        match cmd with
        | { sc_desc = SCtype dl } ->
            let tyenv' = add_typedef tyenv cmd.sc_loc dl
            tyenvs.Add(tyenv)
            ccmds.Add (CCtype (dl, cmd.sc_loc))
            tyenv <- tyenv'
        | { sc_desc = SChide (name, loc) } -> 
            let tyenv' = Types.hide_type tyenv name
            tyenvs.Add(tyenv)
            ccmds.Add (CChide (name, loc))
            tyenv <- tyenv'
        | { sc_desc = SChideval name } ->
            if tyenv.values.ContainsKey(name) then
                let tyenv' = { tyenv with values = tyenv.values.Remove(name) }
                tyenvs.Add(tyenv')
                ccmds.Add(CChideval name)
                tyenv <- tyenv'
            else raise (Type_error ((Unbound_identifier name), cmd.sc_loc))
        | { sc_desc = SCexn (name, tyl) } ->
            if not (Char.IsUpper name.[0]) then raise (Type_error (Must_start_with_uppercase Exception_name, cmd.sc_loc))
            let tyl = List.map (type_expr tyenv true (Dictionary<string, type_expr>())) tyl
            let tyenv', _ = add_exn_constructor tyenv name tyl
            tyenvs.Add(tyenv)
            ccmds.Add (CCexn (name, cmd.sc_loc))
            tyenv <- tyenv'
        | { sc_desc = SCexpr e } ->
            let ty = type_expression ps tyenv e
            tyenvs.Add(tyenv)
            ccmds.Add (CCexpr (e, ty, cmd.sc_loc))
        | { sc_desc = (SCval _ | SCvar _ | SCfun _) } as cmd ->
            let new_values = type_command ps tyenv cmd
            let tyenv' = Types.add_values tyenv new_values
            tyenvs.Add(tyenv)
            ccmds.Add (match cmd.sc_desc with
                       | SCval l -> (CCval (l, new_values, cmd.sc_loc))
                       | SCvar l -> (CCvar (l, new_values, cmd.sc_loc))
                       | SCfun l -> (CCfun (l, new_values, cmd.sc_loc))
                       | _ -> dontcare())
            tyenv <- tyenv'
        
    tyenvs.Add(tyenv)
    (tyenvs.ToArray(), ccmds.ToArray())
