﻿module FsMiniMAL.Types

open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Reflection
open FSharp.Reflection

type type_id =
    | UNIT = 0
    | INT = 1
    | CHAR = 2
    | FLOAT = 3
    | ARRAY = 4
    | BOOL = 5
    | LIST = 6
    | STRING = 7
    | FORMAT = 8
    | REF = 9
    | EXN = 10
    | LEXBUF = 11

let mutable private type_id_top = 12

let type_id_new () =
    let i = type_id_top
    type_id_top <- type_id_top + 1
    enum<type_id> i

type [<NoEquality; NoComparison >]
    type_expr = 
    | Tvar of type_var
    | Tarrow of string * type_expr * type_expr
    | Ttuple of type_expr list
    | Tconstr of type_id * type_expr list

// This type represents type variable. It realizes assignment operation to type varialbe using mutable 'link' field.
// The 'level' field is assigned based on the position (depth from root) in expression tree where the type variable was introduced.
// And level indicates area of influence when type var is assigned to particular type.
and type_var = 
    { mutable link : type_expr option
      mutable level : int }

let generic_level = -1

type value_info = 
    { vi_type : type_expr
      vi_access : access }

type type_info = 
    { ti_name : string
      ti_params : type_var list
      ti_res : type_expr // 常に Tconstr
      ti_kind : type_kind }

and type_kind = 
    | Kabbrev of type_expr
    | Kvariant of (string * int * type_expr list) list
    | Krecord of (string * type_expr * access) list
    | Kbasic

// This type represents record label information.
// Exapmle in field comment is for the 'bar' field when we deifne type 'foobar' as below.
// "type 'a foobar = { foo : int, bar : 'a list }"
type label_info = 
    { li_id : type_id // ID_FOOBAR
      li_params : type_var list // ['a]
      li_arg : type_expr // [Tconstr (ID_LIST, ['a])]
      li_res : type_expr // [Tconstr (ID_FOOBAR, ['a])]
      li_access : access // Immutable
      li_total : int // 2
      li_index : int // 1
    }

// This type represents case (constructor) of variant type.
// Example in field comment is for the 'Bar' case when we define type 'foobar' as below.
// "type ('a, 'b) foobar = Foo of 'a | Bar of 'b"
type constr_info = 
    { ci_params : type_var list // ['a; 'b]
      ci_args : type_expr list // [Tvar 'b]
      ci_res : type_expr //  Tconstr (ID_FOOBAR, ['a; 'b])
      ci_tag : int // 1
    }

let ty_int = Tconstr (type_id.INT, [])
let ty_char = Tconstr (type_id.CHAR, [])
let ty_float = Tconstr (type_id.FLOAT, [])
let ty_bool = Tconstr (type_id.BOOL, [])
let ty_unit = Ttuple []
let ty_exn = Tconstr (type_id.EXN, [])

let arrow t1 t2 = Tarrow ("", t1, t2)
let arrow2 t1 t2 t3 = Tarrow ("",t1, (Tarrow ("",t2, t3)))
let arrow3 t1 t2 t3 t4 = Tarrow ("",t1, (Tarrow ("",t2, Tarrow ("",t3, t4))))
let arrow4 t1 t2 t3 t4 t5 = Tarrow ("",t1, (Tarrow ("",t2, Tarrow ("",t3, Tarrow ("",t4, t5)))))
let arrow5 t1 t2 t3 t4 t5 t6 = Tarrow ("",t1, (Tarrow ("",t2, Tarrow ("",t3, Tarrow ("",t4, (Tarrow ("",t5, t6)))))))
let named_arrow2 name1 t1 name2 t2 t3 = Tarrow (name1 ,t1, (Tarrow (name2,t2, t3)))
let ty_list a = Tconstr (type_id.LIST, [ a ])
let ty_array a = Tconstr (type_id.ARRAY, [ a ])
let ty_string = Tconstr (type_id.STRING, [])
let ty_floatarray = ty_array ty_float
let ty_ref a = Tconstr (type_id.REF, [ a ])

let ty_ii = arrow ty_int ty_int
let ty_iii = arrow2 ty_int ty_int ty_int
let ty_ff = arrow ty_float ty_float
let ty_fff = arrow2 ty_float ty_float ty_float

let tv_a = { link = None; level = 0 }
let tv_b = { link = None; level = 0 }

let make_ti id name params' kind = 
    { ti_name = name;
      ti_params = params'
      ti_res = Tconstr(id, List.map (fun tv -> Tvar tv) params')
      ti_kind = kind }

let ti_int = make_ti type_id.INT "int" [] Kbasic
let ti_char = make_ti type_id.CHAR "char" [] Kbasic
let ti_float = make_ti type_id.FLOAT "float" [] Kbasic
let ti_array = make_ti type_id.ARRAY "array" [ tv_a ] Kbasic
let ti_bool = make_ti type_id.BOOL "bool" [] (Kvariant [ "false", 0, []; "true", 1, [] ])
let ti_list = make_ti type_id.LIST "list" [ tv_a ] (Kvariant [ "[]", 0, []; "::", 1, [ Tvar tv_a; Tconstr(type_id.LIST, [ Tvar tv_a ]) ] ])
let ti_unit = make_ti type_id.UNIT "unit" [] (Kabbrev(Ttuple []))
let ti_string = make_ti type_id.STRING "string" [] Kbasic
let ti_format = make_ti type_id.FORMAT "format" [tv_a; tv_b] Kbasic
let ti_exn = make_ti type_id.EXN "exn" [] Kbasic
let ti_lexbuf = make_ti type_id.LEXBUF "lexbuf" [] (Krecord [("source", ty_string, Immutable)
                                                             ("start_pos", ty_int, Mutable)
                                                             ("end_pos", ty_int, Mutable)
                                                             ("scan_start_pos", ty_int, Mutable)
                                                             ("eof", ty_bool, Mutable)])

type tyenv =
    { types :  MultiStrMap<type_info>
      types_of_id : Map<type_id, type_info>
      constructors : MultiStrMap<constr_info>
      exn_constructors : (string * constr_info) array
      labels :  MultiStrMap<label_info>

      // Value infos are separated into two dictionaries to make tyenv_clone faster.
      // Keys stored in two dictionaries never overwrap.

      // Values with immutable type expressions.
      // Thus, type expressions which doesn't contain type vars or contains type vars but generic ones only.
      values_typeexpr_immutable :   ImmutableDictionary<string, value_info>

      // Values with mutable type expressions.
      // Thus, type expressions which contains narrowable (non-generic) type vars.
      // It is okay to set values with immutable type vars to values_typeexpr_mutable.
      // They will be moved to values_typeexpr_immutable when scanned by tyenv_clone.
      values_typeexpr_mutable :   ImmutableDictionary<string, value_info>

      registered_abstract_types : Dictionary<Type, type_id>
      registered_fsharp_types : Dictionary<Type, type_id> }

let try_get_value (tyenv : tyenv) name =
    match tyenv.values_typeexpr_immutable.TryGetValue(name) with
    | true, info -> Some info
    | false, _ ->
        match tyenv.values_typeexpr_mutable.TryGetValue(name) with
        | true, info -> Some info
        | _ -> None

let add_type tyenv info =
    let name = info.ti_name
    let id = match info.ti_res with Tconstr(id, _) -> id | _ -> dontcare()
    let tyenv = { tyenv with
                    types = tyenv.types.Add(name, info)
                    types_of_id = tyenv.types_of_id.Add(id, info) }

    match info.ti_kind with
    | Kvariant l ->
        let cs = List.map (fun (name, tag, ty_args) ->
            let info = 
                { ci_params = info.ti_params
                  ci_args = ty_args
                  ci_res = info.ti_res
                  ci_tag = tag }
            (name, info)) l
        List.fold (fun tyenv (name, info) -> { tyenv with constructors = tyenv.constructors.Add(name, info) }) tyenv cs

    | Krecord l -> 
        let total = List.length l
        list_foldi (fun tyenv i (name, ty_arg, access) ->
            let info =
                { li_id = id
                  li_params = info.ti_params
                  li_arg = ty_arg
                  li_res = info.ti_res
                  li_access = access
                  li_total = total
                  li_index = i }
            { tyenv with labels = tyenv.labels.Add(name, info) }) tyenv l
    | _ -> tyenv

let remove_type tyenv info =
    let name = info.ti_name
    let id =
        match info.ti_res with
            | Tconstr(id, _) -> id
            | _ -> dontcare()
        
    let e =
        { tyenv with
            types = tyenv.types.Remove(name, (fun ti -> match ti.ti_res with Tconstr (id', _) -> id = id' | _ -> false))
            types_of_id = tyenv.types_of_id.Remove(id) }

    match info.ti_kind with
    | Kvariant l ->
        List.fold (fun e (name, tag, ty_args) ->
                { e with
                    constructors = e.constructors.Remove(name, (fun info -> match info.ci_res with Tconstr (id', _) -> id = id' | _ -> false))}) e l

    | Krecord l ->
        List.fold (fun e (name, _, _) ->
            { e with
                    labels = e.labels.Remove(name, (fun li -> match li.li_res with Tconstr (id', _) -> id = id' | _ -> false)) }) e l
    | _ -> e

let add_exn_constructor tyenv name args =
    let tag = tyenv.exn_constructors.Length
    let ci = { ci_params = []
               ci_args = args
               ci_res = ty_exn
               ci_tag = tag }
    
    { tyenv with
        constructors = tyenv.constructors.Add(name, ci)
        exn_constructors = Array.append tyenv.exn_constructors [| (name, ci) |] }, tag

let add_value (tyenv : tyenv) name info =
    { tyenv with
        values_typeexpr_mutable = tyenv.values_typeexpr_mutable.SetItem(name, info)
        values_typeexpr_immutable = tyenv.values_typeexpr_immutable.Remove(name) }

let add_values (tyenv : tyenv) (new_values : (string * value_info) seq) =
    let accu_mutable = tyenv.values_typeexpr_mutable.ToBuilder()
    let accu_immutable = tyenv.values_typeexpr_immutable.ToBuilder()
    for (name, info) in new_values do
        accu_mutable.[name] <- info
        accu_immutable.Remove(name) |> ignore
    { tyenv with
        values_typeexpr_mutable = accu_mutable.ToImmutable()
        values_typeexpr_immutable = accu_immutable.ToImmutable() }

let rec typeexpr_of_type (tyenv : tyenv) (bnds : Dictionary<Type, type_expr>) (ty : Type) =
    if ty = typeof<unit> then
        ty_unit
    elif ty = typeof<bool> then
        ty_bool
    elif ty = typeof<int32> then
        ty_int
    elif ty = typeof<char> then
        ty_char
    elif ty = typeof<float> then
        ty_float
    elif ty = typeof<string> then
        ty_string
    elif ty.IsGenericParameter then
        bnds.[ty]
    elif ty.IsArray then
        let ty_elem = ty.GetElementType()
        ty_array (typeexpr_of_type tyenv bnds ty_elem)
    elif FSharpType.IsTuple ty then
        let types = Array.map (typeexpr_of_type tyenv bnds) (FSharpType.GetTupleElements(ty))
        Ttuple (List.ofArray types)
    elif tyenv.registered_abstract_types.ContainsKey(ty) then
        let id = tyenv.registered_abstract_types.[ty]
        Tconstr (id, [])
    elif FSharpType.IsRecord ty || FSharpType.IsUnion ty then
        let args =
            let info = ty.GetTypeInfo()
            if info.IsGenericTypeDefinition then
                info.GenericTypeParameters |> Array.map (typeexpr_of_type tyenv bnds) |> List.ofArray
            elif info.IsConstructedGenericType then
                info.GenericTypeArguments |> Array.map (typeexpr_of_type tyenv bnds) |> List.ofArray
            else []
        let id = tyenv.registered_fsharp_types.[(if ty.GetTypeInfo().IsGenericType then ty.GetGenericTypeDefinition() else ty)]
        Tconstr (id, args)             
    elif FSharpType.IsFunction ty then
        let t1, t2 = FSharpType.GetFunctionElements(ty)
        Tarrow ("",(typeexpr_of_type tyenv bnds) t1, (typeexpr_of_type tyenv bnds) t2)
    else
        dontcare()

let register_abstract_type (tyenv : tyenv) (name : string) (ty : Type) =
    let id = type_id_new()

    let info = { ti_name = name; ti_params = []; ti_res = Tconstr (id, []); ti_kind = Kbasic }

    let tyenv =
        { tyenv with
            registered_abstract_types =
                let dict = Dictionary(tyenv.registered_abstract_types)
                dict.Add(ty, id)
                dict
            types = tyenv.types.Add(name, info)
            types_of_id = tyenv.types_of_id.Add(id, info) }
        
    (tyenv, id)

let register_fsharp_types tyenv (types : (string * Type) array) =

    Array.iter (fun (_, ty) ->
        if not (FSharpType.IsRecord(ty) || FSharpType.IsUnion(ty)) then dontcare()
        if ty.IsConstructedGenericType then dontcare()) types
    
    let types = Array.map (fun (name, ty) -> (name, ty, type_id_new())) types

    let dummy_tyenv =
        { tyenv with
            registered_fsharp_types =
                let dict = Dictionary(tyenv.registered_fsharp_types)
                for (_, ty, id) in types do
                    dict.Add(ty, id)
                dict }
    
    let mutable tyenv = tyenv

    for (name, ty, id) in types do

        let ty_params = List.ofArray (if ty.IsGenericTypeDefinition then ty.GetTypeInfo().GenericTypeParameters else [||])
        let mappings = List.map (fun (ty_arg : Type) ->
            let tv = { link = None ; level = 0 }
            (ty_arg, tv, Tvar tv)) ty_params

        let bnds =
            let dict = Dictionary()
            List.iter (fun (ty, mal_tv, mal_ty) -> dict.Add(ty, mal_ty)) mappings
            dict

        let mal_vars = List.map (fun (ty, mal_tv, mal_ty) -> mal_tv) mappings
        let mal_args = List.map (fun (ty, mal_tv, mal_ty) -> mal_ty) mappings

        if FSharpType.IsRecord ty then
            let fields = FSharpType.GetRecordFields(ty)
            let fields =
                Array.map (fun (field : PropertyInfo) ->
                    let name = field.Name
                    let field_type = typeexpr_of_type dummy_tyenv bnds field.PropertyType
                    let access = if field.CanWrite then access.Mutable else access.Immutable
                    (name, field_type, access)) fields
                |> List.ofArray

            let info = { ti_name = name; ti_params = mal_vars; ti_res = Tconstr (id, mal_args); ti_kind = Krecord fields }
            let fields_count = List.length fields

            tyenv <-
                { tyenv with
                        registered_fsharp_types =
                            let dict = Dictionary(tyenv.registered_fsharp_types)
                            dict.Add(ty, id)
                            dict
                        types = tyenv.types.Add(name, info)
                        types_of_id = tyenv.types_of_id.Add(id, info)
                        labels = list_foldi (fun accu i (name, ty_arg, access) ->
                            let info =
                                { li_id = id
                                  li_params = info.ti_params
                                  li_arg = ty_arg
                                  li_res = info.ti_res
                                  li_access = access
                                  li_total = fields_count
                                  li_index = i }
                            accu.Add(name, info)  ) tyenv.labels fields }
            
        else // union
            let cases = FSharpType.GetUnionCases(ty)
            let cases = 
                Array.map (fun (case : UnionCaseInfo) ->
                    let name = case.Name
                    let field_types =
                        case.GetFields()
                        |> Array.map (fun (f : PropertyInfo) ->
                            let t = f.PropertyType
                            typeexpr_of_type dummy_tyenv bnds t)
                        |> List.ofArray
                    let tag = case.Tag
                    (name, tag, field_types)) cases
                |> List.ofArray

            let info = { ti_name = name; ti_params = mal_vars; ti_res = Tconstr (id, mal_args); ti_kind = Kvariant cases }

            tyenv <-
                { tyenv with
                    registered_fsharp_types =
                        let dict = Dictionary(tyenv.registered_fsharp_types)
                        dict.Add(ty, id)
                        dict
                    types = tyenv.types.Add(name, info)
                    types_of_id = tyenv.types_of_id.Add(id, info)
                    constructors = List.fold (fun accu (name, tag, ty_args) ->
                        let info = 
                            { ci_params = info.ti_params
                              ci_args = ty_args
                              ci_res = info.ti_res
                              ci_tag = tag }                    
                        accu.Add(name, info)) tyenv.constructors cases }

    let ids = Array.map (fun (_, _, id) -> id) types
    tyenv, ids

let tyenv_basic, id_ref, id_option, tag_exn_Failure, tag_exn_DivisionByZero, tag_exn_IndexOutOfRange, tag_exn_MatchFailure =
    let tyenv =
        { tyenv.types =  MultiStrMap.Empty
          types_of_id = Map.empty
          constructors = MultiStrMap.Empty
          exn_constructors = [||]
          labels =  MultiStrMap.Empty
          values_typeexpr_mutable = ImmutableDictionary.Empty
          values_typeexpr_immutable = ImmutableDictionary.Empty
          registered_abstract_types = Dictionary()
          registered_fsharp_types = Dictionary() }
     
    let tyenv = Array.fold add_type tyenv [| ti_int; ti_char; ti_float; ti_array; ti_bool; ti_list; ti_unit; ti_string; ti_format; ti_exn; ti_lexbuf |]
    
    tyenv.registered_fsharp_types.Add(typedefof<list<_>>, type_id.LIST)

    let tyenv, ids = register_fsharp_types tyenv [| ("ref", typedefof<ref<_>>); ("option", typedefof<option<_>>) |]
    let id_ref = ids.[0]
    let id_option = ids.[1]
    
    let tyenv, tag_exn_Failure = add_exn_constructor tyenv "Failure" [ty_string]
    let tyenv, tag_exn_DivisionByZero = add_exn_constructor tyenv "DivisionByZero" []
    let tyenv, tag_exn_IndexOutOfRange = add_exn_constructor tyenv "IndexOutOfRange" []
    let tyenv, tag_exn_MatchFailure = add_exn_constructor tyenv "MatchFailure" []

    tyenv, id_ref, id_option, tag_exn_Failure, tag_exn_DivisionByZero, tag_exn_IndexOutOfRange, tag_exn_MatchFailure