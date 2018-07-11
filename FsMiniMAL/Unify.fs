module FsMiniMAL.Unify

open Types

exception Unify

let map_type f ty =
    match ty with
    | Tvar _ -> ty
    | Tarrow(name, ty1, ty2) -> Tarrow(name, f ty1, f ty2)
    | Ttuple tyl -> Ttuple(List.map f tyl)
    | Tconstr(id, tyl) -> Tconstr(id, List.map f tyl)

let do_type f ty = 
    match ty with
    | Tvar _ -> ()
    | Tarrow(_, ty1, ty2) -> 
        f ty1
        f ty2
    | Ttuple tyl -> List.iter f tyl
    | Tconstr(_, tyl) -> List.iter f tyl

/// Follow the link of type var and returns represented type.
/// Therefore returned type will be Ttuple, Tarrow, Tconstr or unassigned Tvar.
/// As a side effect, updates link field to shortest path to represented type.
/// (Doing so doesn't change meaning of type instance, only increase performance when calling 'repr' next time.)
let rec repr ty =
    match ty with
    | Tvar ({ link = Some ty' } as tv) -> 
        let ty'' = repr ty'
        if not (LanguagePrimitives.PhysicalEquality ty' ty'') then
            tv.link <- Some ty''
        ty''
    | _ -> ty

/// Substitutes tvar appears in ty using mapping from tvar instance to ty instance.
let rec subst (s : (type_var * type_expr) list) ty = 
    match repr ty with
    | Tvar tv as ty ->
        match assqo tv s with
        | Some ty' -> ty'
        | None -> ty
    | ty -> map_type (subst s) ty

/// Expand type abbreviation.
/// When ty is Tconstr which is defined as type abbreviation in tyenv, returns expanded type.
/// Otherwise returns None.
let expand (tyenv : tyenv) ty =
    match repr ty with
    | Tconstr(id, ty_args) ->
        match tyenv.types_of_id.TryFind(id) with
        | Some ({ ti_kind = Kabbrev ty' } as info) -> Some (subst (List.zip info.ti_params ty_args) ty')
        | _ -> None
    | _ -> None

/// Returns true if two types are same. This function doesn't cause side effects which changes maeaning of type expr.
let rec same_type tyenv ty1 ty2 =
    match repr ty1, repr ty2 with
    | Tvar a, Tvar b -> LanguagePrimitives.PhysicalEquality a b
    | Tarrow (_, ty11, ty12), Tarrow (_, ty21, ty22) -> same_type tyenv ty11 ty21 && same_type tyenv ty12 ty22
    | Ttuple l1, Ttuple l2 -> l1.Length = l2.Length && List.forall2 (same_type tyenv) l1 l2
    | Tconstr (id1, l1), Tconstr (id2, l2) when id1 = id2 -> l1.Length = l2.Length && List.forall2 (same_type tyenv) l1 l2
    | _ ->
        match expand tyenv ty1 with
        | Some ty1 -> same_type tyenv ty1 ty2
        | None ->
            match expand tyenv ty2 with
            | Some ty2 -> same_type tyenv ty1 ty2
            | None -> false

/// Raises exception Unify when tvar appears in ty.
/// As a side effect, updates level of all tvar in this ty. 
let rec occur tv ty = 
    match repr ty with
    | Tvar tv' -> 
        if LanguagePrimitives.PhysicalEquality tv tv' then raise Unify
        if tv'.level > tv.level then tv'.level <- tv.level
    | ty -> do_type (occur tv) ty

/// Perform unification. Throws exception Unify when impossible.
/// Unification is procedure to test two types can be same type by assigining to unassigned tvar, and actually do it.
/// Note that ty1, ty2 and tyenv can be leave mutated even after failed unification (raises Unify).
let rec unify tyenv ty1 ty2 = 
    match repr ty1, repr ty2 with
    | Tvar tv1, Tvar tv2 ->
        if not (LanguagePrimitives.PhysicalEquality tv1 tv2) then
            tv1.link <- Some ty2
            tv2.level <- min tv1.level tv2.level
    | Tvar tv, _ -> 
        occur tv ty2
        tv.link <- Some ty2
    | _, Tvar tv -> 
        occur tv ty1
        tv.link <- Some ty1
    | Tarrow(_, ty11, ty12), Tarrow(_, ty21, ty22) -> 
        unify tyenv ty11 ty21
        unify tyenv ty12 ty22
    | Ttuple l1, Ttuple l2 -> 
        if List.length l1 <> List.length l2 then raise Unify
        List.iter2 (unify tyenv) l1 l2
    | Tconstr(id1, l1), Tconstr(id2, l2) when id1 = id2 -> List.iter2 (unify tyenv) l1 l2
    | _ ->
        match expand tyenv ty1 with
        | Some ty1 -> unify tyenv ty1 ty2
        | None ->
            match expand tyenv ty2 with
            | Some ty2 -> unify tyenv ty1 ty2
            | None -> raise Unify


