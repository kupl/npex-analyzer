open! IStd
open! Vocab

module Key = struct
  type t =
    {arg_length: int; method_name: string; model_index: int; ret_type: abstract_type; method_kind: method_kind}
  [@@deriving compare]

  and abstract_type = Aint | Afloat | Aobject | Avoid [@@deriving compare]

  and method_kind = Static | Constructor | Virtual [@@deriving compare]

  let equal_abstract_type = [%compare.equal: abstract_type]

  let equal_method_kind = [%compare.equal: method_kind]

  let equal = [%compare.equal: t]

  let is_prefix callee ~prefix:{arg_length; method_name; model_index; ret_type; method_kind} =
    Int.equal callee.arg_length arg_length
    && String.is_prefix callee.method_name ~prefix:method_name
    && Int.equal model_index callee.model_index
    && equal_abstract_type ret_type callee.ret_type
    && equal_method_kind method_kind callee.method_kind


  let to_string_abstract_type = function
    | Aint ->
        "int"
    | Afloat ->
        "float"
    | Aobject ->
        "Object"
    | Avoid ->
        "void"


  let abstract_type_from_typ typ =
    let open Typ in
    match typ.desc with
    | Tint _ ->
        Aint
    | Tfloat _ ->
        Afloat
    | Tvoid ->
        Avoid
    | Tptr _ ->
        Aobject
    | Tstruct _ | Tarray _ | Tfun ->
        Aobject
    | TVar _ ->
        L.(die ExternalError) "TVar type is C++, not in Java"


  let pp fmt {model_index; method_name; ret_type} =
    (* TODO: print method kind *)
    let ret_typ_str = to_string_abstract_type ret_type in
    match model_index with
    | 0 ->
        F.fprintf fmt "%s:%s.%s(...)" ret_typ_str "NULL" method_name
    | 1 ->
        F.fprintf fmt "%s:....%s(%s, ...)" ret_typ_str method_name "NULL"
    | 2 ->
        F.fprintf fmt "%s:....%s(..., %s, ...)" ret_typ_str method_name "NULL"
    | 3 ->
        F.fprintf fmt "%s:....%s(..., ..., %s, ...)" ret_typ_str method_name "NULL"
    | _ ->
        F.fprintf fmt "%s:....%s(..., ..., ..., %s)" ret_typ_str method_name "NULL"


  let default_of ret_type method_name = {arg_length= 1; model_index= 0; ret_type; method_kind= Virtual; method_name}

  let make ?(arg_length = 1) ?(model_index = 0) ?(method_kind = Virtual) ret_type method_name =
    {arg_length; model_index; ret_type; method_kind; method_name}


  let get_method_kind proc =
    match proc with
    | Procname.Java mthd when Procname.Java.is_static mthd ->
        Static
    | _ when Procname.is_constructor proc ->
        Constructor
    | _ ->
        Virtual


  let from_instr instr model_index =
    match instr with
    | Sil.Call ((_, ret_typ), Const (Cfun callee), arg_typs, _, _) ->
        let arg_length = List.length arg_typs in
        let method_name = Procname.get_method callee in
        let ret_type = abstract_type_from_typ ret_typ in
        let method_kind = get_method_kind callee in
        Some {arg_length; model_index; ret_type; method_kind; method_name}
    | _ ->
        None
end

module Pos = struct
  type t = InstrNode.t * int [@@deriving compare]

  let pp fmt (InstrNode.{inode; instr}, pos) =
    let null_access_str =
      match instr with
      | Sil.Call (_, Const (Cfun procname), _, _, {cf_virtual}) when cf_virtual ->
          let method_name = Procname.get_method procname in
          if Int.equal pos 0 then F.asprintf "NULL.%s(_)" method_name
          else F.asprintf "_.%s(%d-th NULL)" method_name pos
      | Sil.Call (_, Const (Cfun procname), _, _, _) ->
          let method_name = Procname.get_method procname in
          F.asprintf "_.%s(%d-th NULL)" method_name pos
      | _ ->
          ""
    in
    F.fprintf fmt "%s (%a)" null_access_str Location.pp_line (InterNode.get_loc inode)


  let to_key ((InstrNode.{instr}, model_index) as pos) =
    match Key.from_instr instr model_index with
    | Some key ->
        key
    | None ->
        L.(die InternalError) "no key from %a" pp pos
end

module MExp = struct
  type t = model_exp list [@@deriving compare]

  and model_exp =
    (* TODO: design static field (e.g., Collections.EMPTY_SET) *)
    | NULL
    | Const of Const.t
    | Param of int
    | Assign of model_exp * model_exp
    | Call of string * model_exp list
    | Skip
    | Exn of string
    | NonNull
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let is_null : t -> bool = function [NULL] -> true | _ -> false

  let rec pp_model_exp fmt = function
    | NULL ->
        F.fprintf fmt "NULL"
    | Const c ->
        (Const.pp Pp.text) fmt c
    | Param i ->
        F.fprintf fmt "(#%d)" i
    | Assign (lhs, rhs) ->
        F.fprintf fmt "%a := %a" pp_model_exp lhs pp_model_exp rhs
    | Call (proc, args) ->
        F.fprintf fmt "%s(%a)" proc (Pp.seq ~sep:"," pp_model_exp) args
    | Skip ->
        F.fprintf fmt "SKIP"
    | Exn exn_type ->
        F.fprintf fmt "throw new %s" exn_type
    | NonNull ->
        F.fprintf fmt "NonNull"


  let pp = Pp.seq ~sep:" ; " pp_model_exp
end

let unresolved = ref String.Set.empty

module MValue = struct
  type t = MExp.t * float [@@deriving compare]

  let equal = [%compare.equal: t]

  let equal_wo_prob : t -> t -> bool = fun (x, _) (y, _) -> MExp.equal x y

  let no_apply = ([], 0.5)

  let make_null ~prob : t = ([NULL], prob)

  let make_const ~prob const : t = ([Const const], prob)

  let make_skip ~prob : t = ([Skip], prob)

  let make_exn ~prob exn_type : t = ([Exn exn_type], prob)

  let make_nonnull ~prob : t = ([NonNull], prob)

  let from_string_opt ~mval_str ~type_str ~kind_str ~prob : t option =
    let arg_index index = if String.equal kind_str "STATIC" then index else index + 1 in
    match mval_str with
    | "0" | "false" ->
        Some (make_const ~prob (Const.Cint IntLit.zero))
    | "1" | "true" ->
        Some (make_const ~prob (Const.Cint IntLit.one))
    | "0.0F" ->
        Some (make_const ~prob (Const.Cfloat 0.0))
    | "\"\"" ->
        Some (make_const ~prob (Const.Cstr ""))
    | "null" ->
        Some (make_null ~prob)
    | "\"NPEX_SKIP_VALUE\"" | "NPEX_SKIP_VALUE" ->
        Some (make_skip ~prob)
    (* TODO: use nonLiteral to invalidate unconfident model *)
    (* | "NPEXNonLiteral" ->
        Some (make_nonnull ~prob) *)
    (* | "NPEXThrowable" ->
        Some (make_exn ~prob "java.lang.Exception") *)
    | "java.lang.Object.class" ->
        Some (make_const ~prob (Const.Cstr "java.lang.Object"))
    | "java.util.Collections.emptySet()" | "java.util.Collections.emptyList()" | "java.util.Collections.emptyMap()"
      ->
        Some ([Call ("newCollection", [])], prob)
    | "EQ, $(0), null" ->
        (* TODO: parse it by regular expression *)
        Some ([Call ("equals", [Param (arg_index 0); NULL])], prob)
    | "EQ, $(1), null" ->
        (* TODO: parse it by regular expression *)
        Some ([Call ("equals", [Param (arg_index 1); NULL])], prob)
    | "$(-1)" | "this" ->
        (* TODO: parse it by regular expression *)
        Some ([Param (arg_index (-1))], prob)
    | "$(0)" ->
        (* TODO: parse it by regular expression *)
        Some ([Param (arg_index 0)], prob)
    | "$(1)" ->
        (* TODO: parse it by regular expression *)
        Some ([Param (arg_index 1)], prob)
    | "nonnull" ->
        None
    | _ ->
        (* TODO: *)
        unresolved := String.Set.add !unresolved mval_str ;
        L.(debug Analysis Quiet) "[WARNING]: model value %s is not resolved@." mval_str ;
        (* None *)
        Some ([Param 999], prob)


  let pp fmt (model_exp_list, prob) = F.fprintf fmt "%f (%a)" prob MExp.pp model_exp_list
end
