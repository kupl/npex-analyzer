open! IStd
open! Vocab

module Pos = struct
  type t = InstrNode.t * int [@@deriving compare]

  let pp fmt (InstrNode.{inode; instr}, pos) =
    let null_access_str =
      match instr with
      | Sil.Call (_, Const (Cfun procname), _, _, {cf_virtual}) when cf_virtual ->
          let method_name = Procname.get_method procname in
          if Int.equal pos 0 then F.asprintf "NULL.%s(_)" method_name
          else F.asprintf "_.%s(%d-th NULL)" method_name (pos - 1)
      | Sil.Call (_, Const (Cfun procname), _, _, _) ->
          let method_name = Procname.get_method procname in
          F.asprintf "_.%s(%d-th NULL)" method_name pos
      | _ ->
          ""
    in
    (* TODO: add pretty print (e.g., null.isEmpty -> true (at filepath:line) *)
    F.fprintf fmt "%s (%a)" null_access_str Location.pp_line (InterNode.get_loc inode)
end

module MValue = struct
  type t = model_exp list * prob [@@deriving compare]

  and model_exp =
    (* TODO: design static field (e.g., Collections.EMPTY_SET) *)
    | NULL
    | Const of Const.t
    | Param of int
    | Assign of model_exp * model_exp
    | Call of Procname.t * model_exp list
    | Skip
    | Exn of string

  and prob = float

  let equal = [%compare.equal: t]

  let no_apply = ([], 1.0)

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
        F.fprintf fmt "%s(%a)" (Procname.get_method proc) (Pp.seq ~sep:"," pp_model_exp) args
    | Skip ->
        F.fprintf fmt "SKIP"
    | Exn exn_type ->
        F.fprintf fmt "throw new %s" exn_type


  let make_null ?(prob = 1.0) : t = ([NULL], prob)

  let make_const ?(prob = 1.0) const : t = ([Const const], prob)

  let make_skip ?(prob = 1.0) : t = ([Skip], prob)

  let make_exn ?(prob = 1.0) exn_type : t = ([Exn exn_type], prob)

  let pp fmt (model_exp_list, prob) = F.fprintf fmt "%f (%a)" prob (Pp.seq ~sep:" ; " pp_model_exp) model_exp_list
end

module MValueSet = PrettyPrintable.MakePPSet (MValue)
include PrettyPrintable.MakePPMonoMap (Pos) (MValueSet)

let joinable lhs rhs =
  fold
    (fun pos mval_lhs acc ->
      if acc then
        match find_opt pos rhs with Some mval_rhs when MValueSet.equal mval_lhs mval_rhs -> acc | _ -> false
      else acc)
    lhs true


let model = ref empty

let add_element pos mval t =
  match find_opt pos t with
  | Some mvalues ->
      add pos (MValueSet.add mval mvalues) t
  | None ->
      add pos (MValueSet.singleton mval) t
