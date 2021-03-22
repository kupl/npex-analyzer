open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
module Loc = Domain.Loc
module SymHeap = SymDom.SymHeap
module Val = Domain.Val
module ValSet = AbstractDomain.FiniteSet (Val)
module Mem = Domain.Mem
module PC = Domain.PC
module APSet = AbstractDomain.FiniteSet (AccessExpr)

module ValueFeature = struct
  type t = Ftrue | Ffalse | Fnull | Fnonnull [@@deriving compare]

  let to_string = function Ftrue -> "TRUE" | Ffalse -> "FALSE" | Fnull -> "NULL" | Fnonnull -> "NonNull"

  let pp = Pp.of_string ~f:to_string
end

module PreFeatures = struct
  type t = {true_values: Val.Set.t; false_values: Val.Set.t; null_values: Val.Set.t; non_null_values: Val.Set.t}
  [@@deriving compare]

  let empty : t =
    { true_values= Val.Set.empty
    ; false_values= Val.Set.empty
    ; null_values= Val.Set.empty
    ; non_null_values= Val.Set.empty }


  let pp fmt {true_values; false_values; null_values; non_null_values} =
    F.fprintf fmt "   - true_values: %a@,   - false_values: %a@,   - null_values: %a@,   - non_null_values: %a"
      Val.Set.pp true_values Val.Set.pp false_values Val.Set.pp null_values Val.Set.pp non_null_values


  let add t v : ValueFeature.t -> t = function
    | Ftrue ->
        {t with true_values= Val.Set.add v t.true_values}
    | Ffalse ->
        {t with false_values= Val.Set.add v t.false_values}
    | Fnull ->
        {t with null_values= Val.Set.add v t.null_values}
    | Fnonnull ->
        {t with non_null_values= Val.Set.add v t.non_null_values}


  let is_important_value = (* TODO: only formal.field or ap field *) Val.is_symbolic

  let from_state proc_desc astate : t =
    let all_values = SpecCheckerDomain.all_values astate in
    let symbolic_values = Val.Set.filter is_important_value all_values in
    Val.Set.fold
      (fun v acc ->
        let equal_values = Domain.equal_values astate v in
        let value_feature_opt =
          List.find_map equal_values ~f:(fun v' ->
              if Val.is_true v' then Some ValueFeature.Ftrue
              else if Val.is_false v' then Some ValueFeature.Ffalse
              else if Val.is_null v' then Some ValueFeature.Fnull
              else None)
        in
        match value_feature_opt with
        | Some value_feature ->
            add acc v value_feature
        | None when List.exists (Domain.inequal_values astate v) ~f:Val.is_null ->
            add acc v Fnonnull
        | None ->
            acc)
      symbolic_values empty
end

module PostFeatures = struct
  type t =
    { return_value: Val.t option
    ; npe_alternative: bool
    ; exceptional: bool
    ; non_null_locs: Loc.Set.t
    ; null_locs: Loc.Set.t }
  [@@deriving compare]

  let pp fmt {return_value; non_null_locs; null_locs} =
    let return_value_str =
      match return_value with Some v -> F.asprintf "   - return_value : %a" Val.pp v | None -> ""
    in
    F.fprintf fmt "   - null_locs: %a@,   - non_null_locs: %a@,%s" Loc.Set.pp null_locs Loc.Set.pp non_null_locs
      return_value_str


  let is_important_loc = function
    | Loc.Var pv ->
        Pvar.is_return pv
    | Loc.Field (Loc.Var gv, _) | Loc.Index (Loc.Var gv, _) ->
        Pvar.is_global gv
    | Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _) ->
        SymHeap.is_symbolic sh
    | _ ->
        false


  let from_state proc_desc astate =
    let ret_var = Procdesc.get_ret_var proc_desc in
    let return_value =
      let value = Domain.read_loc astate (Loc.of_pvar ret_var) in
      if Val.is_constant value then Some value else None
    in
    let null_locs =
      let is_null astate v = List.exists (Domain.equal_values astate v) ~f:Val.is_null in
      Mem.fold
        (fun l v acc -> if is_important_loc l && is_null astate v then Loc.Set.add l acc else acc)
        Domain.(astate.mem)
        Loc.Set.empty
    in
    let non_null_locs =
      let is_non_null astate v = List.exists (Domain.inequal_values astate v) ~f:Val.is_null in
      Mem.fold
        (fun l v acc -> if is_important_loc l && is_non_null astate v then Loc.Set.add l acc else acc)
        Domain.(astate.mem)
        Loc.Set.empty
    in
    let npe_alternative = Domain.is_npe_alternative astate in
    let exceptional = Domain.is_exceptional astate in
    {null_locs; return_value; npe_alternative; exceptional; non_null_locs}
end

type t = PreFeatures.t * PostFeatures.t [@@deriving compare]

let from_state proc_desc astate : t =
  (PreFeatures.from_state proc_desc astate, PostFeatures.from_state proc_desc astate)


let pp fmt (prefeatures, postfeatures) =
  F.fprintf fmt "===== Pre Features =====@,%a@,===== Post Features =====@,%a" PreFeatures.pp prefeatures
    PostFeatures.pp postfeatures
