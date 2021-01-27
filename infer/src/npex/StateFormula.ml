open! IStd
open! Vocab
module L = Logging
module Loc = SymDom.Loc
module Val = SymDom.Val
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)

type t = Formula.t * Formula.t [@@deriving compare]

let pp fmt (pc_formula, state_formula) =
  F.fprintf fmt "- PC Formula: %a@. - State Formula: %a@." Formula.pp pc_formula Formula.pp state_formula


let loc_to_access_expr mem l =
  let rec _loc_to_access_expr l fields_to_append =
    match l with
    | Loc.Var pv ->
        APSet.singleton (AccessExpr.of_pvar pv)
    | Loc.Field (_, fld) when List.mem fields_to_append (AccessExpr.FieldAccess fld) ~equal:AccessExpr.equal_access
      ->
        APSet.empty
    | Loc.Field (l', fld) ->
        _loc_to_access_expr l' (AccessExpr.FieldAccess fld :: fields_to_append)
    | Loc.Index _ ->
        APSet.empty
    | Loc.SymHeap sh ->
        symHeap_to_access_expr sh fields_to_append
  and symHeap_to_access_expr sh fields_to_append : APSet.t =
    Domain.Mem.fold
      (fun l v acc ->
        if SymDom.Val.equal v (SymDom.Val.of_symheap sh) then
          APSet.union acc (_loc_to_access_expr l fields_to_append)
        else acc)
      mem APSet.empty
  in
  _loc_to_access_expr l []


(* IOption.if_none_evalopt
   ~f:(fun () ->
     L.debug_dev
       "Could not convert %a to access expr@.(Memory does not contain any location whose value matches with \
        the symbolic heap)"
       SymDom.SymHeap.pp sh ;
     None)
   ae *)

let from_state proc_desc (Domain.{pc; mem} as astate) : Formula.t * Formula.t =
  let val_to_ap : Val.t -> APSet.t = function
    | Val.Vint SymDom.SymExp.(IntLit intlit) ->
        APSet.singleton (AccessExpr.of_const (Const.Cint intlit))
    | (Val.Vint SymDom.SymExp.(Symbol _) | Val.Vint SymDom.SymExp.(Extern _)) as v ->
        Domain.Mem.fold
          (fun l v' acc -> if SymDom.Val.equal v' v then APSet.union acc (loc_to_access_expr mem l) else acc)
          mem APSet.empty
    | Val.Vint _ ->
        APSet.empty
    | Val.Vheap SymDom.SymHeap.(Null _) ->
        APSet.singleton AccessExpr.null
    | Val.Vheap SymDom.SymHeap.(String str) ->
        APSet.singleton (AccessExpr.of_const (Const.Cstr str))
    | Val.Vheap sh ->
        loc_to_access_expr mem (Loc.SymHeap sh)
    | Val.Vexn _ ->
        (* TODO *) APSet.empty
    | _ ->
        APSet.empty
  in
  let make_formula binop ap_set1 ap_set2 =
    let ap_pairs = List.cartesian_product (APSet.elements ap_set1) (APSet.elements ap_set2) in
    List.map ap_pairs ~f:(fun (ap1, ap2) -> Predicate.make_physical_equals binop ap1 ap2) |> Formula.of_list
  in
  let summary_formula =
    let filter_local = APSet.filter (not <<< AccessExpr.is_local proc_desc) in
    Domain.Mem.fold
      (fun l v ->
        let aps_loc, aps_val = (loc_to_access_expr mem l, val_to_ap v) in
        make_formula Binop.Eq (filter_local aps_loc) (filter_local aps_val) |> Formula.union)
      mem Formula.empty
  in
  let pc_formula =
    let rec pathcond_to_formula = function
      | Domain.PathCond.PEquals (v1, v2) ->
          let ap_set1, ap_set2 = (val_to_ap v1, val_to_ap v2) in
          make_formula Binop.Eq ap_set1 ap_set2
      | Domain.PathCond.Not pc ->
          pathcond_to_formula pc |> Formula.map Predicate.make_negation
      | Domain.PathCond.Equals _ ->
          (* TODO: *)
          Formula.empty
    in
    Domain.PC.fold (fun pc -> pathcond_to_formula pc |> Formula.union) pc Formula.empty
  in
  let debug_msg =
    F.asprintf
      "===== State to pc * output =====@. - Original state: %a@. - Summary Formula: %a@. - PC Formula: %a@. \
       ==============================@."
      Domain.pp astate Formula.pp summary_formula Formula.pp pc_formula
  in
  (* L.progress "%s" debug_msg ;  *)
  (pc_formula, summary_formula)
