open! IStd
open! Vocab
module L = Logging
module Loc = SymDom.Loc
module Val = SymDom.Val
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)
module AliasMap = WeakMap.Make (Val) (APSet)

let state_to_pc proc_desc (Domain.{pc; mem} as astate) : Formula.t * Formula.t =
  let rec loc_to_access_expr mem : Loc.t -> APSet.t = function
    | Loc.Var pv ->
        APSet.singleton (AccessExpr.of_pvar pv)
    | Loc.Field (l', fld) ->
        let base = loc_to_access_expr mem l' in
        APSet.map (fun base -> AccessExpr.append_access base (AccessExpr.FieldAccess fld)) base
    | Loc.Index _ ->
        APSet.empty
    | Loc.SymHeap sh ->
        symHeap_to_access_expr mem sh
  and symHeap_to_access_expr mem sh : APSet.t =
    Domain.Mem.fold
      (fun l v acc ->
        if SymDom.Val.equal v (SymDom.Val.of_symheap sh) then APSet.union acc (loc_to_access_expr mem l) else acc)
      mem APSet.empty
    (* IOption.if_none_evalopt
       ~f:(fun () ->
         L.debug_dev
           "Could not convert %a to access expr@.(Memory does not contain any location whose value matches with \
            the symbolic heap)"
           SymDom.SymHeap.pp sh ;
         None)
       ae *)
  in
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
        symHeap_to_access_expr mem sh
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
  L.progress "%s" debug_msg ; (pc_formula, summary_formula)


let verify proc_desc summary_inferenced summary_patched =
  let specs_inferenced, specs_patched =
    ( List.filter summary_inferenced ~f:Domain.is_npe_alternative |> List.map ~f:(state_to_pc proc_desc)
    , List.filter summary_patched ~f:Domain.is_npe_alternative |> List.map ~f:(state_to_pc proc_desc) )
  in
  (not (List.is_empty specs_inferenced))
  && List.for_all specs_inferenced ~f:(fun spec_inferenced ->
         let pc_inferenced, state_inferenced = spec_inferenced in
         let satisfiable_specs = List.filter specs_patched ~f:(Formula.check_sat pc_inferenced <<< fst) in
         (not (List.is_empty satisfiable_specs))
         && List.for_all satisfiable_specs ~f:(Formula.check_valid state_inferenced <<< snd))


let launch ~get_summary ~get_original_summary =
  let program = Program.build () in
  let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
  let target_proc = Patch.get_method patch in
  let target_pdesc = Program.pdesc_of program target_proc in
  let summary_inferenced : Domain.t list = get_original_summary target_proc in
  let summary_patched : Domain.t list = get_summary target_proc in
  let result = verify target_pdesc summary_inferenced summary_patched in
  if result then (
    L.progress "[SUCCESS]: the patch is verified w.r.t. specification@." ;
    L.exit 0 )
  else (
    L.progress "[FAIL]: the patch does not satisfy specification@." ;
    L.exit 1 )
