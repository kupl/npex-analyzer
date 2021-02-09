open! IStd
open! Vocab
module L = Logging
module Loc = SymDom.Loc
module Val = SymDom.Val
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)
module APMap = WeakMap.Make (Loc) (APSet)
module LocMap = WeakMap.Make (Loc) (Loc.Set)

type t = Formula.t * Formula.t [@@deriving compare]

let pp fmt (pc_formula, state_formula) =
  F.fprintf fmt "- PC Formula: %a@. - State Formula: %a@." Formula.pp pc_formula Formula.pp state_formula


let compute_ap_map formals mem =
  let field_map =
    Domain.Mem.fold
      (fun l _ acc ->
        match l with
        | Loc.Field (l', _) ->
            LocMap.weak_update l' (Loc.Set.singleton l) acc
        | Loc.Index l' ->
            LocMap.weak_update l' (Loc.Set.singleton l) acc
        | _ ->
            acc)
      mem LocMap.empty
  in
  let rec _compute worklist ap_map =
    if Loc.Set.is_empty worklist then ap_map
    else
      let work = Loc.Set.choose worklist in
      let rest = Loc.Set.remove work worklist in
      let cur_aps = APMap.find work ap_map in
      let next_aps =
        match work with
        | Loc.Var (pv, _) ->
            (* add (pv, []) *)
            APSet.singleton (AccessExpr.of_pvar pv)
        | Loc.Field (l, fn) ->
            (* add ap_map(l).fn *)
            APSet.fold
              (fun ap next_aps_acc ->
                let[@warning "-8"] (AccessExpr.AccessExpr (_, accesses)) = ap in
                if List.mem accesses (AccessExpr.FieldAccess fn) ~equal:AccessExpr.equal_access then next_aps_acc
                else APSet.add (AccessExpr.append_access ap (AccessExpr.FieldAccess fn)) next_aps_acc)
              (APMap.find l ap_map) APSet.empty
        | Loc.Index _ ->
            (* TODO: skip *)
            APSet.empty
        | Loc.SymHeap symheap ->
            (* for all l' -> l. add ap_map(l') *)
            let locs_ptsto_work =
              Domain.Mem.fold
                (fun l v acc -> if Val.equal v (Val.of_symheap symheap) then Loc.Set.add l acc else acc)
                mem Loc.Set.empty
            in
            Loc.Set.fold (fun l -> APMap.find l ap_map |> APSet.union) locs_ptsto_work APSet.empty
      in
      if Int.equal (APSet.cardinal cur_aps) (APSet.cardinal next_aps) then _compute rest ap_map
      else
        let next_locs =
          let field_locs = LocMap.find work field_map in
          ( match Domain.Mem.find work mem with
          | Val.Vheap symheap ->
              Loc.Set.add (Loc.SymHeap symheap) field_locs
          | _ ->
              field_locs )
          |> Loc.Set.filter (not <<< Loc.is_unknown)
        in
        let next_works = Loc.Set.union rest next_locs in
        let next_ap_map = APMap.strong_update work next_aps ap_map in
        _compute next_works next_ap_map
  in
  let init =
    Domain.Mem.fold
      (fun l _ acc ->
        match l with
        | (Loc.Var (pv, _) | Loc.Field (Loc.Var (pv, _), _)) when Pvar.is_global pv ->
            (* Global variable may have no pvar as location *)
            Loc.Set.add l acc
        | Loc.Var (pv, _) when List.mem formals pv ~equal:Pvar.equal ->
            Loc.Set.add l acc
        | _ ->
            acc)
      mem Loc.Set.empty
  in
  _compute init APMap.empty


let rec val_to_ap mem ap_map : Val.t -> APSet.t = function
  | Val.Vint SymDom.SymExp.(IntLit intlit) ->
      APSet.singleton (AccessExpr.of_const (Const.Cint intlit))
  | (Val.Vint SymDom.SymExp.(Symbol _) | Val.Vint SymDom.SymExp.(Extern _)) as v ->
      Domain.Mem.fold
        (fun l v' acc -> if SymDom.Val.equal v' v then APSet.union acc (APMap.find l ap_map) else acc)
        mem APSet.empty
  | Val.Vint _ ->
      APSet.empty
  | Val.Vheap SymDom.SymHeap.(Null _) ->
      APSet.singleton AccessExpr.null
  | Val.Vheap SymDom.SymHeap.(String str) ->
      APSet.singleton (AccessExpr.of_const (Const.Cstr str))
  | Val.Vheap sh ->
      APMap.find (Loc.SymHeap sh) ap_map
  | Val.Vexn sh -> (
    match Val.get_class_name_opt (Val.Vheap sh) with
    | Some cls ->
        AccessExpr.of_const (Const.Cstr (Typ.Name.to_string cls)) |> APSet.singleton
    | None ->
        APSet.empty )
  | Val.Vextern (callee, args) ->
      let make_ap_call callee arg_aps =
        let method_call_access = AccessExpr.MethodCallAccess (callee, arg_aps) in
        AccessExpr.append_access AccessExpr.dummy method_call_access
      in
      let aps_args_list = List.map args ~f:(fun arg_value -> val_to_ap mem ap_map arg_value |> APSet.elements) in
      let arg_aps_list =
        (* [v1, v2]: args
         * [[ap11, ap12], [ap21, ap22]]: aps_args_list
         * [ap11, ap21], [ap11, ap22], [ap12, ap21], [ap12, ap22]: arg_aps_list *)
        List.fold aps_args_list ~init:[[]]
          ~f:(fun (acc : AccessExpr.t list list) (aps : AccessExpr.t list) : AccessExpr.t list list ->
            List.concat_map acc ~f:(fun arg_list -> List.map aps ~f:(fun ap -> arg_list @ [ap])))
        (* [ap11], [ap12] 
         * [ap11, ap21], [ap11, ap21] | [ap12, ap21], [ap12, ap22] *)
      in
      let results = List.map arg_aps_list ~f:(make_ap_call callee) |> APSet.of_list in
      results
  | _ ->
      APSet.empty


let from_state proc_desc (Domain.{pc; mem} as astate) : Formula.t * Formula.t =
  let formal_pvars = Procdesc.get_ret_var proc_desc :: (Procdesc.get_pvar_formals proc_desc |> List.map ~f:fst) in
  let ap_map = compute_ap_map formal_pvars mem in
  let make_formula binop ap_set1 ap_set2 =
    let ap_pairs = List.cartesian_product (APSet.elements ap_set1) (APSet.elements ap_set2) in
    List.map ap_pairs ~f:(fun (ap1, ap2) -> Predicate.make_physical_equals binop ap1 ap2) |> Formula.of_list
  in
  let summary_formula =
    let filter_local = APSet.filter (not <<< AccessExpr.is_local proc_desc) in
    Domain.Mem.fold
      (fun l v ->
        let aps_loc, aps_val = (APMap.find l ap_map, val_to_ap mem ap_map v) in
        (* L.debug_dev "@. - make %a = %a@." APSet.pp aps_loc APSet.pp aps_val ; *)
        let formula = make_formula Binop.Eq (filter_local aps_loc) (filter_local aps_val) in
        (* L.debug_dev " - formula : %a@." Formula.pp formula ; *)
        Formula.union formula)
      mem Formula.empty
  in
  let pc_formula =
    let rec pathcond_to_formula = function
      | Domain.PathCond.PEquals (v1, v2) ->
          let ap_set1, ap_set2 = (val_to_ap mem ap_map v1, val_to_ap mem ap_map v2) in
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
  if Config.debug_mode then L.progress "%s" debug_msg ;
  (pc_formula, summary_formula)
