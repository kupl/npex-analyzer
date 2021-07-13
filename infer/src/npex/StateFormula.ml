open! IStd
open! Vocab
module L = Logging
open SymDom
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)

module ValToAP = struct
  include WeakMap.Make (Val) (APSet)

  let find v t =
    let rec resolve v =
      let sub_aps =
        match v with
        | Val.Vheap (Null _) ->
            AccessExpr.null |> APSet.singleton
        | Val.Vheap (String str) ->
            AccessExpr.of_const (Const.Cstr str) |> APSet.singleton
        | Val.Vheap (Symbol s) ->
            Symbol.to_ap s |> APSet.singleton
        | Val.Vint (IntLit intlit) ->
            AccessExpr.of_const (Const.Cint intlit) |> APSet.singleton
        | Val.Vint (FloatLit flit) ->
            AccessExpr.of_const (Const.Cfloat flit) |> APSet.singleton
        | Val.Vint (Symbol s) ->
            APSet.singleton (Symbol.to_ap s)
        | Val.Vextern (callee, args) ->
            let make_ap_call callee arg_aps =
              let method_call_access = AccessExpr.MethodCallAccess (callee, arg_aps) in
              AccessExpr.append_access AccessExpr.dummy method_call_access
            in
            let aps_args_list =
              List.map args ~f:(fun arg_value ->
                  (* this recursive is ok because function value does not contain function value *)
                  let arg_aps = resolve arg_value in
                  APSet.elements arg_aps)
            in
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
            List.map arg_aps_list ~f:(make_ap_call callee) |> APSet.of_list
        | _ ->
            APSet.empty
      in
      APSet.union sub_aps (find v t)
    in
    resolve v


  let find_loc l t =
    match l with
    | Loc.Var pv when Pvar.is_return pv ->
        AccessExpr.of_formal pv |> APSet.singleton
    | Loc.Var pv ->
        (* Local predicate *)
        AccessExpr.of_pvar pv |> APSet.singleton
    | Loc.SymHeap sh ->
        find (Val.Vheap sh) t
    | Loc.Field (Loc.Var pv, fn) ->
        AccessExpr.append_access (AccessExpr.of_pvar pv) (AccessExpr.FieldAccess fn) |> APSet.singleton
    | Loc.Field (Loc.SymHeap sh, fn) ->
        let base_aps = find (Val.Vheap sh) t in
        APSet.map (fun base_ap -> AccessExpr.append_access base_ap (AccessExpr.FieldAccess fn)) base_aps
    | Loc.Index (Loc.Var pv, index) ->
        let index_aps = find (Val.Vint index) t in
        APSet.fold
          (fun index_ap ->
            AccessExpr.append_access (AccessExpr.of_pvar pv) (AccessExpr.ArrayAccess index_ap) |> APSet.add)
          index_aps APSet.empty
    | Loc.Index (Loc.SymHeap sh, index) ->
        let base_aps = find (Val.Vheap sh) t in
        let index_aps = find (Val.Vint index) t in
        let append_index base_ap index_ap =
          AccessExpr.append_access base_ap (AccessExpr.ArrayAccess index_ap) |> APSet.add
        in
        APSet.fold (fun base_ap -> APSet.fold (append_index base_ap) index_aps) base_aps APSet.empty
    | _ ->
        APSet.empty


  let weak_update v aps t =
    let aps = APSet.filter (not <<< AccessExpr.has_duplicates) aps in
    if not (mem v t) then weak_update v (APSet.union aps (find v t)) t else weak_update v aps t
end

type t = Formula.t * Formula.t * APSet.t [@@deriving compare]

(* let pp fmt (pc_formula, state_formula) =
  F.fprintf fmt "== PC Formula ==@.%a@.== State Formula ==@.%a@." Formula.PCSet.pp (Formula.to_pc_set pc_formula)
    Formula.PCSet.pp (Formula.to_pc_set state_formula) *)

let do_work Domain.{mem; pc= Domain.PC.{const_map; pc_set}} val_to_ap : ValToAP.t =
  Domain.Mem.fold
    (fun l v ->
      if Val.is_abstract v then function x -> x else ValToAP.weak_update v (ValToAP.find_loc l val_to_ap))
    mem val_to_ap
  |> Domain.PC.ConstMap.fold (fun v c -> ValToAP.weak_update v (ValToAP.find c val_to_ap)) const_map
  |> Domain.PC.PCSet.fold
       (function
         | Domain.PathCond.PEquals (v1, v2) ->
             ValToAP.weak_update v1 (ValToAP.find v2 val_to_ap)
             <<< ValToAP.weak_update v2 (ValToAP.find v1 val_to_ap)
         | _ -> (
             function x -> x ))
       pc_set


let rec do_worklist astate acc =
  let acc' = do_work astate acc in
  if ValToAP.equal APSet.equal acc acc' then acc else do_worklist astate acc'


let exception_cond proc_desc is_exceptional =
  let ab_ret_var = Pvar.mk_abduced_ret (Procdesc.get_proc_name proc_desc) Location.dummy in
  let is_true = if is_exceptional then AccessExpr.one else AccessExpr.zero in
  Predicate.make_physical_equals Binop.Eq (AccessExpr.of_pvar ab_ret_var) is_true


let from_state proc_desc (Domain.{pc; mem; is_exceptional} as astate) : Formula.t * Formula.t * APSet.t =
  let make_formula binop ap_set1 ap_set2 =
    let ap_pairs = List.cartesian_product (APSet.elements ap_set1) (APSet.elements ap_set2) in
    List.fold ~init:Formula.empty ap_pairs ~f:(fun acc (ap1, ap2) ->
        Formula.add (Predicate.make_physical_equals binop ap1 ap2) acc)
  in
  let val_to_ap = do_worklist astate ValToAP.empty in
  L.progress "ValToAP: %a@." ValToAP.pp val_to_ap ;
  (* L.progress "=========================convert state ================@.%a@." Domain.pp astate ; *)
  let pc_formula =
    let pathcond_to_formula = function
      | Domain.PathCond.PEquals (v1, v2) ->
          let ap_set1, ap_set2 = (ValToAP.find v1 val_to_ap, ValToAP.find v2 val_to_ap) in
          (* L.debug_dev "from (%a = %a) to (%a = %a)@." Val.pp v1 Val.pp v2 APSet.pp ap_set1 APSet.pp ap_set2 ; *)
          make_formula Binop.Eq ap_set1 ap_set2
      | Domain.PathCond.Not (Domain.PathCond.PEquals (v1, v2)) ->
          let ap_set1, ap_set2 = (ValToAP.find v1 val_to_ap, ValToAP.find v2 val_to_ap) in
          make_formula Binop.Ne ap_set1 ap_set2
      | _ ->
          (* TODO: *)
          Formula.empty
    in
    let exception_cond = exception_cond proc_desc is_exceptional in
    Domain.PC.PCSet.fold
      (fun pc -> pathcond_to_formula pc |> Formula.join)
      (Domain.PC.get_branches pc) Formula.empty
    |> Formula.add exception_cond
  in
  let summary_formula =
    let astate' =
      List.fold (Domain.Mem.bindings mem) ~init:astate ~f:(fun acc (l, _) ->
          (* remove all local-variable assignment *)
          match l with
          | Loc.Var pv when Pvar.is_return pv ->
              acc
          | Loc.Var pv ->
              Domain.remove_pvar ~pv ~line:0 acc
          | _ ->
              acc)
    in
    let val_to_ap' = do_worklist astate' ValToAP.empty in
    let result =
      Domain.Mem.fold
        (fun l v ->
          let aps_loc, aps_val = (ValToAP.find_loc l val_to_ap', ValToAP.find v val_to_ap') in
          (* L.debug_dev "from (%a -> %a) to (%a = %a)@." Loc.pp l Val.pp v APSet.pp aps_loc APSet.pp aps_val ; *)
          let formula =
            make_formula Binop.Eq aps_loc aps_val
            |> Formula.filter ~f:(function
                 | Predicate.PEquals (v1, v2) ->
                     (* prestate information could be different whether a pointer is used or not. 
                      * e.g., local-variable = param just instroduces param = $param *)
                     not (AccessExpr.equal_wo_formal v1 v2)
                 | _ ->
                     true)
          in
          Formula.join formula)
        Domain.(astate'.mem)
        Formula.empty
    in
    Formula.diff result pc_formula
  in
  let uncaught_npes =
    let null_values = Domain.(astate.uncaught_npes) in
    Val.Set.fold (fun v -> ValToAP.find v val_to_ap |> APSet.union) (Val.Set.of_list null_values) APSet.empty
  in
  (pc_formula, summary_formula, uncaught_npes)
