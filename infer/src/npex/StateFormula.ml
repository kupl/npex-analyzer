open! IStd
open! Vocab
module L = Logging
open SymDom
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)

type t = Formula.t * Formula.t [@@deriving compare]

let pp fmt (pc_formula, state_formula) =
  F.fprintf fmt "== PC Formula ==@.%a@.== State Formula ==@.%a@." Formula.pp pc_formula Formula.pp state_formula


let symbol_to_ap : Symbol.t -> AccessExpr.t =
  let append_symbol_access aexpr = function
    | Symbol.Field fn ->
        AccessExpr.append_access aexpr (AccessExpr.FieldAccess fn)
    | Symbol.Index intlit ->
        AccessExpr.append_access aexpr (AccessExpr.ArrayAccess (AccessExpr.of_const (Cint intlit)))
  in
  function
  | Symbol.Global (pv, access), accesses ->
      List.fold (access :: accesses) ~init:(AccessExpr.of_formal pv) ~f:append_symbol_access
  | Symbol.Param pv, accesses ->
      List.fold accesses ~init:(AccessExpr.of_formal pv) ~f:append_symbol_access


let rec symheap_to_ap astate : SymHeap.t -> APSet.t =
  let open SymDom in
  (* TODO: find ap recursively, but without infinite-loop *)
  let var_aps_of sh =
    Domain.Mem.fold
      (fun l v acc ->
        if Loc.is_concrete l && Val.equal v (Val.of_symheap sh) then APSet.union (loc_to_ap astate l) acc else acc)
      Domain.(astate.mem)
      APSet.empty
  in
  function
  | SymHeap.Allocsite _ as sh ->
      let var_aps = var_aps_of sh in
      (* allociste => type *)
      (* match SymHeap.get_class_name_opt sh with
         | Some name ->
             let alloc_str = F.asprintf "%a" Typ.Name.pp name in
             Const.Cstr alloc_str |> AccessExpr.of_const |> APSet.singleton |> APSet.union var_aps
         | None -> *)
      var_aps
  | SymHeap.Extern _ as sh ->
      (* extern => constant values *)
      let var_aps = var_aps_of sh in
      let equal_values = Domain.equal_values astate (Val.Vheap sh) |> List.filter ~f:Val.is_constant in
      List.fold equal_values ~init:var_aps ~f:(fun acc v -> APSet.union acc (val_to_ap astate v))
  | SymHeap.Null _ ->
      APSet.singleton AccessExpr.null
  | SymHeap.String str ->
      APSet.singleton (AccessExpr.of_const (Const.Cstr str))
  | SymHeap.Symbol s ->
      APSet.singleton (symbol_to_ap s)
  | _ ->
      APSet.empty


and symexp_to_ap astate : SymExp.t -> APSet.t =
  (* TODO: find ap recursively, but without infinite-loop *)
  let var_aps_of symexp =
    Domain.Mem.fold
      (fun l v acc ->
        if Loc.is_concrete l && Val.equal v (Val.of_symexp symexp) then APSet.union (loc_to_ap astate l) acc
        else acc)
      Domain.(astate.mem)
      APSet.empty
  in
  function
  | SymExp.IntLit intlit ->
      APSet.singleton (AccessExpr.of_const (Const.Cint intlit))
  | SymExp.FloatLit flit ->
      APSet.singleton (AccessExpr.of_const (Const.Cfloat flit))
  | SymExp.Symbol s ->
      APSet.singleton (symbol_to_ap s)
  | SymExp.Extern _ as symexp ->
      (* extern => constant values *)
      let var_aps = var_aps_of symexp in
      let equal_values = Domain.equal_values astate (Val.Vint symexp) |> List.filter ~f:Val.is_constant in
      List.fold equal_values ~init:var_aps ~f:(fun acc v -> APSet.union acc (val_to_ap astate v))
  | _ ->
      APSet.empty


and loc_to_ap astate : Loc.t -> APSet.t = function
  | Loc.Var pv when Pvar.is_return pv ->
      APSet.singleton (AccessExpr.of_formal pv)
  | Loc.Var pv ->
      (* Local predicate *)
      APSet.singleton (AccessExpr.of_pvar pv)
  | Loc.SymHeap sh ->
      symheap_to_ap astate sh
  | Loc.Field (l, fn) ->
      let base_aps = loc_to_ap astate l in
      APSet.map (fun base_ap -> AccessExpr.append_access base_ap (AccessExpr.FieldAccess fn)) base_aps
  | Loc.Index (l, index) ->
      let base_aps = loc_to_ap astate l in
      let index_aps = symexp_to_ap astate index in
      let append_index base_ap index_ap =
        AccessExpr.append_access base_ap (AccessExpr.ArrayAccess index_ap) |> APSet.add
      in
      APSet.fold (fun base_ap -> APSet.fold (append_index base_ap) index_aps) base_aps APSet.empty
  | _ ->
      APSet.empty


and val_to_ap astate : Val.t -> APSet.t = function
  | Val.Vint symexp ->
      symexp_to_ap astate symexp
  | Val.Vheap sh ->
      symheap_to_ap astate sh
  | Val.Vexn (Val.Vheap (SymHeap.String str)) ->
      (* Modeled exception (e.g., uncaught NPE) *)
      AccessExpr.of_const (Const.Cstr (F.asprintf "Exn:%s" str)) |> APSet.singleton
  | Val.Vexn _ ->
      (* TODO: modeling exn heap by type *)
      AccessExpr.of_const (Const.Cstr "Exn") |> APSet.singleton
      (* ( match Val.get_class_name_opt (Val.Vheap sh) with
         | Some cls ->
             AccessExpr.of_const (Const.Cstr (Typ.Name.to_string cls)) |> APSet.singleton
         | None ->
             APSet.empty ) *)
  | Val.Vextern (callee, args) ->
      let make_ap_call callee arg_aps =
        let method_call_access = AccessExpr.MethodCallAccess (callee, arg_aps) in
        AccessExpr.append_access AccessExpr.dummy method_call_access
      in
      let aps_args_list =
        List.map args ~f:(fun arg_value ->
            let arg_aps = val_to_ap astate arg_value in
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
      let results = List.map arg_aps_list ~f:(make_ap_call callee) |> APSet.of_list in
      results
  | _ ->
      APSet.empty


let from_state proc_desc (Domain.{pc; mem; is_exceptional} as astate) : Formula.t * Formula.t =
  let make_formula binop ap_set1 ap_set2 =
    let ap_pairs = List.cartesian_product (APSet.elements ap_set1) (APSet.elements ap_set2) in
    List.fold ~init:Formula.empty ap_pairs ~f:(fun acc (ap1, ap2) ->
        Formula.add (Predicate.make_physical_equals binop ap1 ap2) acc)
  in
  let summary_formula =
    let filter_local = APSet.filter (not <<< AccessExpr.is_local proc_desc) in
    (* let filter_local = APSet.filter (fun _ -> true) in *)
    Domain.Mem.fold
      (fun l v ->
        let aps_loc, aps_val = (loc_to_ap astate l, val_to_ap astate v) in
        (* L.debug_dev "@. - make %a = %a@." APSet.pp aps_loc APSet.pp aps_val ; *)
        let formula = make_formula Binop.Eq (filter_local aps_loc) (filter_local aps_val) in
        (* L.debug_dev " - formula : %a@." Formula.pp formula ; *)
        Formula.join formula)
      mem Formula.empty
  in
  let pc_formula =
    let pathcond_to_formula = function
      | Domain.PathCond.PEquals (v1, v2) ->
          let ap_set1, ap_set2 = (val_to_ap astate v1, val_to_ap astate v2) in
          make_formula Binop.Eq ap_set1 ap_set2
      | Domain.PathCond.Not (Domain.PathCond.PEquals (v1, v2)) ->
          let ap_set1, ap_set2 = (val_to_ap astate v1, val_to_ap astate v2) in
          make_formula Binop.Ne ap_set1 ap_set2
      | _ ->
          (* TODO: *)
          Formula.empty
    in
    let exception_cond =
      let ab_ret_var = Pvar.mk_abduced_ret (Procdesc.get_proc_name proc_desc) Location.dummy in
      let is_true = if is_exceptional then AccessExpr.one else AccessExpr.zero in
      Predicate.make_physical_equals Binop.Eq (AccessExpr.of_pvar ab_ret_var) is_true
    in
    Domain.PC.PCSet.fold (fun pc -> pathcond_to_formula pc |> Formula.join) (Domain.PC.to_pc_set pc) Formula.empty
    |> Formula.add exception_cond
  in
  let debug_msg =
    F.asprintf
      "===== State to pc * output =====@. - Original state: %a@. - Summary Formula: %a@. - PC Formula: %a@. \
       ==============================@."
      Domain.pp astate Formula.pp summary_formula Formula.pp pc_formula
  in
  if Config.debug_mode then L.progress "%s" debug_msg ;
  (pc_formula, summary_formula)
