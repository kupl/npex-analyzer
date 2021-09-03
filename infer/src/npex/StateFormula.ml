open! IStd
open! Vocab
module L = Logging
open SymDom
module Domain = SpecCheckerDomain
module Predicate = Constraint.Make (AccessExpr)
module Formula = Constraint.MakePC (AccessExpr)
module APSet = AbstractDomain.FiniteSet (AccessExpr)

module ExecutedCallExp = struct
  type t = AccessExpr.t * AccessExpr.t [@@deriving compare]

  let pp fmt (ret, fexp) = F.fprintf fmt "(%a, %a)" AccessExpr.pp ret AccessExpr.pp fexp
end

module ExecutedCallExps = PrettyPrintable.MakePPSet (ExecutedCallExp)

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
                  APSet.filter (not <<< AccessExpr.contains_method_access) arg_aps |> APSet.elements)
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
    | Loc.Field (Loc.Var pv, fn) when Pvar.is_global pv ->
        AccessExpr.append_access (AccessExpr.of_formal pv) (AccessExpr.FieldAccess fn) |> APSet.singleton
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

type t =
  { pc: Formula.t
  ; output: Formula.t
  ; local_output: Formula.t
  ; symbols: Val.Set.t
  ; uncaught_npes: APSet.t
  ; is_exceptional: bool
  ; executed_calls: ExecutedCallExps.t
  ; defined_aps: APSet.t }
[@@deriving compare]

let pp fmt {pc; output; symbols; uncaught_npes; local_output; defined_aps; executed_calls} =
  F.fprintf fmt
    "@[<v 2> - Formula:@,\
    \   %a@,\n\
    \     - Output:@,\
    \   %a@,\n\
    \     - Local Output:@,\
    \   %a@,\n\
    \     - Symbol used:@,\
    \   %a@,\n\
    \     - Executed calls:@,\
    \   %a@,\n\
    \     - Defined Exprs:@,\
    \   %a@,\n\
    \     - Uncaughted NPEs:@,\
    \   %a@,\
     @]"
    Formula.pp_set pc Formula.pp_set output Formula.pp_set local_output Val.Set.pp symbols ExecutedCallExps.pp
    executed_calls APSet.pp defined_aps APSet.pp uncaught_npes


let pp_executed_calls fmt {executed_calls} =
  F.fprintf fmt "@[<v 2> - Executed calls:@, %a@]@." ExecutedCallExps.pp executed_calls


let pp_local_output fmt {local_output} = F.fprintf fmt "@[<v 2> - Local output:@, %a@]@." Formula.pp local_output

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


let make_formula binop ap_set1 ap_set2 =
  let ap_pairs = List.cartesian_product (APSet.elements ap_set1) (APSet.elements ap_set2) in
  List.fold ~init:Formula.empty ap_pairs ~f:(fun acc (ap1, ap2) ->
      Formula.add (Predicate.make_physical_equals binop ap1 ap2) acc)


let encoding_memory ~is_local val_to_ap astate =
  Domain.Mem.fold
    (fun l v ->
      let aps_loc, aps_val = (ValToAP.find_loc l val_to_ap, ValToAP.find v val_to_ap) in
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
      let inequal_formula =
        let init =
          let null_aps = if Val.is_allocsite v then APSet.singleton AccessExpr.null else APSet.empty in
          make_formula Binop.Ne aps_val null_aps
        in
        List.fold (Domain.inequal_values astate v) ~init ~f:(fun acc v' ->
            let aps_val' = ValToAP.find v' val_to_ap in
            make_formula Binop.Ne aps_loc aps_val' |> Formula.join acc)
      in
      (* L.debug_dev "Formula: %a@." Formula.pp_set formula ; *)
      if is_local then Formula.join formula inequal_formula |> Formula.join else Formula.join formula)
    Domain.(astate.mem)
    Formula.empty


let from_state proc_desc (astate_local : Domain.t) : t =
  let astate_public =
    List.fold (Domain.Mem.bindings astate_local.mem) ~init:astate_local ~f:(fun acc (l, _) ->
        (* remove all local-variable assignment *)
        match l with
        | Loc.Var pv when Pvar.is_return pv ->
            acc
        | Loc.Var pv ->
            Domain.remove_pvar ~pv ~line:0 acc
        | _ ->
            acc)
  in
  let val_to_ap_public = do_worklist astate_public ValToAP.empty in
  let val_to_ap_local = do_worklist astate_local ValToAP.empty in
  (* L.progress "ValToAP: %a@." ValToAP.pp val_to_ap_public ; *)
  (* L.progress "=========================convert state ================@.%a@." Domain.pp astate ; *)
  let pc_formula =
    let pathcond_to_formula = function
      | Domain.PathCond.PEquals (v1, v2) ->
          let ap_set1, ap_set2 = (ValToAP.find v1 val_to_ap_public, ValToAP.find v2 val_to_ap_public) in
          L.debug_dev "from (%a = %a) to (%a = %a)@." Val.pp v1 Val.pp v2 APSet.pp ap_set1 APSet.pp ap_set2 ;
          make_formula Binop.Eq ap_set1 ap_set2
      | Domain.PathCond.Not (Domain.PathCond.PEquals (v1, v2)) ->
          let ap_set1, ap_set2 = (ValToAP.find v1 val_to_ap_public, ValToAP.find v2 val_to_ap_public) in
          make_formula Binop.Ne ap_set1 ap_set2
      | _ ->
          (* TODO: *)
          Formula.empty
    in
    let exception_cond = exception_cond proc_desc astate_public.is_exceptional in
    Domain.PC.PCSet.fold
      (fun pc -> pathcond_to_formula pc |> Formula.join)
      (Domain.PC.to_pc_set astate_public.pc) Formula.empty
    |> Formula.add exception_cond
  in
  (* L.progress "PC Formula %a@." Formula.pp_set pc_formula ; *)
  let output =
    let result = encoding_memory ~is_local:false val_to_ap_public astate_public in
    result
  in
  let local_output =
    let result = encoding_memory ~is_local:true val_to_ap_local astate_local in
    result
  in
  let uncaught_npes =
    let null_values = Domain.(astate_public.uncaught_npes) in
    let uncaught_npes =
      Val.Set.fold
        (fun v -> ValToAP.find v val_to_ap_public |> APSet.union)
        (Val.Set.of_list null_values) APSet.empty
    in
    if APSet.is_empty uncaught_npes then APSet.empty
    else (* redundant, but for equality *)
      APSet.add AccessExpr.null uncaught_npes
  in
  let symbols = Domain.collect_summary_symbols astate_public in
  let executed_calls =
    let executed_call_values = Domain.(astate_local.executed_calls) in
    ExecutedCalls.fold
      (fun (ret, fexp) ->
        (* let ret_aps = ValToAP.find ret val_to_ap_local in
           let fexps = ValToAP.find fexp val_to_ap_local in *)
        (* APSet.fold (fun ret_ap -> APSet.fold (fun f_ap -> ExecutedCallExps.add (ret_ap, f_ap)) fexps) ret_aps) *)
        match fexp with
        | Val.Vextern (callee, _) ->
            let method_call_access = AccessExpr.MethodCallAccess (callee, []) in
            let f_ap = AccessExpr.append_access AccessExpr.dummy method_call_access in
            let ret_ap = AccessExpr.dummy in
            ExecutedCallExps.add (ret_ap, f_ap)
        | _ ->
            fun x -> x)
      executed_call_values ExecutedCallExps.empty
    (* (ValToAP.find v val_to_ap |> APSet.union) executed_call_values APSet.empty *)
  in
  let defined_aps =
    Domain.Mem.fold
      (fun l v -> APSet.union (ValToAP.find_loc l val_to_ap_local))
      Domain.(astate_local.mem)
      APSet.empty
  in
  { pc= pc_formula
  ; output
  ; uncaught_npes
  ; is_exceptional= astate_public.is_exceptional
  ; symbols
  ; executed_calls
  ; local_output
  ; defined_aps }


let check_sat ?(print_unsat = false) (infered : t) (patched : t) =
  (* let pc_sat = Formula.check_sat ~print_unsat infered.pc patched.pc in
     let uncaught_sat = Bool.equal (APSet.is_empty infered.uncaught_npes) (APSet.is_empty patched.uncaught_npes) in *)
  (* pc_sat && uncaught_sat *)
  true


let filter_by_defined_aps ~is_local defined_aps formula =
  Formula.filter_by_value formula ~f:(fun ap -> (is_local && AccessExpr.is_formal ap) || APSet.mem ap defined_aps)


let check_valid ?(print_invalid = false) (infered : t) (patched : t) =
  let defined_aps = APSet.inter infered.defined_aps patched.defined_aps in
  let missing_output =
    (* FIXME: this is temporal fix for unalined formula *)
    let output1 = Formula.merge infered.pc patched.output in
    let output2 = Formula.merge patched.pc infered.output in
    Formula.join output1 output2
  in
  let infered_output =
    Formula.join missing_output infered.output |> filter_by_defined_aps ~is_local:false defined_aps
  in
  let patched_output =
    Formula.join missing_output patched.output |> filter_by_defined_aps ~is_local:false defined_aps
  in
  (* L.progress "check sat %a, %a@." Formula.pp_set infered.pc Formula.pp_set patched.pc ; *)
  let result =
    Formula.check_sat infered.pc patched.pc
    && Bool.equal (APSet.is_empty infered.uncaught_npes) (APSet.is_empty patched.uncaught_npes)
    && Formula.check_valid ~print_invalid infered_output patched_output
    && Val.Set.equal infered.symbols patched.symbols
    && APSet.subset
         (APSet.filter (fun ap -> APSet.mem ap defined_aps) patched.uncaught_npes)
         (APSet.filter (fun ap -> APSet.mem ap defined_aps) infered.uncaught_npes)
  in
  result


let check_syn_equiv (infered : t) (patched : t) =
  let defined_aps = APSet.inter infered.defined_aps patched.defined_aps in
  let infered_output = filter_by_defined_aps defined_aps ~is_local:true infered.local_output in
  let patched_output = filter_by_defined_aps defined_aps ~is_local:true patched.local_output in
  (* L.progress "Compare %a and %a on %a@.Acutial compare: %a, %a@." Formula.pp_set infered.local_output
     Formula.pp_set patched.local_output APSet.pp defined_aps Formula.pp_set infered_output Formula.pp_set
     patched_output ; *)
  check_valid infered patched
  && Formula.check_valid ~print_invalid:false infered_output patched_output
  && ExecutedCallExps.equal infered.executed_calls patched.executed_calls


let join lhs rhs =
  let pc = Formula.merge lhs.pc rhs.pc in
  let output = Formula.merge lhs.output rhs.output in
  let symbols = Val.Set.union lhs.symbols rhs.symbols in
  let uncaught_npes = APSet.union lhs.uncaught_npes rhs.uncaught_npes in
  let executed_calls = ExecutedCallExps.union lhs.executed_calls rhs.executed_calls in
  let local_output = Formula.merge lhs.local_output rhs.local_output in
  { pc
  ; output
  ; symbols
  ; uncaught_npes
  ; is_exceptional= lhs.is_exceptional
  ; executed_calls
  ; local_output
  ; defined_aps= APSet.inter lhs.defined_aps rhs.defined_aps }


let joinable lhs rhs = check_sat lhs rhs

let is_exceptional {is_exceptional} = is_exceptional

let from_state proc_desc astate =
  let result = from_state proc_desc astate in
  (* L.progress "@.========= State to Spec ===========@." ;
     L.progress "%a@.------------------------------Specification-------------------@." Domain.pp astate ;
     L.progress "%a@." pp result ; *)
  result
