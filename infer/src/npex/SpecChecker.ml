open! Vocab
module F = Format
module L = Logging
module CFG = ProcCfg.Exceptional
module Node = InstrNode
module Summary = SpecCheckerSummary

module DisjReady = struct
  module CFG = CFG
  module Domain = SpecCheckerDomain

  type analysis_data =
    {program: Program.t; interproc: SpecCheckerSummary.t InterproceduralAnalysis.t; patch: Patch.t option}

  let analysis_data interproc : analysis_data =
    let program = Program.from_marshal () in
    match Utils.read_json_file Config.npex_patch_json_name with
    | Ok _ ->
        let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
        {program; interproc; patch= Some patch}
    | Error _ ->
        {program; interproc; patch= None}


  let check_npe_alternative {patch} node instr astate =
    match patch with
    | Some {conditional= Some (null_cond, _)} when InstrNode.equal null_cond (InstrNode.of_pnode node instr) ->
        Domain.mark_npe_alternative astate
    | _ ->
        astate


  let init_uninitialized_fields mthd arg_typs node instr astate =
    let cls = Procname.Java.get_class_type_name mthd in
    match Tenv.load_global () with
    | Some tenv -> (
      match Tenv.lookup tenv cls with
      | Some Struct.{fields} ->
          let base_exp, _ = List.hd_exn arg_typs in
          let base_loc = Domain.eval_lv astate base_exp in
          List.fold fields ~init:astate ~f:(fun acc (fn, fn_typ, _) ->
              let field_loc = Domain.Loc.append_field ~fn base_loc in
              if Domain.is_unknown_loc acc field_loc then
                let instr_node = InstrNode.of_pnode node instr in
                Domain.store_loc acc field_loc (Domain.Val.get_default_by_typ instr_node fn_typ)
              else acc)
      | None ->
          astate )
    | None ->
        astate


  let exec_prune astate node instr bexp =
    try
      let pathcond =
        match bexp with
        | Exp.BinOp (binop, e1, e2) ->
            let value1 = Domain.eval ~pos:0 astate node instr e1 in
            let value2 = Domain.eval ~pos:0 astate node instr e2 in
            Domain.PathCond.make_physical_equals binop value1 value2
        | Exp.UnOp (Unop.LNot, Exp.BinOp (binop, e1, e2), _) ->
            let value1 = Domain.eval ~pos:0 astate node instr e1 in
            let value2 = Domain.eval ~pos:0 astate node instr e2 in
            Domain.PathCond.make_physical_equals binop value1 value2 |> Domain.PathCond.make_negation
        | Exp.Var _ as e ->
            let value = Domain.eval ~pos:0 astate node instr e in
            (* TODO: make e == 1 *)
            Domain.PathCond.make_physical_equals Binop.Ne value Domain.Val.zero
        | Exp.UnOp (Unop.LNot, (Exp.Var _ as e), _) ->
            let value = Domain.eval ~pos:0 astate node instr e in
            Domain.PathCond.make_physical_equals Binop.Eq value Domain.Val.zero
        | _ as bexp ->
            raise (Unexpected (F.asprintf "%a is not allowed as boolean expression in java" Exp.pp bexp))
      in
      L.d_printfln "Generated path condition : %a" Domain.PathCond.pp pathcond ;
      if Domain.PathCond.is_false pathcond then []
      else if Domain.PathCond.is_true pathcond then [astate]
      else Domain.add_pc astate pathcond
    with TODO _ -> [astate]


  let add_non_null_constraints node instr e astate =
    match e with
    | Exp.Var _ ->
        let instr_node = Node.of_pnode node instr in
        let value = Domain.eval ~pos:0 astate node instr e in
        let null = Domain.Val.make_null ~pos:0 instr_node in
        let non_null_cond = Domain.PathCond.make_physical_equals Binop.Ne value null in
        if Domain.PathCond.is_true non_null_cond then [astate] else Domain.add_pc astate non_null_cond
    | _ ->
        [astate]


  let exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs =
    (* TODO: binding unknown values to arguments *)
    let _ = arg_typs in
    let instr_node = Node.of_pnode node instr in
    (* TODO: ret_typ is not reliable *)
    let value = Domain.Val.make_extern instr_node ret_typ in
    [Domain.store_reg astate ret_id value]


  let exec_unknown_get_proc astate node instr fieldname (ret_id, _) arg_typs =
    let instr_node = Node.of_pnode node instr in
    let value = Domain.Val.make_extern instr_node Typ.void_star in
    let this_type_loc =
      let this_loc =
        let arg_exp, _ = List.hd_exn arg_typs in
        Domain.eval_lv astate arg_exp
      in
      let field_class = Typ.Name.Java.from_string (String.capitalize fieldname) in
      let field_name = Fieldname.make field_class fieldname in
      Domain.Loc.append_field this_loc ~fn:field_name
    in
    let astate_field_stored = Domain.store_loc astate this_type_loc value in
    [Domain.store_reg astate_field_stored ret_id value]


  let exec_model_proc astate node instr callee (ret_id, ret_typ) arg_typs =
    let[@warning "-8"] is_virtual = match instr with Sil.Call (_, _, _, _, {cf_virtual}) -> cf_virtual in
    let instr_node = Node.of_pnode node instr in
    match callee with
    | _ when String.equal "__cast" (Procname.get_method callee) ->
        (* ret_typ of__cast is Boolean, but is actually pointer type *)
        let arg_exp, _ = List.hd_exn arg_typs in
        (* TODO: check the logic is correct *)
        let value = Domain.eval astate node instr arg_exp in
        (* let value = Domain.Val.make_extern instr_node Typ.void_star in *)
        [Domain.store_reg astate ret_id value]
    | _ when String.equal "__instanceof" (Procname.get_method callee) ->
        (* TODO: add type checking by using sizeof_exp and get_class_name_opt *)
        let (arg_exp, _), (sizeof_exp, _) = (List.nth_exn arg_typs 0, List.nth_exn arg_typs 1) in
        let arg_value = Domain.eval astate node instr arg_exp in
        let null_cond =
          Domain.PathCond.make_physical_equals Binop.Eq arg_value (Domain.Val.make_null instr_node)
        in
        let value =
          if Domain.is_valid_pc astate null_cond then (* instanceof(null) = false *)
            Domain.Val.zero
          else Domain.Val.make_extern instr_node Typ.void_star
        in
        [Domain.store_reg astate ret_id value]
    | _ when String.equal "__unwrap_exception" (Procname.get_method callee) ->
        let value = Domain.Val.make_extern instr_node Typ.void_star in
        [Domain.unwrap_exception (Domain.store_reg astate ret_id value)]
    | _ when is_virtual && String.is_prefix (Procname.get_method callee) ~prefix:"get" ->
        (* Modeling getter method (e.g., p.getField() returns p.field) *)
        let fieldname = String.chop_prefix_exn (Procname.get_method callee) ~prefix:"get" |> String.uncapitalize in
        exec_unknown_get_proc astate node instr fieldname (ret_id, ret_typ) arg_typs
    | Procname.Java mthd ->
        (* Formal return type is more precise than actual return type (i.e., ret_typ) *)
        let ret_typ = Procname.Java.get_return_typ mthd in
        let value = Domain.Val.make_extern instr_node ret_typ in
        [Domain.store_reg astate ret_id value]
    | _ ->
        exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs


  let exec_interproc_call astate {interproc= InterproceduralAnalysis.{analyze_dependency; proc_desc}} node instr
      ret_typ arg_typs callee =
    let ret_id, _ = ret_typ in
    match analyze_dependency callee with
    | Some (callee_pdesc, callee_summary) ->
        L.d_printfln "Found summary from %a" Procname.pp callee ;
        let formals = Procdesc.get_pvar_formals callee_pdesc in
        let formal_pvars = List.map formals ~f:fst in
        let ret_var = Procdesc.get_ret_var callee_pdesc in
        let locals =
          Procdesc.get_locals callee_pdesc |> List.map ~f:(fun ProcAttributes.{name} -> Pvar.mk name callee)
        in
        let actual_values =
          List.mapi arg_typs ~f:(fun i (arg, _) -> Domain.eval astate node instr arg ~pos:(i + 1))
        in
        Summary.resolve_summary astate ~actual_values ~formals callee_summary
        |> List.map ~f:(fun astate' ->
               let return_value = Domain.read_loc astate' (Domain.Loc.of_pvar ret_var) in
               let astate_ret_binded =
                 if Domain.is_exceptional astate' then
                   (* caller_return := callee_return *)
                   let caller_ret_loc = Procdesc.get_ret_var proc_desc |> Domain.Loc.of_pvar in
                   Domain.store_loc astate' caller_ret_loc return_value
                 else (* ret_id := callee_return *)
                   Domain.store_reg astate' ret_id return_value
               in
               Domain.remove_locals ~locals:((ret_var :: formal_pvars) @ locals) astate_ret_binded)
    | None ->
        exec_model_proc astate node instr callee ret_typ arg_typs


  let compute_posts astate analysis_data node instr =
    let instr_node = Node.of_pnode node instr in
    match instr with
    | Sil.Load {id; e} when Ident.is_none id ->
        (* dereference instruction *)
        let loc = Domain.eval_lv astate e in
        if Domain.Loc.is_null loc then [] else add_non_null_constraints node instr e astate
    | Sil.Load {id; e; typ} ->
        let loc = Domain.eval_lv astate e in
        if Domain.Loc.is_null loc then []
        else if Domain.is_unknown_loc astate loc then
          (* symbolic location is introduced at load instr *)
          let state_unknown_resolved = Domain.resolve_unknown_loc astate typ loc in
          let value = Domain.read_loc state_unknown_resolved loc in
          Domain.store_reg state_unknown_resolved id value |> add_non_null_constraints node instr e
        else
          let value = Domain.read_loc astate loc in
          [Domain.store_reg astate id value]
    | Sil.Store {e1; e2= Exp.Exn _ as e2} ->
        let loc = Domain.eval_lv astate e1 in
        let value = Domain.eval astate node instr e2 ~pos:0 in
        [Domain.set_exception (Domain.store_loc astate loc value)]
    | Sil.Store {e1; e2} ->
        let loc = Domain.eval_lv astate e1 in
        if Domain.Loc.is_null loc then []
        else
          let value = Domain.eval astate node instr e2 ~pos:0 in
          Domain.store_loc astate loc value |> add_non_null_constraints node instr e1
    | Sil.Call ((ret_id, _), Const (Cfun proc), _, _, _) when Models.is_new proc ->
        (* allocation instruction *)
        let value = Domain.Val.make_allocsite instr_node in
        [Domain.store_reg astate ret_id value]
    | Sil.Call (ret_typ, Const (Cfun (Java mthd)), arg_typs, _, _) when Procname.Java.is_constructor mthd ->
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs (Procname.Java mthd)
        |> List.map ~f:(init_uninitialized_fields mthd arg_typs node instr)
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual}) when not cf_virtual ->
        (* static call *)
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs proc
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual}) when cf_virtual -> (
        (* virtual call *)
        let this_exp, _ = List.hd_exn arg_typs in
        let this_value = Domain.eval astate node instr this_exp ~pos:0 in
        match Domain.Val.get_class_name_opt this_value with
        | Some class_name ->
            let callee = Procname.replace_class proc class_name in
            exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee
        | None ->
            exec_interproc_call astate analysis_data node instr ret_typ arg_typs proc )
    | Sil.Call (ret_typ, _, arg_typs, _, _) ->
        (* callback call *)
        exec_unknown_call astate node instr ret_typ arg_typs
    | Sil.Prune (bexp, _, _, _) ->
        exec_prune astate node instr bexp
    | Sil.Metadata (ExitScope (vars, _)) ->
        let real_temps =
          List.filter vars ~f:(function Var.LogicalVar _ -> true | Var.ProgramVar pv -> Pvar.is_frontend_tmp pv)
        in
        [Domain.remove_temps astate real_temps]
    | Sil.Metadata (Nullify (pv, _)) when Pvar.is_frontend_tmp pv ->
        [Domain.remove_pvar astate ~pv]
    | Sil.Metadata (Nullify (_, _)) ->
        [astate]
    | Sil.Metadata (Abstract _) | Sil.Metadata Skip | Sil.Metadata (VariableLifetimeBegins _) ->
        [astate]


  let filter_invalid_states astate = function
    | Sil.Load {e= Var id} when Domain.is_unknown_id astate id ->
        (* Undefined behavior (e.g., unhandled exceptional flow) *)
        []
    | Sil.Store {e2= Var id} when Domain.is_unknown_id astate id ->
        (* Undefined behavior (e.g., unhandled exceptional flow) *)
        []
    | Sil.Call (_, _, arg_typs, _, _) ->
        let contains_unknown_id (arg_exp, _) =
          match arg_exp with Exp.Var id -> Domain.is_unknown_id astate id | _ -> false
        in
        if List.exists arg_typs ~f:contains_unknown_id then [] else [astate]
    | _ ->
        [astate]


  let exec_instr astate analysis_data cfg_node instr =
    let node = CFG.Node.underlying_node cfg_node in
    let is_exn_handler () =
      Procdesc.Node.equal_nodekind Procdesc.Node.exn_handler_kind (Procdesc.Node.get_kind node)
    in
    if Domain.is_exceptional astate && not (is_exn_handler ()) then
      (* If a state is exceptional, stop executing instruction until it met catch statement *)
      [astate]
    else
      let pre_states = filter_invalid_states astate instr in
      let post_states =
        List.concat_map pre_states ~f:(fun astate -> compute_posts astate analysis_data node instr)
      in
      List.map post_states ~f:(check_npe_alternative analysis_data node instr)


  let pp_session_name node fmt =
    F.fprintf fmt "===== Spec Checker (%a) ====@." Procdesc.Node.pp (CFG.Node.underlying_node node)
end

module DisjunctiveConfig : TransferFunctions.DisjunctiveConfig = struct
  let join_policy = `UnderApproximateAfter 20

  let widen_policy = `UnderApproximateAfterNumIterations 2
end

module Analyzer = NpexSymExecutor.Make (DisjReady) (DisjunctiveConfig)

let compute_invariant_map : SpecCheckerSummary.t InterproceduralAnalysis.t -> Analyzer.invariant_map =
 fun ({InterproceduralAnalysis.proc_desc} as interproc) ->
  let analysis_data = DisjReady.analysis_data interproc in
  let formals = Procdesc.get_pvar_formals proc_desc in
  Analyzer.exec_pdesc ~do_narrowing:true
    ~initial:[SpecCheckerDomain.init_with_formals formals]
    analysis_data proc_desc


let cached_compute_invariant_map =
  let cache_get, cache_set = Procname.UnitCache.create () in
  fun ({InterproceduralAnalysis.proc_desc} as analysis_data) ->
    let pname = Procdesc.get_proc_name proc_desc in
    match cache_get pname with
    | Some inv_map ->
        inv_map
    | None ->
        let inv_map = compute_invariant_map analysis_data in
        cache_set pname inv_map ; inv_map


let compute_summary : (Pvar.t * Typ.t) list -> CFG.t -> Analyzer.invariant_map -> SpecCheckerSummary.t =
 fun _ cfg inv_map ->
  (* don't need to invalidate local information thanks to remove_temps and nullify *)
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with Some exit_state -> exit_state | None -> []


let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  match Procdesc.get_proc_name proc_desc with
  | Procname.Java mthd when Procname.Java.is_autogen_method mthd ->
      (* TODO: IR of lambda function is incorrect *)
      None
  | _ ->
      let inv_map = cached_compute_invariant_map analysis_data in
      let formals = Procdesc.get_pvar_formals proc_desc in
      let cfg = CFG.from_pdesc proc_desc in
      let summary = compute_summary formals cfg inv_map in
      Some summary
