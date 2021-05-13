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
    { program: Program.t
    ; interproc: SpecCheckerSummary.t InterproceduralAnalysis.t
    ; patch: Patch.t option
    ; npe_list: NullPoint.t list option
    ; null_model: NullModel.t }

  let analysis_data interproc : analysis_data =
    let program = Program.from_marshal () in
    if Config.npex_launch_localize then
      { program
      ; interproc
      ; npe_list= Some (NullPoint.get_nullpoint_list program)
      ; patch= None
      ; null_model= NullModel.empty }
    else if Config.npex_launch_spec_inference then
      let proc_desc = InterproceduralAnalysis.(interproc.proc_desc) in
      (* let null_model = ManualNullModel.construct_manual_model proc_desc in *)
      let null_model =
        if Config.npex_manual_model then ManualNullModel.construct_manual_model proc_desc
        else NullModel.construct proc_desc
      in
      (* L.debug_dev "@.======= Null Model of %a ========@.%a@." Procname.pp (Procdesc.get_proc_name proc_desc)
         NullModel.pp null_model ; *)
      {program; interproc; npe_list= Some (NullPoint.get_nullpoint_list program); patch= None; null_model}
    else if Config.npex_launch_spec_verifier then
      let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
      {program; interproc; npe_list= None; patch= Some patch; null_model= NullModel.empty}
    else {program; interproc; npe_list= None; patch= None; null_model= NullModel.empty}


  let check_npe_alternative {npe_list; patch} node instr astate =
    if Domain.is_exceptional astate then [astate]
    else if Domain.is_npe_alternative astate then [astate]
    else if Config.npex_launch_spec_inference || Config.npex_launch_localize then
      let is_npe_instr nullpoint = Sil.equal_instr instr nullpoint.NullPoint.instr in
      match List.find (IOption.find_value_exn npe_list) ~f:is_npe_instr with
      | Some (NullPoint.{null_exp} as npe) ->
          let nullvalue = Domain.eval ~pos:(-1) astate node instr null_exp in
          if Domain.Val.is_abstract nullvalue then (* This state cannot be applied to null-model *) [astate]
          else
            let existing_nullvalues = Domain.equal_values astate nullvalue |> List.filter ~f:Domain.Val.is_null in
            let null = Domain.Val.make_null ~pos:NullSpecModel.null_pos (Node.of_pnode node instr) in
            let astate_replaced =
              let astate_pc_replaced =
                Domain.{astate with pc= Domain.PC.replace_value astate.pc ~src:nullvalue ~dst:null}
              in
              List.fold existing_nullvalues ~init:astate_pc_replaced ~f:(fun astate_acc existing_nullvalue ->
                  Domain.replace_value astate_acc ~src:existing_nullvalue ~dst:null)
            in
            let nullcond = Domain.PathCond.make_physical_equals Binop.Eq nullvalue null in
            let null_state =
              let state_null_marked : Domain.t =
                Domain.set_nullptrs astate_replaced (Domain.Val.Set.singleton nullvalue)
                |> Domain.mark_npe_alternative
                |> Domain.set_fault ~nullpoint:npe
              in
              Domain.add_pc state_null_marked nullcond
            in
            let non_null_state = Domain.add_pc astate (Domain.PathCond.make_negation nullcond) in
            null_state @ non_null_state
      | None ->
          [astate]
    else if Config.npex_launch_spec_verifier then
      match patch with
      | Some {conditional= Some (null_cond, _); null_exp}
        when InstrNode.equal null_cond (InstrNode.of_pnode node instr) ->
          let nullvalue = Domain.eval ~pos:(-1) astate node instr null_exp in
          if Domain.Val.is_abstract nullvalue then (* This state is not comparable *) [astate]
          else [Domain.mark_npe_alternative astate]
      | _ ->
          [astate]
    else [astate]


  let init_uninitialized_fields callee arg_typs node instr astate =
    match callee with
    | Procname.Java mthd -> (
        let cls = Procname.Java.get_class_type_name mthd in
        match Tenv.load_global () with
        | Some tenv -> (
          match Tenv.lookup tenv cls with
          | Some Struct.{fields} ->
              let base_exp, _ = List.hd_exn arg_typs in
              let base_loc = Domain.eval_lv astate node instr base_exp in
              List.fold fields ~init:astate ~f:(fun acc (fn, fn_typ, _) ->
                  let field_loc = Domain.Loc.append_field ~fn base_loc in
                  if Domain.is_unknown_loc acc field_loc then
                    let instr_node = InstrNode.of_pnode node instr in
                    Domain.store_loc acc field_loc (Domain.Val.get_default_by_typ instr_node fn_typ)
                  else acc)
          | None ->
              astate )
        | None ->
            astate )
    | _ ->
        astate


  let pathcond_from_prune astate node instr bexp =
    match bexp with
    | Exp.BinOp ((Binop.Eq as binop), e1, e2) | Exp.BinOp ((Binop.Ne as binop), e1, e2) ->
        let value1 = Domain.eval ~pos:0 astate node instr e1 in
        let value2 = Domain.eval ~pos:0 astate node instr e2 in
        Some (Domain.PathCond.make_physical_equals binop value1 value2)
    | Exp.UnOp (Unop.LNot, Exp.BinOp ((Binop.Eq as binop), e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp ((Binop.Ne as binop), e1, e2), _) ->
        let value1 = Domain.eval ~pos:0 astate node instr e1 in
        let value2 = Domain.eval ~pos:0 astate node instr e2 in
        Some (Domain.PathCond.make_physical_equals binop value1 value2 |> Domain.PathCond.make_negation)
    | Exp.Var _ as e ->
        let value = Domain.eval ~pos:0 astate node instr e in
        Some (Domain.PathCond.make_physical_equals Binop.Eq value Domain.Val.one)
    | Exp.UnOp (Unop.LNot, (Exp.Var _ as e), _) ->
        let value = Domain.eval ~pos:0 astate node instr e in
        Some (Domain.PathCond.make_physical_equals Binop.Eq value Domain.Val.zero)
    | _ ->
        None


  let exec_prune astate node instr bexp =
    match pathcond_from_prune astate node instr bexp with
    | Some pathcond ->
        L.d_printfln "Generated path condition : %a" Domain.PathCond.pp pathcond ;
        if Domain.PathCond.is_false pathcond then []
        else if Domain.PathCond.is_true pathcond then [astate]
        else Domain.add_pc astate pathcond
    | None ->
        (* Non-equal predicaate: just check whether bexp is true, not, or unknown *)
        let value = Domain.eval astate node instr bexp in
        if Domain.Val.is_true value then [astate] else if Domain.Val.is_false value then [] else [astate]


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
    L.d_printfln "no model found. exec unknown call" ;
    (* TODO: binding unknown values to arguments *)
    let _ = arg_typs in
    let instr_node = Node.of_pnode node instr in
    (* TODO: ret_typ is not reliable *)
    let value = Domain.Val.make_extern instr_node ret_typ in
    [Domain.store_reg astate ret_id value]


  let exec_unknown_getter astate node instr callee (ret_id, ret_typ) arg_typs =
    (* Modeling getter method (e.g., p.getField() returns p.field) *)
    let fieldname = String.chop_prefix_exn (Procname.get_method callee) ~prefix:"get" |> String.uncapitalize in
    let instr_node = Node.of_pnode node instr in
    let this_type_loc =
      let this_loc =
        let arg_exp, _ = List.hd_exn arg_typs in
        Domain.eval_lv astate node instr arg_exp
      in
      let field_class = Typ.Name.Java.from_string (String.capitalize fieldname) in
      let field_name = Fieldname.make field_class fieldname in
      Domain.Loc.append_field this_loc ~fn:field_name
    in
    let value =
      if Domain.is_unknown_loc astate this_type_loc then Domain.Val.make_extern instr_node ret_typ
      else Domain.read_loc astate this_type_loc
    in
    let astate_field_stored = Domain.store_loc astate this_type_loc value in
    [Domain.store_reg astate_field_stored ret_id value]


  let instantiate_summary astate proc_desc node instr (ret_id, ret_typ) arg_typs callee_pdesc callee_summary =
    let callee = Procdesc.get_proc_name callee_pdesc in
    let ret_var = Procdesc.get_ret_var callee_pdesc in
    let actual_values = List.mapi arg_typs ~f:(fun i (arg, _) -> Domain.eval astate node instr arg ~pos:(i + 1)) in
    let resolved_disjuncts = Summary.resolve_summary astate ~actual_values ~callee_pdesc callee_summary in
    L.d_printfln "%d states are instantiated from %d summaries from %a"
      (List.length (Summary.get_disjuncts callee_summary))
      (List.length resolved_disjuncts) Procname.pp callee ;
    let bind_return astate' =
      let return_value =
        let _value = Domain.read_loc astate' (Domain.Loc.of_pvar ret_var) in
        (* TODO: why this is happening? *)
        if Domain.Val.is_top _value then Domain.Val.of_typ ret_typ else _value
      in
      let astate_ret_binded =
        if Domain.is_exceptional astate' then
          (* caller_return := callee_return *)
          let caller_ret_loc = Procdesc.get_ret_var proc_desc |> Domain.Loc.of_pvar in
          Domain.store_loc astate' caller_ret_loc return_value
        else (* ret_id := callee_return *)
          Domain.store_reg astate' ret_id return_value
      in
      Domain.remove_locals ~pdesc:callee_pdesc astate_ret_binded
    in
    List.map resolved_disjuncts ~f:bind_return


  let exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee =
    let instr_node = Node.of_pnode node instr in
    L.d_printfln "*** No Summary Found ***" ;
    match (instr, callee) with
    | Sil.Call (_, _, _, _, {cf_virtual}), _
      when cf_virtual
           && List.hd_exn arg_typs |> snd |> Typ.is_pointer
           && String.is_prefix (Procname.get_method callee) ~prefix:"get" ->
        exec_unknown_getter astate node instr callee (ret_id, ret_typ) arg_typs
    | _, Procname.Java mthd ->
        (* Formal return type is more precise than actual return type (i.e., ret_typ) *)
        let ret_typ = Procname.Java.get_return_typ mthd in
        let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
        Domain.bind_extern_value astate instr_node (ret_id, ret_typ) callee arg_values
    | _ ->
        let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
        Domain.bind_extern_value astate instr_node (ret_id, ret_typ) callee arg_values


  let exec_interproc_call astate {interproc= InterproceduralAnalysis.{analyze_dependency; proc_desc}} node instr
      (ret_id, ret_typ) arg_typs callee =
    (* TODO: refactoring *)
    if SpecCheckerModels.is_model callee instr then
      SpecCheckerModels.exec_model astate proc_desc node instr callee (ret_id, ret_typ) arg_typs
    else
      match analyze_dependency callee with
      | Some (callee_pdesc, callee_summary) when Procname.is_constructor (Procdesc.get_proc_name callee_pdesc) ->
          instantiate_summary astate proc_desc node instr (ret_id, ret_typ) arg_typs callee_pdesc callee_summary
          |> List.map ~f:(init_uninitialized_fields (Procdesc.get_proc_name callee_pdesc) arg_typs node instr)
      | Some (callee_pdesc, callee_summary) ->
          instantiate_summary astate proc_desc node instr (ret_id, ret_typ) arg_typs callee_pdesc callee_summary
      | None when Domain.is_npe_alternative astate && Config.npex_launch_spec_inference -> (
          (* TODO: remove this redundant calculation *)
          let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
          match NullSpecModel.find_model_index astate node instr arg_values with
          | Some pos ->
              (* In case of invoking unknowon call by model-null, it would have low probability *)
              let astate = Domain.add_model astate pos ([], 0.8) in
              exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee
          | None ->
              exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee )
      | None ->
          exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee


  let exec_null_model astate {interproc= InterproceduralAnalysis.{proc_desc}; null_model} node instr
      (ret_id, ret_typ) arg_typs callee =
    if Config.npex_launch_spec_inference && Domain.is_npe_alternative astate then
      NullSpecModel.exec astate null_model proc_desc node instr (ret_id, ret_typ) arg_typs callee
    else []


  let throw_uncaught_exn astate {interproc= InterproceduralAnalysis.{proc_desc}} node instr null =
    let instr_node = Node.of_pnode node instr in
    L.progress "[WARNING]: Uncaught NPE for %a!@. - at %a@." SymDom.Null.pp_src null Node.pp instr_node ;
    let return_loc = Procdesc.get_ret_var proc_desc |> Domain.Loc.of_pvar in
    let astate_exn = Domain.set_exception astate in
    let exn_value = Domain.Val.make_string "java.lang.NullPointerException" |> Domain.Val.to_exn in
    (* TODO: should we maintain astate with uncaught exception? *)
    [Domain.store_loc astate_exn return_loc exn_value]


  let exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee =
    let normal_states =
      match instr with
      | Sil.Call (_, _, _, _, {cf_virtual}) when cf_virtual ->
          (* null-check on "this", not on empty load instruction *)
          let this_exp, _ = List.hd_exn arg_typs in
          let this_value = Domain.eval astate node instr this_exp in
          let equal_values = Domain.equal_values astate this_value in
          if List.exists equal_values ~f:Domain.Val.is_null then
            let null_value = List.find_exn equal_values ~f:Domain.Val.is_null in
            throw_uncaught_exn astate analysis_data node instr
              (Domain.Val.to_symheap null_value |> SymDom.SymHeap.to_null)
          else
            add_non_null_constraints node instr this_exp astate
            |> List.concat_map ~f:(fun astate ->
                   exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee)
      | _ ->
          exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee
    in
    let inferenced_states = exec_null_model astate analysis_data node instr ret_typ arg_typs callee in
    normal_states @ inferenced_states


  let compute_posts astate analysis_data node instr =
    let instr_node = Node.of_pnode node instr in
    match instr with
    | Sil.Load {id} when Ident.is_none id ->
        (* Ignore empty dereference and null-check on virtual invocation *)
        [astate]
    | Sil.Load {id; e= Exp.Lvar pv} when Pvar.is_frontend_tmp pv && not (is_catch_var pv) ->
        (* CatchVar could be undefined if there is no catch statement *)
        let loc = Domain.Loc.of_pvar pv ~line:(get_line node) in
        if Domain.is_unknown_loc astate loc then L.(die InternalError) "%a is unknown@." Domain.Loc.pp loc ;
        let value = Domain.read_loc astate loc in
        [Domain.store_reg astate id value]
    | Sil.Load {id; e; typ} ->
        let loc = Domain.eval_lv astate node instr e in
        if Domain.Loc.is_null loc then
          let null = Domain.Loc.to_symheap loc |> SymDom.SymHeap.to_null in
          throw_uncaught_exn astate analysis_data node instr null
        else if Domain.is_unknown_loc astate loc then
          (* symbolic location is introduced at load instr *)
          let state_unknown_resolved = Domain.resolve_unknown_loc astate typ loc in
          let value = Domain.read_loc state_unknown_resolved loc in
          Domain.store_reg state_unknown_resolved id value |> add_non_null_constraints node instr e
        else
          let value = Domain.read_loc astate loc in
          [Domain.store_reg astate id value]
    | Sil.Store {e1; e2= Exp.Exn _ as e2} ->
        let loc = Domain.eval_lv astate node instr e1 in
        let value = Domain.eval astate node instr e2 ~pos:0 in
        [Domain.set_exception (Domain.store_loc astate loc value)]
    | Sil.Store {e1= Exp.Lvar pv; e2= Exp.Const (Cint intlit); typ}
      when IntLit.iszero intlit
           && Procdesc.Node.get_succs node
              |> List.hd_exn
              |> Procdesc.Node.get_kind
              |> Procdesc.Node.equal_nodekind Procdesc.Node.Join_node ->
        (* for (i = 0; ...) *)
        [Domain.store_loc astate (Domain.Loc.of_pvar pv) (Domain.Val.make_extern instr_node typ)]
    | Sil.Store {e1= Exp.Lvar pv; e2} when Pvar.is_frontend_tmp pv ->
        let loc = Domain.Loc.of_pvar pv ~line:(get_line node) in
        let value = Domain.eval astate node instr e2 ~pos:0 in
        [Domain.store_loc astate loc value]
    | Sil.Store {e1; e2} ->
        let loc = Domain.eval_lv astate node instr e1 in
        if Domain.Loc.is_null loc then
          let null = Domain.Loc.to_symheap loc |> SymDom.SymHeap.to_null in
          throw_uncaught_exn astate analysis_data node instr null
        else
          let value = Domain.eval astate node instr e2 ~pos:0 in
          Domain.store_loc astate loc value |> add_non_null_constraints node instr e1
    | Sil.Call ((ret_id, _), Const (Cfun proc), _, _, _) when Models.is_new proc ->
        (* allocation instruction *)
        let value = Domain.Val.make_allocsite instr_node in
        [Domain.store_reg astate ret_id value]
    (* | Sil.Call (ret_typ, Const (Cfun (Java mthd)), arg_typs, _, _) when Procname.Java.is_constructor mthd ->
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs (Procname.Java mthd) *)
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
    (* | Sil.Metadata (ExitScope (vars, _)) ->
           [Domain.remove_temps astate vars]
       | Sil.Metadata (Nullify (pv, _)) ->
           [Domain.remove_pvar astate ~pv] *)
    | Sil.Metadata (ExitScope (vars, _)) ->
        let real_temps =
          List.filter vars ~f:(function
            | Var.LogicalVar _ ->
                true
            | Var.ProgramVar pv when Pvar.is_frontend_tmp pv ->
                Domain.Loc.of_pvar pv |> Domain.Loc.is_temp (* Pvar.is_frontend_tmp pv *)
            | Var.ProgramVar _ ->
                false)
        in
        [Domain.remove_temps astate ~line:(get_line node) real_temps]
    (* | Sil.Metadata (Nullify (pv, _)) when Pvar.is_frontend_tmp pv ->
        [Domain.remove_pvar astate ~line:(get_line node) ~pv] *)
    | Sil.Metadata (Nullify (pv, _)) when Domain.Loc.of_pvar pv |> Domain.Loc.is_temp ->
        [Domain.remove_pvar astate ~line:(get_line node) ~pv]
    | Sil.Metadata (Nullify (_, _)) ->
        [astate]
    | Sil.Metadata (Abstract _) | Sil.Metadata Skip | Sil.Metadata (VariableLifetimeBegins _) ->
        [astate]


  let filter_invalid_states astate = (* State with unexpected flow (e.g., unhandled exception) *)
    function
    | (Sil.Load {e= Var id} | Sil.Store {e2= Var id}) when Domain.is_unknown_id astate id ->
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
    let is_exn_handler =
      Procdesc.Node.equal_nodekind Procdesc.Node.exn_handler_kind (Procdesc.Node.get_kind node)
    in
    if Domain.is_exceptional astate && not is_exn_handler then
      (* If a state is exceptional, stop executing instruction until it met catch statement *)
      [astate]
    else
      let pre_states = filter_invalid_states astate instr in
      let post_states =
        List.concat_map pre_states ~f:(fun astate -> compute_posts astate analysis_data node instr)
      in
      List.concat_map post_states ~f:(check_npe_alternative analysis_data node instr)


  let pp_session_name node fmt =
    F.fprintf fmt "===== Spec Checker (%a) ====@." Procdesc.Node.pp (CFG.Node.underlying_node node)
end

module DisjunctiveConfig : TransferFunctions.DisjunctiveConfig = struct
  let join_policy = `UnderApproximateAfter 20

  let widen_policy = `UnderApproximateAfterNumIterations 2
end

module Analyzer = NpexSymExecutor.Make (DisjReady) (DisjunctiveConfig)

let summary_serializer : Summary.t Serialization.serializer =
  Serialization.create_serializer Serialization.Key.summary


let is_all_target_funs_analyzed : DisjReady.analysis_data -> bool =
  let is_analyzed proc =
    Filename.concat Config.npex_summary_dir (Procname.to_filename proc ^ ".specs")
    |> DB.filename_from_string
    |> Serialization.read_from_file summary_serializer
    |> Option.is_some
  in
  fun {npe_list} ->
    if Config.npex_launch_spec_inference then
      match npe_list with
      | Some npe_list ->
          List.map npe_list ~f:NullPoint.get_procname |> List.for_all ~f:is_analyzed
      | None ->
          L.(die ExternalError) "No null point parsed"
    else if Config.npex_launch_spec_verifier then
      (* TODO: how to check whether the target method is analyzed? *)
      false
    else false


let compute_invariant_map : DisjReady.analysis_data -> Analyzer.invariant_map =
 fun ({interproc= {proc_desc}} as analysis_data) ->
  let formals = Procdesc.get_pvar_formals proc_desc in
  Analyzer.exec_pdesc ~do_narrowing:false
    ~initial:[SpecCheckerDomain.init_with_formals formals]
    analysis_data proc_desc


let cached_compute_invariant_map =
  let cache_get, cache_set = Procname.UnitCache.create () in
  fun (DisjReady.{interproc= {proc_desc}} as analysis_data) ->
    let pname = Procdesc.get_proc_name proc_desc in
    match cache_get pname with
    | Some inv_map ->
        inv_map
    | None ->
        let inv_map = compute_invariant_map analysis_data in
        cache_set pname inv_map ; inv_map


let compute_summary : Procdesc.t -> CFG.t -> Analyzer.invariant_map -> SpecCheckerSummary.t =
 fun proc_desc cfg inv_map ->
  (* don't need to invalidate local information thanks to remove_temps and nullify *)
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some exit_state ->
      Summary.to_summary proc_desc exit_state
  | None ->
      Summary.empty


let checker ({InterproceduralAnalysis.proc_desc} as interproc) =
  let analysis_data = DisjReady.analysis_data interproc in
  let formals = Procdesc.get_pvar_formals proc_desc |> List.map ~f:fst in
  if List.exists formals ~f:Pvar.is_frontend_tmp then (* In this case, IR might be incomplete *)
    None
  else if is_all_target_funs_analyzed analysis_data then None
  else
    let inv_map = cached_compute_invariant_map analysis_data in
    let cfg = CFG.from_pdesc proc_desc in
    let summary = compute_summary proc_desc cfg inv_map in
    Some summary
