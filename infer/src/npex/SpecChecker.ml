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
    else if Config.npex_launch_spec_inference then (
      let proc_desc = InterproceduralAnalysis.(interproc.proc_desc) in
      let null_model =
        if Config.npex_manual_model then ManualNullModel.construct_manual_model proc_desc
        else NullModel.construct proc_desc
      in
      if Config.debug_level_analysis >= 3 then
        L.debug_dev "@.======= Null Model of %a ========@.%a@." Procname.pp (Procdesc.get_proc_name proc_desc)
          NullModel.pp null_model ;
      {program; interproc; npe_list= Some (NullPoint.get_nullpoint_list program); patch= None; null_model} )
    else if Config.npex_launch_spec_verifier then
      let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
      {program; interproc; npe_list= None; patch= Some patch; null_model= NullModel.empty}
    else {program; interproc; npe_list= None; patch= None; null_model= NullModel.empty}


  let check_npe_alternative {npe_list; patch} node instr astate =
    let has_different_npe astate nexp =
      match astate with Domain.{fault= Some NullPoint.{null_exp}} -> not (Exp.equal nexp null_exp) | _ -> false
    in
    if Domain.is_exceptional astate then [astate]
    else if Config.npex_launch_spec_inference || Config.npex_launch_localize then
      let is_npe_instr nullpoint =
        Sil.equal_instr instr nullpoint.NullPoint.instr
        && InterNode.equal (InterNode.of_pnode node) nullpoint.NullPoint.node
      in
      match List.find (IOption.find_value_exn npe_list) ~f:is_npe_instr with
      | Some (NullPoint.{null_exp; instr} as npe) when not (has_different_npe astate null_exp) ->
          L.d_printfln " - Found null pointer expression %a" Exp.pp null_exp ;
          let nullvalue =
            match instr with
            | Sil.Metadata Skip ->
                Domain.read_loc astate (Domain.eval_lv astate node instr null_exp)
            | _ ->
                Domain.eval ~pos:(-1) astate node instr null_exp
          in
          if Domain.Val.is_top nullvalue then (* This state cannot be applied to null-model *) [astate]
          else
            (* set null condition as is_branch=true since patched program has explicit branch here *)
            let existing_nullvalues = Domain.equal_values astate nullvalue |> List.filter ~f:Domain.Val.is_null in
            let null = Domain.Val.make_null ~is_model:true (Node.of_pnode node instr) in
            L.d_printfln " - Existing null values (%a) are changed to %a" (Pp.seq Domain.Val.pp)
              existing_nullvalues Domain.Val.pp null ;
            let astate_replaced =
              (* let astate_pc_replaced =
                   Domain.{astate with pc= Domain.PC.replace_value astate.pc ~src:nullvalue ~dst:null}
                 in *)
              List.fold existing_nullvalues ~init:astate ~f:(fun astate_acc existing_nullvalue ->
                  Domain.replace_value astate_acc ~src:existing_nullvalue ~dst:null )
            in
            let nullcond = Domain.PathCond.make_physical_equals Binop.Eq nullvalue null in
            let null_state =
              let state_null_marked : Domain.t =
                Domain.set_nullptrs astate_replaced (Domain.Val.Set.singleton nullvalue)
                |> Domain.mark_npe_alternative
                |> Domain.set_fault ~nullpoint:npe
              in
              Domain.add_pc ~is_branch:true state_null_marked nullcond
            in
            let non_null_state = Domain.add_pc astate ~is_branch:true (Domain.PathCond.make_negation nullcond) in
            null_state @ non_null_state
      | _ ->
          [astate]
    else if Config.npex_launch_spec_verifier then
      match patch with
      | Some {conditional= Some (null_cond, _); null_exp}
        when InstrNode.equal null_cond (InstrNode.of_pnode node instr) ->
          let nullvalue = Domain.eval ~pos:(-1) astate node instr null_exp in
          if Domain.Val.is_top nullvalue then (* This state is not comparable *) [astate]
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
                  else acc )
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
    | Exp.BinOp (Binop.Lt, e1, e2)
    | Exp.BinOp (Binop.Gt, e2, e1)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Ge, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Le, e2, e1), _) ->
        (* e1 < e2 = e2 > e1 = not (e1 >= e2) = not (e2 <= e1) *)
        let value1 = Domain.eval ~pos:0 astate node instr e1 in
        let value2 = Domain.eval ~pos:0 astate node instr e2 in
        Some (Domain.PathCond.make_lt_pred value1 value2)
    | Exp.BinOp (Binop.Le, e1, e2)
    | Exp.BinOp (Binop.Ge, e2, e1)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Gt, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Lt, e2, e1), _) ->
        (* e1 <= e2 = e2 >= e1 = not (e1 > e2) = not (e2 < e1) *)
        let value1 = Domain.eval ~pos:0 astate node instr e1 in
        let value2 = Domain.eval ~pos:0 astate node instr e2 in
        Some (Domain.PathCond.make_le_pred value1 value2)
    | _ ->
        None


  let[@warning "-57"] exec_prune astate node instr bexp =
    match pathcond_from_prune astate node instr bexp with
    | Some pathcond ->
        L.d_printfln "Generated path condition : %a" Domain.PathCond.pp pathcond ;
        Domain.add_pc ~is_branch:true astate pathcond
    | None ->
        (* Non-equal predicaate: just check whether bexp is true, not, or unknown *)
        let value = Domain.eval astate node instr bexp in
        if Domain.Val.is_true value then [astate] else if Domain.Val.is_false value then [] else [astate]


  let throw_uncaught_exn astate {interproc= InterproceduralAnalysis.{proc_desc}} node instr value =
    (* let instr_node = Node.of_pnode node instr in
       L.progress "[WARNING]: Uncaught NPE for %a!@. - at %a@." SymDom.Null.pp_src null Node.pp instr_node ; *)
    let return_loc = Procdesc.get_ret_var proc_desc |> Domain.Loc.of_pvar in
    let astate_exn = Domain.set_exception astate in
    let exn_value = Domain.Val.npe in
    let null = Domain.Val.make_null ~pos:0 (Node.of_pnode node instr) in
    let null_cond = Domain.PathCond.make_physical_equals Binop.Eq value null in
    let states_with_nullcond = Domain.add_pc ~is_branch:true astate_exn null_cond in
    (* Maintain astates with uncaught exception for patch validation and fault localization
     * * validation: to check if patch introduce uncaught exception (e.g., NPE)
     * * localization: to pass the target error to caller *)
    let store_return_exn states =
      List.map states ~f:(fun state_with_nullcond -> Domain.store_loc state_with_nullcond return_loc exn_value)
    in
    let values = Domain.equal_values astate value in
    List.map states_with_nullcond ~f:(fun astate' -> Domain.set_uncaught_npes astate' values) |> store_return_exn


  let add_non_null_constraints astate node instr value =
    let instr_node = Node.of_pnode node instr in
    let null = Domain.Val.make_null ~pos:0 instr_node in
    let non_null_cond = Domain.PathCond.make_physical_equals Binop.Ne value null in
    if Domain.PathCond.is_true non_null_cond then [astate]
    else
      (* HEURISTICS: distinguish nullability in verification *)
      Domain.add_pc ~is_branch:true astate non_null_cond


  let check_null astate analysis_data node instr e =
    match e with
    | Exp.Lvar _ | Exp.Lindex _ ->
        (* TODO: deal with null.f, null[x] cases
         * Currently, we assume _.f and _[] location is non-null *)
        ([], [astate])
    | Exp.Lfield (Exp.Lvar _, _, _) | Exp.Lfield (Exp.Const _, _, _) ->
        (* Global.field, "".value: not null *)
        ([], [astate])
    | Exp.Lfield ((Exp.Var _ as e'), _, _) ->
        let value = Domain.eval astate node instr e' in
        let null_states = throw_uncaught_exn astate analysis_data node instr value in
        let non_null_states = add_non_null_constraints astate node instr value in
        (null_states, non_null_states)
    | _ ->
        let value = Domain.eval astate node instr e in
        let null_states = throw_uncaught_exn astate analysis_data node instr value in
        let non_null_states = add_non_null_constraints astate node instr value in
        (null_states, non_null_states)


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
    let callee_summary_filtered =
      if Config.npex_launch_spec_verifier then SpecCheckerSummary.get_only_normals callee_summary
      else callee_summary
    in
    let resolved_disjuncts = Summary.resolve_summary astate ~actual_values ~callee_pdesc callee_summary_filtered in
    L.d_printfln "%d states are instantiated from %d summaries from %a" (List.length resolved_disjuncts)
      (List.length (Summary.get_disjuncts callee_summary))
      Procname.pp callee ;
    let bind_return astate' =
      let return_value =
        let _value = Domain.read_loc astate' (Domain.Loc.of_pvar ret_var) in
        (* TODO: why this is happening? *)
        if Domain.Val.is_top _value then Domain.Val.top_of_typ ret_typ else _value
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
    let result =
      match (instr, callee) with
      | Sil.Call (_, _, [(_, arg_typ)], _, {cf_virtual}), _
        when cf_virtual && Typ.is_pointer arg_typ && String.is_prefix (Procname.get_method callee) ~prefix:"get" ->
          (* model only getter without arguments *)
          exec_unknown_getter astate node instr callee (ret_id, ret_typ) arg_typs
      | _, Procname.Java mthd ->
          (* Formal return type is more precise than actual return type (i.e., ret_typ) *)
          let ret_typ = Procname.Java.get_return_typ mthd in
          let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
          Domain.bind_extern_value astate instr_node (ret_id, ret_typ) callee arg_values
      | _ ->
          let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
          Domain.bind_extern_value astate instr_node (ret_id, ret_typ) callee arg_values
    in
    L.d_printfln "*** No summary found, %d states are returned by analyzing it as uninterpretted function... ***"
      (List.length result) ;
    result


  let exec_interproc_call astate
      ({interproc= InterproceduralAnalysis.{analyze_dependency; proc_desc}; program} as analysis_data) node instr
      (ret_id, ret_typ) arg_typs callee =
    if SpecCheckerModels.is_model callee instr then (
      L.d_printfln "execute model function" ;
      SpecCheckerModels.exec_model astate proc_desc node instr callee (ret_id, ret_typ) arg_typs )
    else
      let callee =
        match Program.unique_callee_of_instr_node_opt program (Node.of_pnode node instr) with
        | Some callee ->
            callee
        | None ->
            callee
      in
      match analyze_dependency callee with
      | Some (callee_pdesc, callee_summary) when Procname.is_constructor (Procdesc.get_proc_name callee_pdesc) ->
          instantiate_summary astate proc_desc node instr (ret_id, ret_typ) arg_typs callee_pdesc callee_summary
          |> List.map ~f:(init_uninitialized_fields (Procdesc.get_proc_name callee_pdesc) arg_typs node instr)
      | Some (callee_pdesc, callee_summary) ->
          instantiate_summary astate proc_desc node instr (ret_id, ret_typ) arg_typs callee_pdesc callee_summary
      | None -> (
          let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
          (* Assume: npe occurs if an extern function is invoked with null arguments *)
          match NullSpecModel.find_model_index astate node instr arg_values with
          | Some (_, i) ->
              L.d_printfln "[INVALID] execute extern call by null-model arg" ;
              let model_exp = List.nth_exn arg_typs i |> fst in
              let model_value = Domain.eval astate node instr model_exp in
              throw_uncaught_exn astate analysis_data node instr model_value
          | _ ->
              exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee )


  let exec_null_model ~is_library ~must astate
      {interproc= InterproceduralAnalysis.{proc_desc}; null_model; program} node instr (ret_id, ret_typ) arg_typs
      callee =
    if Config.npex_launch_spec_inference && Domain.is_npe_alternative astate then
      NullSpecModel.exec ~is_library ~must astate null_model proc_desc node instr (ret_id, ret_typ) arg_typs callee
    else []


  let exec_interproc_call astate
      ({interproc= InterproceduralAnalysis.{analyze_dependency}; program} as analysis_data) node instr ret_typ
      arg_typs callee =
    let normal_states =
      let apply_no_model astate =
        let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
        let ret_value =
          if Domain.is_exceptional astate then Domain.Val.exn
          else if Typ.is_void (snd ret_typ) then Domain.Val.bottom
          else Domain.eval astate node instr (Exp.Var (fst ret_typ))
        in
        let astate =
          (* TODO: invocation whose return is unused *)
          if Typ.is_void (snd ret_typ) then Domain.record_call astate node instr callee ret_value arg_values
          else astate
        in
        if Config.npex_launch_spec_inference && Domain.is_npe_alternative astate then
          match NullSpecModel.find_model_index astate node instr arg_values with
          | Some pos ->
              Domain.add_model astate pos NullModel.MValue.no_apply
          | None ->
              [astate]
        else [astate]
      in
      let posts =
        match instr with
        | Sil.Call (_, _, _, _, {cf_virtual}) when cf_virtual ->
            (* null-check on "this", not on empty load instruction *)
            let this_exp, _ = List.hd_exn arg_typs in
            let null_states, non_null_states = check_null astate analysis_data node instr this_exp in
            let non_null_states =
              List.concat_map non_null_states ~f:(fun astate ->
                  exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee )
            in
            null_states @ non_null_states
        | _ ->
            exec_interproc_call astate analysis_data node instr ret_typ arg_typs callee
      in
      List.concat_map posts ~f:apply_no_model
    in
    let inferenced_states =
      if Config.npex_launch_spec_inference && Domain.is_npe_alternative astate then
        (* Apply null model for foo if
           1. NPE occurs by null arguments (e.g., foo(NULL) -> NPE)
           2. NPE occurs by dereferencing base variable (e.g., NULL.foo())
           3. foo is extern function (NPE may occur)
        *)
        let summary_opt =
          let callee =
            match Program.unique_callee_of_instr_node_opt program (Node.of_pnode node instr) with
            | Some callee ->
                callee
            | None ->
                callee
          in
          analyze_dependency callee
        in
        let has_inferred_summary =
          match summary_opt with
          | Some (_, summary) ->
              SpecCheckerSummary.get_disjuncts summary |> List.exists ~f:Domain.is_inferred
          | None ->
              false
        in
        let is_library =
          let is_model = SpecCheckerModels.is_model callee instr in
          let has_summary = Option.is_some summary_opt in
          not (is_model || has_summary)
        in
        if
          List.is_empty normal_states (* this != null, but call by null = this *)
          || (List.exists normal_states ~f:Domain.has_uncaught_model_npes && not has_inferred_summary)
        then
          (* L.progress
             "Execute %a by model since NPE occurs in \
              callee@.%a@.=================================================@."
             Procname.pp callee (Pp.seq Domain.pp)
             (List.filter normal_states ~f:Domain.has_uncaught_model_npes) ; *)
          (* In some case, virtual flag is not annotated. *)
          exec_null_model ~is_library ~must:true astate analysis_data node instr ret_typ arg_typs callee
        else exec_null_model ~is_library ~must:false astate analysis_data node instr ret_typ arg_typs callee
      else []
    in
    normal_states @ inferenced_states


  let compute_posts astate analysis_data node instr =
    let instr_node = Node.of_pnode node instr in
    match instr with
    | Sil.Load {id} when Ident.is_none id ->
        (* Ignore empty dereference and null-check on virtual invocation *)
        [astate]
    | Sil.Load {id; e; typ} when Program.is_final_field_exp e && Typ.is_pointer typ ->
        (* ASSUMPTION: final static field is not null! *)
        let loc = Domain.eval_lv astate node instr e in
        (* symbolic location is introduced if location is unknown *)
        let state_unknown_resolved = Domain.resolve_unknown_loc astate typ loc in
        let value = Domain.read_loc state_unknown_resolved loc in
        let state_reg_stored = Domain.store_reg astate id value in
        add_non_null_constraints state_reg_stored node instr value
    | Sil.Load {id; e; typ} ->
        let loc = Domain.eval_lv astate node instr e in
        (* symbolic location is introduced if location is unknown *)
        let state_unknown_resolved = Domain.resolve_unknown_loc astate typ loc in
        let null_states, non_null_states = check_null state_unknown_resolved analysis_data node instr e in
        let non_null_states =
          let value = Domain.read_loc state_unknown_resolved loc in
          List.map non_null_states ~f:(fun non_null_state -> Domain.store_reg non_null_state id value)
        in
        null_states @ non_null_states
    | Sil.Store {e1; e2= Exp.BinOp (Binop.PlusA _, x, Const (Cint y))} when IntLit.isone y ->
        (* i' = i + 1 => just add condition: i' > i *)
        let loc = Domain.eval_lv astate node instr e1 in
        let v1 = Domain.eval astate node instr x in
        let value = Domain.Val.make_extern instr_node Typ.int in
        let astate_stored = Domain.store_loc astate loc value in
        Domain.add_pc astate_stored (Domain.PathCond.make_lt_pred v1 value)
    | Sil.Store {e1; e2= Exp.BinOp (Binop.MinusA _, x, y) as e2} ->
        (* e1 = x - y *)
        let loc = Domain.eval_lv astate node instr e1 in
        let v1 = Domain.eval astate node instr x in
        let v2 = Domain.eval astate node instr y in
        if Domain.is_valid_pc astate (Domain.PathCond.make_lt_pred v1 v2) then
          (* x < y => e1 < 0 *)
          let value = Domain.Val.make_extern instr_node Typ.int in
          let astate_stored = Domain.store_loc astate loc value in
          Domain.add_pc astate_stored (Domain.PathCond.make_lt_pred value Domain.Val.zero)
        else if Domain.is_valid_pc astate (Domain.PathCond.make_le_pred v1 v2) then
          (* x <= y => e1 <= 0 *)
          let value = Domain.Val.make_extern instr_node Typ.int in
          let astate_stored = Domain.store_loc astate loc value in
          Domain.add_pc astate_stored (Domain.PathCond.make_lt_pred value Domain.Val.zero)
        else if Domain.is_valid_pc astate (Domain.PathCond.make_lt_pred v2 v1) then
          (* x > y => e1 > 0 *)
          let value = Domain.Val.make_extern instr_node Typ.int in
          let astate_stored = Domain.store_loc astate loc value in
          Domain.add_pc astate_stored (Domain.PathCond.make_lt_pred Domain.Val.zero value)
        else if Domain.is_valid_pc astate (Domain.PathCond.make_le_pred v2 v1) then
          (* x >= y => e1 >= 0 *)
          let value = Domain.Val.make_extern instr_node Typ.int in
          let astate_stored = Domain.store_loc astate loc value in
          Domain.add_pc astate_stored (Domain.PathCond.make_le_pred Domain.Val.zero value)
        else
          let value = Domain.eval astate node instr e2 in
          [Domain.store_loc astate loc value]
    | Sil.Store {e1; e2= Exp.Exn _ as e2} ->
        let loc = Domain.eval_lv astate node instr e1 in
        let value = Domain.eval astate node instr e2 ~pos:0 in
        [Domain.set_exception (Domain.store_loc astate loc value)]
    | Sil.Store {e1= Exp.Lvar pv; e2} when Pvar.is_frontend_tmp pv ->
        let loc = Domain.Loc.of_pvar pv ~line:(get_line node) in
        let value = Domain.eval astate node instr e2 ~pos:0 in
        [Domain.store_loc astate loc value]
    | Sil.Store {e1; e2} ->
        let loc = Domain.eval_lv astate node instr e1 in
        let null_states, non_null_states = check_null astate analysis_data node instr e1 in
        let non_null_states =
          let value = Domain.eval astate node instr e2 ~pos:0 in
          List.map non_null_states ~f:(fun non_null_state -> Domain.store_loc non_null_state loc value)
        in
        null_states @ non_null_states
    | Sil.Call ((ret_id, _), Const (Cfun proc), _, _, _) when is_new proc ->
        (* allocation instruction *)
        let value = Domain.Val.make_allocsite instr_node in
        [Domain.store_reg astate ret_id value]
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual}) when not cf_virtual ->
        (* static call *)
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs proc
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual})
      when cf_virtual && Typ.is_int (List.hd_exn arg_typs |> snd) ->
        (* Pasring ERROR: callee is virtual, but invoke it by integer *)
        exec_unknown_method astate node instr ret_typ arg_typs proc
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
          List.filter vars ~f:(function
            | Var.LogicalVar _ ->
                true
            | Var.ProgramVar pv when Pvar.is_frontend_tmp pv ->
                Domain.Loc.of_pvar pv |> Domain.Loc.is_temp (* Pvar.is_frontend_tmp pv *)
            | Var.ProgramVar _ ->
                (* In Java7, some temp variables ares unsoundly translated. So do not remove it *)
                false )
        in
        [Domain.remove_temps astate ~line:(get_line node) real_temps]
    | Sil.Metadata (Nullify (pv, _)) when Domain.Loc.of_pvar pv |> Domain.Loc.is_temp ->
        [Domain.remove_temps astate ~line:(get_line node) [Var.of_pvar pv]]
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


  let exec_instr astate analysis_data node instr =
    debug_time "exec_instr" ~f:(exec_instr astate analysis_data node) ~arg:instr


  let pp_session_name node fmt =
    F.fprintf fmt "===== Spec Checker (%a) ====@." Procdesc.Node.pp (CFG.Node.underlying_node node)
end

module DisjunctiveConfig : TransferFunctions.DisjunctiveConfig = struct
  let join_policy = `UnderApproximateAfter 20

  let widen_policy =
    if Config.npex_launch_localize then `UnderApproximateAfterNumIterations 0
    else `UnderApproximateAfterNumIterations 2
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
  Analyzer.exec_pdesc ~do_narrowing:false ~initial:[SpecCheckerDomain.init proc_desc] analysis_data proc_desc


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
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some exit_state ->
      Summary.to_summary proc_desc exit_state
  | None ->
      Summary.empty


let checker ({InterproceduralAnalysis.proc_desc} as interproc) =
  let analysis_data = DisjReady.analysis_data interproc in
  let formals = Procdesc.get_pvar_formals proc_desc |> List.map ~f:fst in
  let procname = Procdesc.get_proc_name proc_desc in
  if List.exists formals ~f:Pvar.is_frontend_tmp then (
    (* In this case, IR might be incomplete *)
    L.(debug Analysis Quiet) "%a has incompletely translated IR" Procname.pp procname ;
    None )
  else if Config.npex_launch_localize && Procname.is_java_class_initializer procname then
    (* HEURISTICS: ignore class initializer which may be called at main procedure. *)
    None
  else if
    (Config.npex_launch_spec_inference || Config.npex_launch_spec_verifier) && not (Program.is_executed procname)
  then None (* && is_all_target_funs_analyzed analysis_data then None *)
  else
    let inv_map = cached_compute_invariant_map analysis_data in
    let cfg = CFG.from_pdesc proc_desc in
    let summary = compute_summary proc_desc cfg inv_map in
    Some summary
