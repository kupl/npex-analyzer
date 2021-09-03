open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Spec = StateFormula
module Pos = NullModel.Pos
module ModelKey = NullModel.Key
module MValues = NullModel.MValueSet
module MValue = NullModel.MValue
module MExp = NullModel.MExp
module MExps = PrettyPrintable.MakePPSet (MExp)
module KeyModel = PrettyPrintable.MakePPMonoMap (ModelKey) (MValue)
module Model = PrettyPrintable.MakePPMonoMap (ModelKey) (MExp)
module Models = PrettyPrintable.MakePPMonoMap (ModelKey) (MExps)
module Val = Domain.Val
module APSet = AbstractDomain.FiniteSet (AccessExpr)

let score spec =
  let applied_models =
    List.fold ~init:NullModel.empty spec ~f:(fun acc Domain.{applied_models} ->
        NullModel.union (fun _ lhs _ -> Some lhs) acc applied_models)
  in
  let key_model =
    NullModel.fold
      (fun pos mvalues acc ->
        let mexp', prob' = MValues.choose mvalues in
        let key = Pos.to_key pos in
        match KeyModel.find_opt key acc with
        | _ when List.is_empty mexp' ->
            acc
        | Some (mexp, prob) ->
            KeyModel.add key (mexp, (prob +. prob') /. 2.0) acc
        | None ->
            KeyModel.add key (mexp', prob') acc)
      applied_models KeyModel.empty
  in
  KeyModel.fold (fun _ (_, prob) acc -> prob +. acc) key_model 0.5
  /. (KeyModel.cardinal key_model + 1 |> Float.of_int)


let print_spec spec =
  let applied_models =
    List.fold ~init:NullModel.empty spec ~f:(fun acc Domain.{applied_models} ->
        NullModel.union (fun _ lhs _ -> Some lhs) acc applied_models)
  in
  L.progress " - %f (%a)@." (score spec) NullModel.pp applied_models


type result = UnSAT | SynEquiv | SemEquiv | Invalid [@@deriving compare]

let equal_result = [%compare.equal: result]

module Specs = struct
  include PrettyPrintable.MakePPSet (Spec)

  let clarify_specs specs_to_clarify =
    join_list specs_to_clarify ~joinable:Spec.joinable ~join:Spec.join ~pp:Spec.pp


  let from_disjuncts proc_desc disjuncts =
    (* L.progress "[PROGRESS]: convert disjuncts to specs@." ; *)
    disjuncts |> List.map ~f:(Spec.from_state proc_desc)


  (* |> clarify_specs *)

  let exists_valid ~check_valid (specs : t) (spec : Spec.t) = exists (check_valid spec) specs

  let check_valid ~check_valid (infered : t) (patched : t) =
    let infered_exceptional, infered_normal = partition Spec.is_exceptional infered in
    let patched_exceptional, patched_normal = partition Spec.is_exceptional patched in
    for_all (exists_valid ~check_valid infered_normal) patched_normal
    && for_all (exists_valid ~check_valid patched_normal) infered_normal
    && for_all (exists_valid ~check_valid infered_exceptional) patched_exceptional


  let pp fmt specs =
    F.fprintf fmt "=================== Specs =====================@," ;
    List.iteri (elements specs) ~f:(fun i spec -> F.fprintf fmt "%d-th spec:@, - %a@," i Spec.pp spec)

  (* && for_all (exists_valid ~check_valid x) y *)
end

module InferedStates = struct
  include PrettyPrintable.MakePPMap (NullPoint)

  let update k v = update k (function Some v' -> Some (v :: v') | None -> Some [v])

  let from_disjuncts disjuncts =
    List.fold disjuncts ~init:empty ~f:(fun acc astate ->
        match Domain.(astate.fault) with
        | Some nullpoint ->
            update nullpoint astate acc
        | None ->
            update NullPoint.dummy astate acc)


  let enumerate_candidate_models (specs_inferenced : Domain.t list) =
    let merged_model =
      List.fold specs_inferenced ~init:Models.empty ~f:(fun acc Domain.{applied_models} ->
          NullModel.fold
            (fun (instr_node, pos) mvalues acc ->
              let mexps = NullModel.mexps_from_mvalues mvalues in
              match ModelKey.from_instr (InstrNode.get_instr instr_node) pos with
              | Some key -> (
                match Models.find_opt key acc with
                | Some mexps' ->
                    Models.add key (MExps.union mexps mexps') acc
                | None ->
                    Models.add key mexps acc )
              | None ->
                  acc)
            applied_models acc)
    in
    L.progress " - merged model : %a@." Models.pp merged_model ;
    L.progress "================================================@." ;
    let keylist = Models.bindings merged_model |> List.map ~f:fst in
    let is_key_in_states k disjuncts =
      List.exists disjuncts ~f:(fun Domain.{applied_models} ->
          NullModel.exists (fun pos _ -> ModelKey.equal k (Pos.to_key pos)) applied_models)
    in
    let is_feasible k v Domain.{applied_models} =
      NullModel.for_all
        (fun pos mvals ->
          (not (ModelKey.equal (Pos.to_key pos) k))
          || MExp.equal (NullModel.mexps_from_mvalues mvals |> MExps.choose) v)
        applied_models
    in
    List.fold keylist ~init:[(Model.empty, specs_inferenced)]
      ~f:(fun (model_cands : (Model.t * Domain.t list) list) key ->
        L.progress "Current cands: %d, now enumerate key %a...@." (List.length model_cands) ModelKey.pp key ;
        List.concat_map model_cands ~f:(fun (model, feasible_states) ->
            if is_key_in_states key feasible_states then
              let mexps = Models.find key merged_model |> MExps.elements in
              List.filter_map mexps ~f:(fun mexp ->
                  let model' = Model.add key mexp model in
                  let feasible_states' = List.filter feasible_states ~f:(is_feasible key mexp) in
                  if List.is_empty feasible_states' then None else Some (model', feasible_states'))
            else [(model, feasible_states)]))


  let select_most_probable_spec model_cands =
    let is_valid_model disjuncts =
      let no_uncaught_model_npe = not (List.exists disjuncts ~f:Domain.has_uncaught_model_npes) in
      let exists_no_uncaught_npe = List.exists disjuncts ~f:(not <<< Domain.has_uncaught_npes) in
      (* if (not no_uncaught_model_npe) || not exists_no_uncaught_npe then
         L.progress "%a has invalid state@." NullModel.pp (List.hd_exn disjuncts).Domain.applied_models ; *)
      no_uncaught_model_npe && exists_no_uncaught_npe
    in
    let model_cands = List.filter model_cands ~f:is_valid_model in
    let max_opt =
      List.max_elt model_cands ~compare:(fun lhs rhs ->
          Int.of_float (score lhs *. 100.) - Int.of_float (score rhs *. 100.))
    in
    (* List.iter model_cands ~f:(fun model_cand ->
        let model = Domain.((List.hd_exn model_cand).applied_models) in
        L.progress "Model with score %d:@.   %a@." (Int.of_float (score model_cand *. 100.)) NullModel.pp model) ; *)
    (* L.progress "==== Model with score ====@." ; *)
    (* List.iter model_cands ~f:print_spec ; *)
    match max_opt with
    | Some max ->
        L.progress "@.==== MAX Model ====@." ; print_spec max ; max
    | None ->
        raise (Unexpected "NoSpec")


  let normal_and_max_from_disjuncts disjuncts =
    let inferenced, normal = List.partition_tf disjuncts ~f:Domain.is_npe_alternative in
    let feasible_states_list = enumerate_candidate_models inferenced |> List.map ~f:snd in
    let specs_inferenced = select_most_probable_spec feasible_states_list in
    (normal, specs_inferenced)


  let pp fmt x =
    F.fprintf fmt "@[<v 2>Inferenced States@," ;
    iter
      (fun nullpoint disjuncts ->
        F.fprintf fmt "@[<v 2> States of %a: {@," NullPoint.pp nullpoint ;
        List.iter disjuncts ~f:(fun astate -> F.fprintf fmt "%a@," Domain.pp astate) ;
        F.fprintf fmt "}@]")
      x ;
    F.fprintf fmt "@]"


  let pp_max fmt ~normal ~infered =
    F.fprintf fmt "@[<v 2>Normal States@," ;
    List.iter normal ~f:(fun astate -> F.fprintf fmt "  @[%a@]@," Domain.pp astate) ;
    F.fprintf fmt "Inferenced States@," ;
    List.iter infered ~f:(fun astate -> F.fprintf fmt "  @[%a@]@," Domain.pp astate) ;
    F.fprintf fmt "@]"
end

let get_feasible_disjuncts_opt disjuncts =
  try Some (InferedStates.normal_and_max_from_disjuncts disjuncts) with
  | Unexpected "NoSpec" ->
      None
  | _ as e ->
      (* do not ignore other exceptions *)
      raise e


let pp_states fmt x = InferedStates.pp fmt (InferedStates.from_disjuncts x)

let pp_normal_and_infered fmt (normal, infered) = InferedStates.pp_max fmt ~normal ~infered

let _to_print = ref String.Map.empty

let add_print ~category ~msg =
  _to_print :=
    String.Map.change !_to_print category ~f:(function
      | Some msgs ->
          Some (F.asprintf "%s@,%s" msgs msg)
      | None ->
          Some (F.asprintf "%s" msg))


let print_result () =
  let patch_id = match Config.npex_patch_id with Some patch_id -> patch_id | None -> "unknown_patch" in
  String.Map.iteri !_to_print ~f:(fun ~key ~data ->
      let msg = F.asprintf "@[<v 2> %s:@, %s@]" key data in
      print_to_file ~msg ~filename:(Config.npex_result_dir ^/ patch_id ^ "_" ^ key))


let add_print_state ~category astate = add_print ~category ~msg:(F.asprintf "%a" Domain.pp astate)

let add_print_spec ~category spec = add_print ~category ~msg:(F.asprintf "%a" Spec.pp spec)

let verify proc_desc summary_inferenced summary_patched =
  let states_normal, states_inferenced = InferedStates.normal_and_max_from_disjuncts summary_inferenced in
  let specs_normal, specs_inferenced =
    (Specs.from_disjuncts proc_desc states_normal, Specs.from_disjuncts proc_desc states_inferenced)
  in
  let states_patched, states_patched_normal = List.partition_tf summary_patched ~f:Domain.is_npe_alternative in
  let specs_patched, specs_patched_normal =
    (Specs.from_disjuncts proc_desc states_patched, Specs.from_disjuncts proc_desc states_patched_normal)
  in
  List.iter states_inferenced ~f:(add_print_state ~category:"inferenced_states") ;
  List.iter states_normal ~f:(add_print_state ~category:"normal_states") ;
  List.iter states_patched ~f:(add_print_state ~category:"patched_states") ;
  List.iter states_patched_normal ~f:(add_print_state ~category:"patched_normal_states") ;
  List.iter specs_normal ~f:(add_print_spec ~category:"normal_specs") ;
  List.iter specs_inferenced ~f:(add_print_spec ~category:"inferenced_specs") ;
  List.iter specs_patched ~f:(add_print_spec ~category:"patched_specs") ;
  List.iter specs_patched_normal ~f:(add_print_spec ~category:"patched_normal_specs") ;
  let compute_tuple ~specs_inferenced ~specs_patched =
    let rec _compute_tuple specs_inferenced_rest specs_patched_matched acc =
      match specs_inferenced_rest with
      | []
        when Specs.is_empty specs_patched_matched
             || not (Specs.equal specs_patched_matched (Specs.of_list specs_patched)) ->
          let unmatched_specs = Specs.diff (Specs.of_list specs_patched) specs_patched_matched in
          add_print ~category:"FAIL" ~msg:"unmatched patched specs exist:" ;
          add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp unmatched_specs) ;
          add_print ~category:"FAIL" ~msg:"--------------------inferenced specs----------------------" ;
          add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp (Specs.of_list specs_inferenced)) ;
          (* unmatched spec-patch exists *) []
      | [] ->
          acc
      | spec_inferenced :: specs_inferenced_rest' ->
          let sat_inferenced_specs = List.filter specs_inferenced ~f:(Spec.check_sat spec_inferenced) in
          let sat_patched_specs = List.filter specs_patched ~f:(Spec.check_sat spec_inferenced) in
          if List.is_empty sat_patched_specs then (
            ignore (List.filter specs_patched ~f:(Spec.check_sat ~print_unsat:true spec_inferenced)) ;
            if Spec.is_exceptional spec_inferenced then
              (* IGNORE IT: inferenced state may have more errors than patched *)
              _compute_tuple specs_inferenced_rest' specs_patched_matched acc
            else (
              add_print ~category:"FAIL" ~msg:"no satisfied patched spec to the following inferenced spec" ;
              add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Spec.pp spec_inferenced) ;
              add_print ~category:"FAIL" ~msg:"--------------------patched specs----------------------" ;
              add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp (Specs.of_list specs_patched)) ;
              [] ) )
          else
            let specs_patched_matched' = Specs.union specs_patched_matched (Specs.of_list sat_patched_specs) in
            _compute_tuple specs_inferenced_rest' specs_patched_matched'
              ((Specs.of_list sat_inferenced_specs, Specs.of_list sat_patched_specs) :: acc)
    in
    _compute_tuple specs_inferenced Specs.empty []
  in
  let verify ~is_alternative ~specs_inferenced ~specs_patched =
    let tuples = compute_tuple ~specs_inferenced ~specs_patched in
    let verify_by_syn_equiv =
      let check_valid = Spec.check_syn_equiv in
      let category = if is_alternative then "FAIL_SYN" else "FAIL_SYN_NORMAL" in
      List.for_all tuples ~f:(fun (sat_inferenced_specs, sat_patched_specs) ->
          (* let exceptional_filtered =
               Specs.filter
                 (fun spec ->
                   let check_valid = Spec.check_sat ~print_unsat:false in
                   Spec.is_exceptional spec && Specs.exists_valid ~check_valid sat_patched_specs spec)
                 sat_inferenced_specs
             in *)
          let is_valid = Specs.check_valid ~check_valid sat_inferenced_specs sat_patched_specs in
          ( if not is_valid then
            let unmatched_infered =
              Specs.filter (not <<< Specs.exists_valid ~check_valid sat_patched_specs) sat_inferenced_specs
            in
            let unmatched_patched =
              Specs.filter (not <<< Specs.exists_valid ~check_valid sat_inferenced_specs) sat_patched_specs
            in
            if not (Specs.is_empty unmatched_infered) then (
              add_print ~category ~msg:"Could not find any valid patched spec for the following infered" ;
              add_print ~category ~msg:(F.asprintf "%a@." (Pp.seq Spec.pp) (Specs.elements unmatched_infered)) ;
              add_print ~category ~msg:"-----------------------patched specs-----------------------" ;
              add_print ~category ~msg:(F.asprintf "%a@." (Pp.seq Spec.pp) (Specs.elements unmatched_patched)) ;
              add_print ~category ~msg:"-----------------------all patched specs-----------------------" ;
              add_print ~category ~msg:(F.asprintf "%a@." (Pp.seq Spec.pp) (Specs.elements sat_patched_specs)) )
            else if not (Specs.is_empty unmatched_patched) then (
              add_print ~category ~msg:"Could not find any valid infered spec for the following patched" ;
              add_print ~category ~msg:(F.asprintf "%a@." (Pp.seq Spec.pp) (Specs.elements unmatched_patched)) ;
              add_print ~category ~msg:"-----------------------infered specs-----------------------" ;
              add_print ~category ~msg:(F.asprintf "%a@." (Pp.seq Spec.pp) (Specs.elements sat_inferenced_specs)) )
          ) ;
          is_valid)
    in
    let verify_by_sem_equiv =
      let check_valid = Spec.check_valid in
      let category = if is_alternative then "FAIL" else "FAIL_NORMAL" in
      List.for_all tuples ~f:(fun (sat_inferenced_specs, sat_patched_specs) ->
          let is_valid = Specs.check_valid ~check_valid sat_inferenced_specs sat_patched_specs in
          ( if not is_valid then
            let unmatched_infered =
              Specs.filter (not <<< Specs.exists_valid ~check_valid sat_patched_specs) sat_inferenced_specs
            in
            let unmatched_patched =
              Specs.filter (not <<< Specs.exists_valid ~check_valid sat_inferenced_specs) sat_patched_specs
            in
            if not (Specs.is_empty unmatched_infered) then (
              add_print ~category ~msg:"Could not find any valid patched spec for the following infered" ;
              add_print ~category ~msg:(F.asprintf "%a@." Specs.pp unmatched_infered) ;
              add_print ~category ~msg:"-----------------------patched specs-----------------------" ;
              add_print ~category ~msg:(F.asprintf "%a@." Specs.pp sat_patched_specs) )
            else if not (Specs.is_empty unmatched_patched) then (
              add_print ~category ~msg:"Could not find any valid infered spec for the following patched" ;
              add_print ~category ~msg:(F.asprintf "%a@." Specs.pp unmatched_patched) ;
              add_print ~category ~msg:"-----------------------infered specs-----------------------" ;
              add_print ~category ~msg:(F.asprintf "%a@." Specs.pp sat_inferenced_specs) ) ) ;
          is_valid)
    in
    List.iter tuples ~f:(fun (infered, patched) ->
        add_print ~category:"paired_spec" ~msg:(F.asprintf "(%a, %a)" Specs.pp infered Specs.pp patched)) ;
    if List.is_empty tuples then UnSAT
    else if verify_by_syn_equiv then SynEquiv
    else if verify_by_sem_equiv then SemEquiv
    else Invalid
  in
  if List.is_empty specs_normal then (
    L.progress "[WARNING]: normal summary is empty!@." ;
    if List.is_empty specs_patched_normal then verify ~specs_inferenced ~specs_patched ~is_alternative:true
    else (* TODO: compare alternative specs with normal specs of patched method *)
      UnSAT
      (* else if
           List.for_all specs_inferenced ~f:Spec.is_exceptional && not (List.for_all specs_patched ~f:Spec.is_exceptional)
         then (
           L.progress "Patched state should have exceptional states!@." ;
           false )
         else if
           (not (List.for_all specs_inferenced ~f:Spec.is_exceptional))
           && List.for_all specs_patched ~f:Spec.is_exceptional
         then (
           L.progress "Patched state should have normal states!@." ;
           false )
         else
           let normal_patch_pairs =
             compute_tuple ~specs_inferenced:specs_normal ~specs_patched
             |> List.map ~f:(fun (n, ps) -> List.filter ps ~f:(Spec.check_valid n))
           in
           if List.exists normal_patch_pairs ~f:List.is_empty then false *) )
  else
    let result = verify ~is_alternative:true ~specs_inferenced ~specs_patched in
    let normal_result =
      verify ~is_alternative:false ~specs_inferenced:specs_normal ~specs_patched:specs_patched_normal
    in
    if equal_result normal_result UnSAT || equal_result normal_result Invalid then normal_result else result


(* let result_normal = verify 
   if equal_result result SemEquiv || equal_result result SynEquiv then result_normal else result *)

(* else
   let specs_inferenced = Specs.from_disjuncts proc_desc (states_inferenced @ states_normal) in
   let specs_patched = Specs.from_disjuncts proc_desc (states_patched @ states_patched_normal) in
   verify ~specs_inferenced ~specs_patched *)

let has_caller_npe program get_summary target_proc =
  let callers = Program.callers_of_proc program target_proc in
  List.exists callers ~f:(fun caller ->
      try
        let summary = get_summary caller |> SpecCheckerSummary.get_disjuncts in
        let alternative_states = List.filter summary ~f:Domain.is_npe_alternative in
        if List.is_empty alternative_states then false
        else List.for_all alternative_states ~f:Domain.has_uncaught_npes
      with _ -> (* caller not analyzed *) false)


let launch ~get_summary ~get_original_summary =
  let program = Program.build () in
  let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
  let target_proc = Patch.get_method patch in
  (* TODO: verify on most caller
     let null_procs = NullPoint.parse_npe_methods program in
     let target_proc =
       Procname.Set.fold
         (fun acc proc ->
           let callees_of_proc = Program.cg_reachables_of program (Procname.Set.singleton proc) in
           if Procname.Set.mem acc callees_of_proc then proc else acc)
         null_procs target_proc
     in *)
  let target_pdesc = Program.pdesc_of program target_proc in
  let summary_inferenced = get_original_summary target_proc |> SpecCheckerSummary.get_local_disjuncts in
  let summary_patched = get_summary target_proc |> SpecCheckerSummary.get_local_disjuncts in
  (* L.progress "patched summaries: %a@." (Pp.seq ~sep:"\n" Domain.pp) summary_patched ; *)
  let result : result = verify target_pdesc summary_inferenced summary_patched in
  match result with
  | _ when has_caller_npe program get_summary target_proc ->
      L.progress "[FAIL]: NPE remains in patch@." ;
      print_result () ;
      L.exit 13
  | SynEquiv ->
      L.progress "[SUCCESS]: the patch is verified w.r.t. specification (SynEquiv) @." ;
      print_result () ;
      L.exit 11
  | SemEquiv ->
      L.progress "[SUCCESS]: the patch is verified w.r.t. specification (SemEquiv) @." ;
      print_result () ;
      L.exit 12
  | UnSAT ->
      L.progress "[FAIL]: the patch does not satisfy specification (UnSAT) @." ;
      print_result () ;
      L.exit 13
  | Invalid ->
      L.progress "[FAIL]: the patch does not satisfy specification (Invalid) @." ;
      print_result () ;
      L.exit 14
