open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Formula = StateFormula.Formula
module ModelKey = ManualNullModel.Key
module MValues = NullModel.MValueSet
module MValue = NullModel.MValue
module Model = PrettyPrintable.MakePPMonoMap (ModelKey) (MValue)
module Models = PrettyPrintable.MakePPMonoMap (ModelKey) (MValues)
module Val = Domain.Val
module APSet = AbstractDomain.FiniteSet (AccessExpr)

let score spec =
  let applied_models =
    List.fold ~init:NullModel.empty spec ~f:(fun acc Domain.{applied_models} ->
        NullModel.union (fun _ lhs _ -> Some lhs) acc applied_models)
  in
  NullModel.compute_probability applied_models


let print_spec spec =
  let applied_models =
    List.fold ~init:NullModel.empty spec ~f:(fun acc Domain.{applied_models} ->
        NullModel.union (fun _ lhs _ -> Some lhs) acc applied_models)
  in
  L.progress " - %f (%a)@." (score spec) NullModel.pp applied_models


module Spec = struct
  type t = {pc: Formula.t; output: Formula.t; symbols: Val.Set.t; uncaught_npes: APSet.t} [@@deriving compare]

  let pp fmt {pc; output; symbols; uncaught_npes} =
    F.fprintf fmt 
      "@[<v 2> - Formula:@, %a@]@. 
       @[<v 2> - Output:@, %a@]@. 
       @[<v 2> - Symbol used:@, %a@]@. 
       @[<v 2> - Uncaughted NPEs:@, %a@]@."
    Formula.pp_set pc Formula.pp_set output Val.Set.pp symbols APSet.pp uncaught_npes
    [@@ocamlformat "disable"]

  let check_sat ?(print_unsat = false) (infered : t) (patched : t) =
    let pc_sat = Formula.check_sat ~print_unsat infered.pc patched.pc in
    let uncaught_sat = Bool.equal (APSet.is_empty infered.uncaught_npes) (APSet.is_empty patched.uncaught_npes) in
    pc_sat && uncaught_sat


  let check_valid ?(print_invalid = false) (infered : t) (patched : t) =
    let result =
      Formula.check_valid ~print_invalid infered.output patched.output
      && Val.Set.equal infered.symbols patched.symbols
      && APSet.subset patched.uncaught_npes infered.uncaught_npes
    in
    result


  let join lhs rhs =
    let pc = Formula.merge lhs.pc rhs.pc in
    let output = Formula.merge lhs.output rhs.output in
    let symbols = Val.Set.union lhs.symbols rhs.symbols in
    let uncaught_npes = APSet.union lhs.uncaught_npes rhs.uncaught_npes in
    {pc; output; symbols; uncaught_npes}


  let joinable lhs rhs = check_sat lhs rhs

  let from_state proc_desc astate =
    let pc, output = StateFormula.from_state proc_desc astate in
    let symbols = Domain.collect_summary_symbols astate in
    let uncaught_npes =
      let null_values = Domain.(astate.uncaught_npes) in
      Val.Set.fold (APSet.union <<< StateFormula.val_to_ap astate) (Val.Set.of_list null_values) APSet.empty
    in
    let result = {pc; output; symbols; uncaught_npes} in
    L.progress "@.========= State to Spec ===========@." ;
    L.progress "%a@.------------------------------Specification-------------------@." Domain.pp astate ;
    L.progress "%a@." pp result ;
    result
end

module Specs = struct
  include PrettyPrintable.MakePPSet (Spec)

  let clarify_specs specs_to_clarify =
    join_list specs_to_clarify ~joinable:Spec.joinable ~join:Spec.join ~pp:Spec.pp


  let from_disjuncts proc_desc disjuncts =
    L.progress "[PROGRESS]: convert disjuncts to specs@." ;
    disjuncts |> List.map ~f:(Spec.from_state proc_desc) |> clarify_specs
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


  let all_candidate_model specs_inferenced =
    let merged_model =
      List.fold specs_inferenced ~init:Models.empty ~f:(fun acc Domain.{applied_models} ->
          NullModel.fold
            (fun (instr_node, pos) mvalues acc ->
              match ModelKey.from_instr (InstrNode.get_instr instr_node) pos with
              | Some key -> (
                match Models.find_opt key acc with
                | Some mvalues' ->
                    Models.add key (MValues.union mvalues mvalues') acc
                | None ->
                    Models.add key mvalues acc )
              | None ->
                  acc)
            applied_models acc)
    in
    L.progress " - merged model : %a@." Models.pp merged_model ;
    L.progress "================================================@." ;
    let result =
      Models.fold
        (fun k mvalues acc ->
          List.concat_map (MValues.elements mvalues) ~f:(fun mvalue ->
              List.map acc ~f:(fun model -> Model.add k mvalue model)))
        merged_model [Model.empty]
    in
    L.progress " - all possible model values@." ;
    L.progress "%a@." (Pp.seq ~sep:"\n----------------------------------------------" Model.pp) result ;
    result


  let collect_feasible_state states model =
    let is_feasible model Domain.{applied_models} =
      NullModel.for_all
        (fun (instr_node, pos) mvalues ->
          let mvalue = MValues.choose mvalues in
          match ModelKey.from_instr (InstrNode.get_instr instr_node) pos with
          | Some key -> (
            match Model.find_opt key model with
            | Some mvalue' ->
                MValue.equal mvalue mvalue'
            | None ->
                L.(die InternalError) "%a is not found in the following model@.%a@." ModelKey.pp key Model.pp model
            )
          | None ->
              false)
        applied_models
    in
    List.filter states ~f:(is_feasible model)


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
    List.iter model_cands ~f:(fun model_cand ->
        let model = Domain.((List.hd_exn model_cand).applied_models) in
        L.progress "Model with score %d:@.   %a@." (Int.of_float (score model_cand *. 100.)) NullModel.pp model) ;
    L.progress "==== Model with score ====@." ;
    (* List.iter model_cands ~f:print_spec ; *)
    match max_opt with
    | Some max ->
        L.progress "@.==== MAX Model ====@." ; print_spec max ; max
    | None ->
        L.(die InternalError) "No spec"


  let normal_and_max_from_disjuncts disjuncts =
    let inferenced, normal = List.partition_tf disjuncts ~f:Domain.is_npe_alternative in
    let all_candidate_model = all_candidate_model inferenced in
    let feasible_states_list = List.map all_candidate_model ~f:(collect_feasible_state inferenced) in
    L.progress " - number of possible states: %d@." (List.length feasible_states_list) ;
    let specs_inferenced = feasible_states_list |> select_most_probable_spec in
    (specs_inferenced, normal)


  let pp fmt x =
    F.fprintf fmt "@[<v 2>Inferenced States@," ;
    iter
      (fun nullpoint disjuncts ->
        F.fprintf fmt "@[<v 2> States of %a: {@," NullPoint.pp nullpoint ;
        List.iter disjuncts ~f:(fun astate -> F.fprintf fmt "%a@," Domain.pp astate) ;
        F.fprintf fmt "}@]")
      x ;
    F.fprintf fmt "@]"


  let pp_max fmt x =
    let max_spec, normal = normal_and_max_from_disjuncts x in
    F.fprintf fmt "@[<v 2>Normal States@," ;
    List.iter normal ~f:(fun astate -> F.fprintf fmt "  @[%a@]@," Domain.pp astate) ;
    F.fprintf fmt "Inferenced States@," ;
    List.iter max_spec ~f:(fun astate -> F.fprintf fmt "  @[%a@]@," Domain.pp astate) ;
    F.fprintf fmt "@]"
end

let has_feasible_model disjuncts =
  try
    ignore (InferedStates.normal_and_max_from_disjuncts disjuncts) ;
    true
  with _ -> false


let pp_states fmt x = InferedStates.pp fmt (InferedStates.from_disjuncts x)

let pp_max = InferedStates.pp_max

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
  let states_inferenced, states_normal = InferedStates.normal_and_max_from_disjuncts summary_inferenced in
  (* L.progress " - size of specs_inferenced : %d@." (List.length specs_inferenced) ;
     if Config.debug_mode then
       L.progress " ============ Inferenced States ============== @.%a@.@.@.@."
         (Pp.seq ~sep:"\n---------------------------------------" Domain.pp)
         specs_inferenced ; *)
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
  List.iter specs_patched ~f:(add_print_spec ~category:"_patched_specs") ;
  List.iter specs_patched_normal ~f:(add_print_spec ~category:"_patched_normal_specs") ;
  (* let print_spec i spec = L.progress "==== %d-th spec ====@.%a@." i Spec.pp spec in
     L.progress " - # of inferenced states: %d@." (List.length specs_inferenced) ;
     if Config.debug_mode then List.iteri specs_inferenced ~f:print_spec ;
     L.progress "@.================================================================@." ;
     L.progress " - # of patched states: %d@." (List.length specs_patched) ;
     if Config.debug_mode then List.iteri specs_patched ~f:print_spec ; *)
  let verify ~specs_inferenced ~specs_patched =
    let rec compute_tuple specs_inferenced_rest specs_patched_matched acc =
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
          let sat_specs = List.filter specs_patched ~f:(Spec.check_sat spec_inferenced) in
          if List.is_empty sat_specs then (
            ignore (List.filter specs_patched ~f:(Spec.check_sat ~print_unsat:true spec_inferenced)) ;
            (* add_print ~category:"FAIL" ~msg:"no satisfied patched spec to the following inferenced specs" ;
               add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp (Specs.of_list specs_inferenced)) ;
               add_print ~category:"FAIL" ~msg:"--------------------patched specs----------------------" ;
               add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp (Specs.of_list specs_patched)) ; *)
            if Formula.is_valid (StateFormula.exception_cond proc_desc true) Spec.(spec_inferenced.pc) then
              (* IGNORE IT: inferenced state may have more errors than patched *)
              compute_tuple specs_inferenced_rest' specs_patched_matched acc
            else (
              add_print ~category:"FAIL" ~msg:"no satisfied patched spec to the following inferenced spec" ;
              add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Spec.pp spec_inferenced) ;
              add_print ~category:"FAIL" ~msg:"--------------------patched specs----------------------" ;
              add_print ~category:"FAIL" ~msg:(F.asprintf "%a" Specs.pp (Specs.of_list specs_patched)) ;
              [] ) )
          else
            let specs_patched_matched' = Specs.union specs_patched_matched (Specs.of_list sat_specs) in
            compute_tuple specs_inferenced_rest' specs_patched_matched' ((spec_inferenced, sat_specs) :: acc)
    in
    let tuples = compute_tuple specs_inferenced Specs.empty [] in
    if Config.debug_mode then
      List.iter tuples ~f:(fun (infered, patched) ->
          add_print ~category:"paired_spec"
            ~msg:(F.asprintf "(%a, %a)" Spec.pp infered Specs.pp (Specs.of_list patched))) ;
    if List.is_empty tuples then false
    else
      List.for_all tuples ~f:(fun (spec_inferenced, satisfiable_specs) ->
          let is_valid = List.for_all satisfiable_specs ~f:(Spec.check_valid spec_inferenced) in
          if not is_valid then (
            let invalid_specs =
              List.filter satisfiable_specs ~f:(not <<< Spec.check_valid ~print_invalid:true spec_inferenced)
            in
            add_print ~category:"FAIL" ~msg:"invalid specs inferenced with respect to the following infered spec" ;
            add_print ~category:"FAIL" ~msg:(F.asprintf "%a@." Spec.pp spec_inferenced) ;
            add_print ~category:"FAIL" ~msg:"-----------------------invalid patched specs-----------------------" ;
            add_print ~category:"FAIL" ~msg:(F.asprintf "%a@." Specs.pp (Specs.of_list invalid_specs)) ) ;
          is_valid)
  in
  if List.is_empty specs_normal then (
    L.progress "[WARNING]: normal summary is empty!@." ;
    if List.is_empty specs_patched_normal then verify ~specs_inferenced ~specs_patched else false )
  else
    verify ~specs_inferenced ~specs_patched
    && verify ~specs_inferenced:specs_normal ~specs_patched:specs_patched_normal


let launch ~get_summary ~get_original_summary =
  let program = Program.build () in
  let patch = Patch.create program ~patch_json_path:Config.npex_patch_json_name in
  let target_proc = Patch.get_method patch in
  let target_pdesc = Program.pdesc_of program target_proc in
  let summary_inferenced = get_original_summary target_proc |> SpecCheckerSummary.get_local_disjuncts in
  let summary_patched = get_summary target_proc |> SpecCheckerSummary.get_local_disjuncts in
  let result = verify target_pdesc summary_inferenced summary_patched in
  if result then (
    L.progress "[SUCCESS]: the patch is verified w.r.t. specification@." ;
    print_result () ;
    L.exit 0 )
  else (
    L.progress "[FAIL]: the patch does not satisfy specification@." ;
    print_result () ;
    L.exit 1 )
