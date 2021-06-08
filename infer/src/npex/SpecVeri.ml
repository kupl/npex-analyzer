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

module Spec = struct
  type t = {pc: Formula.t; output: Formula.t; symbols: Val.Set.t} [@@deriving compare]

  let pp fmt {pc; output; symbols} =
    F.fprintf fmt "(%a, %a, %a)" Formula.pp pc Formula.pp output Val.Set.pp symbols


  let check_sat ?(print_unsat = false) (infered : t) (patched : t) =
    let result = Formula.check_sat ~print_unsat infered.pc patched.pc in
    result


  let check_valid ?(print_invalid = false) (infered : t) (patched : t) =
    let result =
      Formula.check_valid ~print_invalid infered.output patched.output
      && Val.Set.equal infered.symbols patched.symbols
    in
    result


  let join lhs rhs =
    let pc = Formula.merge lhs.pc rhs.pc in
    let output = Formula.merge lhs.output rhs.output in
    let symbols = Val.Set.union lhs.symbols rhs.symbols in
    {pc; output; symbols}


  let joinable lhs rhs = Formula.check_sat lhs.pc rhs.pc

  let from_state proc_desc astate =
    let pc, output = StateFormula.from_state proc_desc astate in
    let symbols = Domain.collect_summary_symbols astate in
    {pc; output; symbols}
end

module Specs = struct
  include PrettyPrintable.MakePPSet (Spec)

  let clarify_specs specs_to_clarify =
    join_list specs_to_clarify ~joinable:Spec.joinable ~join:Spec.join ~pp:Spec.pp


  let from_disjuncts proc_desc disjuncts = disjuncts |> List.map ~f:(Spec.from_state proc_desc) |> clarify_specs
end

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


let rec add_mergeable_model acc worklist : Domain.t list list =
  L.progress " - number of worklist : %d@." (List.length worklist) ;
  let joinable lhs rhs = NullModel.joinable Domain.(lhs.applied_models) Domain.(rhs.applied_models) in
  let insertable states to_add = List.for_all states ~f:(joinable to_add) in
  let is_final (selected, remain, abandoned) =
    List.is_empty remain && not (List.exists abandoned ~f:(insertable selected))
  in
  match worklist with
  | [] ->
      acc
  | work :: rest -> (
      let selected, remain, abandoned = work in
      match remain with
      | [] when is_final work ->
          add_mergeable_model (selected :: acc) rest
      | [] ->
          add_mergeable_model acc rest
      | hd :: tl when insertable selected hd ->
          let work_hd_added = (hd :: selected, tl, abandoned) in
          let work_hd_dropped = (selected, tl, hd :: abandoned) in
          add_mergeable_model acc (work_hd_added :: work_hd_dropped :: rest)
      | hd :: tl ->
          let work_hd_dropped = (selected, tl, hd :: abandoned) in
          add_mergeable_model acc (work_hd_dropped :: rest) )


let select_most_probable_spec model_cands =
  let has_uncaught_exceptions model_cand = List.exists model_cand ~f:Domain.is_infer_failed in
  let model_cands = List.filter model_cands ~f:(not <<< has_uncaught_exceptions) in
  let model_cands = List.filter model_cands ~f:(not <<< List.is_empty) in
  let max_opt =
    List.max_elt model_cands ~compare:(fun lhs rhs ->
        Int.of_float (score lhs *. 100.) - Int.of_float (score rhs *. 100.))
  in
  L.progress "==== Model with score ====@." ;
  (* List.iter model_cands ~f:print_spec ; *)
  match max_opt with
  | Some max ->
      L.progress "@.==== MAX Model ====@." ; print_spec max ; max
  | None ->
      L.(die InternalError) "No spec"


let verify proc_desc summary_inferenced summary_patched =
  let specs_inferenced, specs_normal = List.partition_tf summary_inferenced ~f:Domain.is_npe_alternative in
  let specs_normal = Specs.from_disjuncts proc_desc specs_normal in
  L.progress " - size of specs_inferenced : %d@." (List.length specs_inferenced) ;
  let all_candidate_model =
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
    Models.fold
      (fun k mvalues acc ->
        List.concat_map (MValues.elements mvalues) ~f:(fun mvalue ->
            List.map acc ~f:(fun model -> Model.add k mvalue model)))
      merged_model [Model.empty]
  in
  L.progress " - all possible model values@." ;
  L.progress "%a@." (Pp.seq ~sep:"\n=====================================\n" Model.pp) all_candidate_model ;
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
  in
  let feasible_states_list = List.map all_candidate_model ~f:(collect_feasible_state specs_inferenced) in
  L.progress " - number of possible states: %d@." (List.length feasible_states_list) ;
  let specs_inferenced = feasible_states_list |> select_most_probable_spec |> Specs.from_disjuncts proc_desc in
  let specs_patched, specs_patched_normal = List.partition_tf summary_patched ~f:Domain.is_npe_alternative in
  let specs_patched, specs_patched_normal =
    (Specs.from_disjuncts proc_desc specs_patched, Specs.from_disjuncts proc_desc specs_patched_normal)
  in
  let print_spec i spec = L.progress "==== %d-th spec ====@.%a@." i Spec.pp spec in
  L.progress " - # of inferenced states: %d@." (List.length specs_inferenced) ;
  if Config.debug_mode then List.iteri specs_inferenced ~f:print_spec ;
  L.progress "@.================================================================@." ;
  L.progress " - # of patched states: %d@." (List.length specs_patched) ;
  if Config.debug_mode then List.iteri specs_patched ~f:print_spec ;
  let verify ~specs_inferenced ~specs_patched =
    let rec compute_tuple specs_inferenced_rest specs_patched_matched acc =
      match specs_inferenced_rest with
      | [] when Specs.equal specs_patched_matched (Specs.of_list specs_patched) ->
          acc
      | [] ->
          let unmatched_specs = Specs.diff (Specs.of_list specs_patched) specs_patched_matched in
          L.progress "no satisfied spec inferenced to the following patched spec@." ;
          L.progress "%a@." Specs.pp unmatched_specs ;
          L.progress "--------------------inferenced specs----------------------" ;
          L.progress "%a@." Specs.pp (Specs.of_list specs_inferenced) ;
          (* unmatched spec-patch exists *) []
      | spec_inferenced :: specs_inferenced_rest' ->
          let sat_specs = List.filter specs_patched ~f:(Spec.check_sat spec_inferenced) in
          if List.is_empty sat_specs then (
            ignore (List.filter specs_patched ~f:(Spec.check_sat ~print_unsat:true spec_inferenced)) ;
            L.progress "no satisfiable spec to the following inferenced spec@." ;
            L.progress "%a@." Spec.pp spec_inferenced ;
            L.progress "--------------------patched specs----------------------" ;
            L.progress "%a@." (Pp.seq ~sep:"\n" Spec.pp) specs_patched ;
            [] )
          else
            let specs_patched_matched' = Specs.union specs_patched_matched (Specs.of_list sat_specs) in
            compute_tuple specs_inferenced_rest' specs_patched_matched' ((spec_inferenced, sat_specs) :: acc)
    in
    let tuples = compute_tuple specs_inferenced Specs.empty [] in
    if List.is_empty tuples then false
    else
      List.for_all tuples ~f:(fun (spec_inferenced, satisfiable_specs) ->
          let is_valid = List.for_all satisfiable_specs ~f:(Spec.check_valid spec_inferenced) in
          if not is_valid then (
            let invalid_specs =
              List.filter satisfiable_specs ~f:(not <<< Spec.check_valid ~print_invalid:true spec_inferenced)
            in
            L.progress "invalid specs inferenced with respect to the following infered spec@." ;
            L.progress "%a@." Spec.pp spec_inferenced ;
            L.progress "-----------------------invalid patched specs--------------------------" ;
            L.progress "%a@." (Pp.seq ~sep:"\n" Spec.pp) invalid_specs ) ;
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
    L.exit 0 )
  else (
    L.progress "[FAIL]: the patch does not satisfy specification@." ;
    L.exit 1 )
