open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Formula = StateFormula.Formula

let joinable lhs rhs = Formula.check_sat (fst lhs) (fst rhs)

let join lhs rhs =
  let (pc_acc, output_acc), (pc_to_merge, output_to_merge) = (lhs, rhs) in
  let pc_merged = Formula.merge pc_acc pc_to_merge in
  let output_merged = Formula.merge output_acc output_to_merge in
  (pc_merged, output_merged)


let pp fmt (fst, snd) = F.fprintf fmt "(%a, %a)" Formula.pp fst Formula.pp snd

let clarify_specs specs_to_clarify = join_list specs_to_clarify ~joinable ~join ~pp

let rec add_mergeable_model acc states : Domain.t list list =
  let joinable lhs rhs = NullModel.joinable Domain.(lhs.applied_models) Domain.(rhs.applied_models) in
  let joinable_states = List.filter states ~f:(fun state -> List.for_all acc ~f:(joinable state)) in
  let rec packing acc cands : Domain.t list list =
    match cands with [] -> [acc] | spec :: rest -> add_mergeable_model (acc @ [spec]) rest @ packing acc rest
  in
  packing acc joinable_states


let select_most_probable_spec model_cands =
  let model_cands = List.filter model_cands ~f:(not <<< List.is_empty) in
  let score spec =
    List.fold ~init:0.0 spec ~f:(fun acc Domain.{probability} -> acc +. probability)
    /. (List.length spec |> Float.of_int)
  in
  let max_opt =
    List.max_elt model_cands ~compare:(fun lhs rhs ->
        Int.of_float (score lhs *. 100.) - Int.of_float (score rhs *. 100.))
  in
  L.progress "==== Model with score ====@." ;
  let print_spec spec =
    let applied_models =
      List.fold ~init:NullModel.empty spec ~f:(fun acc Domain.{applied_models} ->
          NullModel.union (fun _ lhs _ -> Some lhs) acc applied_models)
    in
    L.progress " - %f (%a)@." (score spec) NullModel.pp applied_models
  in
  List.iter model_cands ~f:print_spec ;
  match max_opt with
  | Some max ->
      L.progress "@.==== MAX Model ====@." ; print_spec max ; max
  | None ->
      L.(die InternalError) "No spec"


let verify proc_desc summary_inferenced summary_patched =
  L.progress "@.@.[PROGRESS]: To formula inferenced states@." ;
  let specs_inferenced =
    List.filter summary_inferenced ~f:Domain.is_npe_alternative
    |> add_mergeable_model []
    |> select_most_probable_spec
    |> List.map ~f:(StateFormula.from_state proc_desc)
    |> clarify_specs
  in
  L.progress "@.@.[PROGRESS]: To formula patched states@." ;
  let specs_patched =
    List.filter summary_patched ~f:Domain.is_npe_alternative
    |> List.map ~f:(StateFormula.from_state proc_desc)
    |> clarify_specs
  in
  let print_spec i spec = L.progress "==== %d-th spec ====@.%a@." i StateFormula.pp spec in
  L.progress " - # of inferenced states: %d@." (List.length specs_inferenced) ;
  if Config.debug_mode then List.iteri specs_inferenced ~f:print_spec ;
  L.progress " - # of patched states: %d@." (List.length specs_patched) ;
  if Config.debug_mode then List.iteri specs_patched ~f:print_spec ;
  let check_sat f1 f2 =
    let result = Formula.check_sat (fst f1) (fst f2) in
    (* L.progress "===== check sat =====@. - lhs:@.%a@. - rhs:@.%a@. - result: %b@." StateFormula.pp f1
       StateFormula.pp f2 result ; *)
    result
  in
  let check_valid f1 f2 =
    let pc1, pc2 = (snd f1, snd f2) in
    let result = Formula.check_valid pc1 pc2 in
    (* L.progress "===== check validity =====@. - lhs: %a@. - rhs: %a@. - result: %b@." Formula.pp pc1 Formula.pp pc2
       result ; *)
    result
  in
  (not (List.is_empty specs_inferenced))
  && List.for_all specs_inferenced ~f:(fun spec_inferenced ->
         let satisfiable_specs = List.filter specs_patched ~f:(check_sat spec_inferenced) in
         (not (List.is_empty satisfiable_specs)) && List.for_all satisfiable_specs ~f:(check_valid spec_inferenced))


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
