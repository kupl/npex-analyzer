open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Formula = StateFormula.Formula

let collect_sat_specs ~base specs =
  let pc, _ = base in
  List.partition_tf specs ~f:(fun (pc', _) -> Formula.check_sat pc pc')


let rec clarify_specs acc specs_to_clarify =
  match specs_to_clarify with
  | [] ->
      acc
  | work :: rest ->
      let sat_specs, unsat_specs = collect_sat_specs ~base:work rest in
      let merged_spec : Formula.t * Formula.t =
        List.fold sat_specs ~init:work ~f:(fun acc_spec spec_to_merge ->
            let (pc_acc, output_acc), (pc_to_merge, output_to_merge) = (acc_spec, spec_to_merge) in
            let pc_merged = Formula.merge pc_acc pc_to_merge in
            let output_merged = Formula.merge output_acc output_to_merge in
            (pc_merged, output_merged))
      in
      clarify_specs (merged_spec :: acc) unsat_specs


let verify proc_desc summary_inferenced summary_patched =
  let specs_inferenced, specs_patched =
    ( List.filter summary_inferenced ~f:Domain.is_npe_alternative
      |> List.map ~f:(StateFormula.from_state proc_desc)
      |> clarify_specs []
    , List.filter summary_patched ~f:Domain.is_npe_alternative
      |> List.map ~f:(StateFormula.from_state proc_desc)
      |> clarify_specs [] )
  in
  let print_spec i spec = L.progress "==== %d-th spec ====@.%a@." i StateFormula.pp spec in
  L.progress " - # of inferenced states: %d@." (List.length specs_inferenced) ;
  if Config.debug_mode then List.iteri specs_inferenced ~f:print_spec ;
  L.progress " - # of patched states: %d@." (List.length specs_patched) ;
  if Config.debug_mode then List.iteri specs_patched ~f:print_spec ;
  let check_sat f1 f2 =
    let result = Formula.check_sat (fst f1) (fst f2) in
    L.progress "===== check sat =====@. - lhs:@.%a@. - rhs:@.%a@. - result: %b@." StateFormula.pp f1
      StateFormula.pp f2 result ;
    result
  in
  let check_valid f1 f2 =
    let pc1, pc2 = (snd f1, snd f2) in
    let result = Formula.check_valid pc1 pc2 in
    L.progress "===== check validity =====@. - lhs: %a@. - rhs: %a@. - result: %b@." Formula.pp pc1 Formula.pp pc2
      result ;
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
  let summary_inferenced = get_original_summary target_proc |> SpecCheckerSummary.get_disjuncts in
  let summary_patched = get_summary target_proc |> SpecCheckerSummary.get_disjuncts in
  let result = verify target_pdesc summary_inferenced summary_patched in
  if result then (
    L.progress "[SUCCESS]: the patch is verified w.r.t. specification@." ;
    L.exit 0 )
  else (
    L.progress "[FAIL]: the patch does not satisfy specification@." ;
    L.exit 1 )
