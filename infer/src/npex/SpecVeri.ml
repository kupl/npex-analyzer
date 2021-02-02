open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Formula = StateFormula.Formula

let verify proc_desc summary_inferenced summary_patched =
  let specs_inferenced, specs_patched =
    ( List.filter summary_inferenced ~f:Domain.is_npe_alternative |> List.map ~f:(StateFormula.from_state proc_desc)
    , List.filter summary_patched ~f:Domain.is_npe_alternative |> List.map ~f:(StateFormula.from_state proc_desc)
    )
  in
  L.progress " - # of inferenced states: %d@." (List.length specs_inferenced) ;
  L.progress " - # of inferenced states: %d@." (List.length specs_patched) ;
  (not (List.is_empty specs_inferenced))
  && List.for_all specs_inferenced ~f:(fun spec_inferenced ->
         let pc_inferenced, state_inferenced = spec_inferenced in
         let satisfiable_specs = List.filter specs_patched ~f:(Formula.check_sat pc_inferenced <<< fst) in
         (not (List.is_empty satisfiable_specs))
         && List.for_all satisfiable_specs ~f:(Formula.check_valid state_inferenced <<< snd))


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
