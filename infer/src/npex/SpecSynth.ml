open! IStd
open! Vocab
module L = Logging
module CFG = SpecChecker.CFG
module Analyzer = SpecChecker.Analyzer
module Domain = SpecCheckerDomain
module Conjunctions = Specification.Conjunctions
module Formula = Specification.Formula

let nullpoint_list = ref []

let get_nullpoint_list () =
  if List.is_empty !nullpoint_list then (
    let program = Program.build () in
    let lst = List.map Config.error_report_json ~f:(NullPoint.from_error_report program) in
    nullpoint_list := lst ;
    lst )
  else !nullpoint_list


(* TODO: extract context-conditions *)
let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  (* Original logic *)
  let inv_map = SpecChecker.cached_compute_invariant_map analysis_data in
  let formals = Procdesc.get_pvar_formals proc_desc in
  let cfg = CFG.from_pdesc proc_desc in
  let summary = SpecChecker.compute_summary formals cfg inv_map in
  Some summary


module Terms = AccessExpr.Set

let rec synthesize ~nullpoint ~summary ~pdesc =
  let terms_from_summary = collect_terms_from_summary summary in
  L.debug_dev "Collected terms from summary: %a@." Terms.pp terms_from_summary ;
  let all_terms = Terms.add AccessExpr.null terms_from_summary in
  let formulas = enumerate_formulas all_terms in
  let npe_str = F.asprintf "%s_%d" (NullPoint.get_method nullpoint) (NullPoint.get_line nullpoint) in
  List.map formulas ~f:(fun post ->
      Specification.create ~prefix:npe_str ~pre:Formula.true_formula ~mthd:(NullPoint.get_procname nullpoint) ~post)


and collect_terms_from_summary summary =
  List.fold summary ~init:Terms.empty ~f:(fun acc d ->
      let open SpecCheckerDomain in
      let terms_from_memory =
        fold_memory d ~init:Terms.empty ~f:(fun aexprs loc v ->
            match (loc_to_access_expr d loc, Val.get_const v) with
            | Some x, Some y ->
                aexprs |> Terms.add x |> Terms.add (AccessExpr.Primitive y)
            | Some v, None ->
                Terms.add v aexprs
            | None, Some v ->
                Terms.add (AccessExpr.Primitive v) aexprs
            | _ ->
                aexprs)
      in
      let terms_from_pc =
        let values = List.concat_map (get_path_conditions d) ~f:PathCond.vals_of_path_cond in
        List.filter_map values ~f:(fun v -> Option.map ~f:(fun c -> AccessExpr.Primitive c) (Val.get_const v))
        |> Terms.of_list
      in
      acc |> Terms.union terms_from_memory |> Terms.union terms_from_pc)


and enumerate_formulas (terms : Terms.t) : Formula.formula list =
  List.map (enumerate_atoms (Terms.elements terms)) ~f:(fun atom -> Formula.Atom atom)


and enumerate_atoms terms =
  let predicates = enumerate_predicates terms in
  [Formula.True] @ List.map predicates ~f:(fun (f, ts) -> Formula.app_of f ts)


and enumerate_predicates terms : (Formula.func * Terms.elt list) list =
  let unary_predicates = enumerate_unaries terms in
  let binary_predicates = enumerate_binaries terms in
  unary_predicates @ binary_predicates


and enumerate_unaries terms =
  let unops = Formula.[IsConstant; IsImmutable] in
  let arguments = List.chunks_of terms ~length:1 in
  List.concat_map unops ~f:(fun unop -> List.map arguments ~f:(fun terms -> (Formula.Unary unop, terms)))


and enumerate_binaries terms =
  let binops = Formula.[Equals; IsFunctionOf] in
  let arguments = List.map (List.cartesian_product terms terms) ~f:(fun (a, b) -> [a; b]) in
  List.concat_map binops ~f:(fun binop -> List.map arguments ~f:(fun terms -> (Formula.Binary binop, terms)))


let launch ~get_summary =
  let nullpoints = get_nullpoint_list () in
  let specs =
    List.fold nullpoints ~init:[] ~f:(fun acc nullpoint ->
        let pdesc = NullPoint.get_pdesc nullpoint in
        let summary = get_summary (Procdesc.get_proc_name pdesc) in
        acc @ synthesize ~nullpoint ~summary ~pdesc)
  in
  Specification.to_marshal_all specs
