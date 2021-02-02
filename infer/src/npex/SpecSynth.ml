open! IStd
open! Vocab
module L = Logging
module CFG = SpecChecker.CFG
module Analyzer = SpecChecker.Analyzer
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
let checker = SpecChecker.checker

module Terms = AccessExpr.Set

(* let rec synthesize ~nullpoint ~summary ~pdesc =
  let terms_from_summary = collect_terms_from_summary summary in
  let terms_from_pdesc = collect_terms_from_pdesc pdesc in
  let all_terms =
    terms_from_summary
    |> Terms.union terms_from_pdesc
    |> Terms.add AccessExpr.null
    |> Terms.filter (not <<< AccessExpr.contain_method_call_access)
  in
  L.debug_dev "All terms collected: %a@." Terms.pp all_terms ;
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


and collect_terms_from_pdesc pdesc =
  let get_expressions_in_instr instr =
    List.concat_map (Sil.exps_of_instr instr) ~f:(fun e -> Exp.fold_captured ~f:(fun acc e' -> e' :: acc) e [e])
    |> Exp.Set.of_list
    |> Exp.Set.filter (function Const (Cfun _) -> false | _ -> true)
  in
  let all_exprs =
    Procdesc.fold_instrs pdesc ~init:Exp.Set.empty ~f:(fun acc _ instr ->
        Exp.Set.union acc (get_expressions_in_instr instr))
  in
  L.debug_dev "All Expressions: %a@." Pp.(seq Exp.pp) (Exp.Set.elements all_exprs) ;
  Exp.Set.fold
    (fun e acc -> match AccessExpr.from_IR_exp_opt pdesc e with Some ae -> Terms.add ae acc | None -> acc)
    all_exprs Terms.empty


and enumerate_formulas (terms : Terms.t) : Formula.formula list =
  List.concat_map
    (enumerate_atoms (Terms.elements terms))
    ~f:(fun atom -> [Formula.Neg (Formula.Atom atom); Formula.Atom atom])


and enumerate_atoms terms =
  let predicates = enumerate_predicates terms in
  [Formula.True] @ List.map predicates ~f:(fun (f, ts) -> Formula.app_of f ts)


and enumerate_predicates terms : (Formula.func * Terms.elt list) list =
  let unary_predicates = enumerate_unaries terms in
  let binary_predicates = enumerate_binaries terms in
  unary_predicates @ binary_predicates


and enumerate_unaries terms =
  let open Formula in
  let arguments = List.chunks_of terms ~length:1 in
  List.concat_map
    ~f:(fun unop -> List.map arguments ~f:(fun terms -> (Unary unop, terms)))
    [IsConstant; IsImmutable]


and enumerate_binaries terms =
  let open Formula in
  let irreflxive_pairs =
    List.filter_map
      ~f:(fun (x, y) -> if equal_term x y then None else Some [x; y])
      (List.cartesian_product terms terms)
  in
  let comb_of_pairs = combinations ~k:2 ~lst:terms in
  List.concat_map
    ~f:(fun binop ->
      let arguments = if equal_binop binop Equals then comb_of_pairs else irreflxive_pairs in
      List.map arguments ~f:(fun terms -> (Binary binop, terms)))
    [Equals; IsFunctionOf]

*)
let launch ~get_summary = ()

(* let program = Program.build () in
   let nullpoints = get_nullpoint_list () in
   let specs =
     List.fold nullpoints ~init:[] ~f:(fun acc nullpoint ->
         let pdesc = Program.pdesc_of program (NullPoint.get_procname nullpoint) in
         let summary = get_summary (Procdesc.get_proc_name pdesc) in
         acc @ synthesize ~nullpoint ~summary ~pdesc)
   in
   Specification.to_marshal_all specs *)
