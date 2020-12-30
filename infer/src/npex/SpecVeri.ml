open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
open Specification.Formula

module Row = struct
  type t = (string, bool) List.Assoc.t

  let pp_item ?(is_header = false) fmt (column, value) =
    if is_header then F.fprintf fmt "%s" column else F.fprintf fmt "%b" value


  let pp ?(is_header = false) : F.formatter -> t -> unit = Pp.seq ~sep:"," (pp_item ~is_header)

  let write_to_csv row fname =
    L.progress "Writing results to %s@." fname ;
    Utils.with_file_out fname ~f:(fun oc ->
        let fmt = F.formatter_of_out_channel oc in
        F.fprintf fmt "%a@." (pp ~is_header:true) row ;
        F.fprintf fmt "%a@." (pp ~is_header:false) row)
end

let eval_term astate = function
  | AccessExpr.AccessExpr (pv, accesses) -> (
      let base = Domain.Loc.of_pvar pv in
      try
        let loc =
          List.fold accesses ~init:base ~f:(fun acc access ->
              match access with
              | AccessExpr.FieldAccess fn ->
                  Domain.Loc.append_field acc ~fn
              | _ ->
                  raise (TODO "Spec should not contain array or method invocation"))
        in
        Domain.read_loc astate loc
      with TODO _ -> Domain.Val.top )
  | AccessExpr.Primitive const ->
      Domain.Val.of_const const


let eval_unary astate f term =
  let value = eval_term astate term in
  match f with IsConstant -> Domain.Val.is_constant value | IsImmutable -> true


(* raise (TODO "How to eval isImmutable?") *)

let eval_binary astate f aexpr1 aexpr2 =
  match f with
  | Equals when AccessExpr.equal aexpr1 aexpr2 ->
      true
  | Equals ->
      let value1 = eval_term astate aexpr1 in
      let value2 = eval_term astate aexpr2 in
      let cond = Domain.PathCond.make_physical_equals Binop.Eq value1 value2 in
      Domain.is_valid_pc astate cond
  | IsFunctionOf ->
      true


(* raise (TODO "How to eval isFunctionOf?") *)

let rec eval_formula astate f =
  match f with
  | Neg formula' ->
      not (eval_formula astate formula')
  | Atom True ->
      true
  | Atom (Predicate (Unary f, [aexpr])) ->
      eval_unary astate f aexpr
  | Atom (Predicate (Binary f, [aexpr1; aexpr2])) ->
      eval_binary astate f aexpr1 aexpr2
  | _ as formula ->
      L.(die InternalError) "Invalid formula: %a@." pp_formula formula


let check ~get_summary specs : Row.t =
  List.fold specs ~init:[] ~f:(fun acc (Specification.{mthd; post; id} as spec) ->
      let summaries = get_summary mthd in
      let debug_file = id ^ ".debug" in
      let debug_msg = ref "" in
      let is_valid =
        List.for_all summaries ~f:(fun summary ->
            let result = (not (SpecCheckerDomain.is_npe_alternative summary)) || eval_formula summary post in
            if Domain.is_npe_alternative summary then
              debug_msg :=
                String.concat ~sep:""
                  [ !debug_msg
                  ; F.asprintf "====== Summary ======@.%a@.%a@. - Result: %b@." Domain.pp summary Specification.pp
                      spec result ] ;
            result)
      in
      if String.equal !debug_msg "" then () else print_to_file ~msg:!debug_msg ~filename:debug_file ;
      acc @ [(id, is_valid)])


let launch ~get_summary =
  let specs = Specification.from_marshal_all () in
  let row = check ~get_summary specs in
  Row.write_to_csv row (Config.results_dir ^/ "verify.csv")
