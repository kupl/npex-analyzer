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

let eval_term_cache = ref AccessExpr.Map.empty

let eval_term_exn astate = function
  | AccessExpr.AccessExpr (pv, accesses) when Pvar.is_global pv ->
      let base = Domain.Loc.of_pvar pv in
      let loc =
        List.fold accesses ~init:base ~f:(fun acc access ->
            match access with
            | AccessExpr.FieldAccess fn ->
                Domain.Loc.append_field acc ~fn
            | _ ->
                raise (TODO "Spec should not contain array or method invocation"))
      in
      Domain.read_loc astate loc
  | AccessExpr.AccessExpr (pv, accesses) ->
      let base = Domain.Loc.of_pvar pv in
      let loc =
        List.fold accesses ~init:base ~f:(fun acc access ->
            if Domain.is_unknown_loc astate acc then raise (Unexpected "Bottom")
            else
              let acc_loc = Domain.read_loc astate acc |> Domain.Val.to_loc in
              match access with
              | AccessExpr.FieldAccess fn ->
                  Domain.Loc.append_field acc_loc ~fn
              | _ ->
                  raise (TODO "Spec should not contain array or method invocation"))
      in
      Domain.read_loc astate loc
  | AccessExpr.Primitive (Const.Cint intlit) when IntLit.isnull intlit ->
      Domain.Val.make_null InstrNode.dummy
  | AccessExpr.Primitive const ->
      Domain.Val.of_const const


let eval_term astate aexpr =
  try eval_term_exn astate aexpr with
  | Unexpected "Bottom" ->
      Domain.Val.top
  | Unexpected msg ->
      L.progress "[WARNING]: error occurs during evaluating %a:@. - Msg: %s@." AccessExpr.pp aexpr msg ;
      Domain.Val.top
  | TODO _ ->
      Domain.Val.top


let eval_term astate aexpr =
  match AccessExpr.Map.find_opt aexpr !eval_term_cache with
  | Some value ->
      value
  | None ->
      let value = eval_term astate aexpr in
      eval_term_cache := AccessExpr.Map.add aexpr value !eval_term_cache ;
      value


let eval_unary astate f term =
  let value = eval_term astate term in
  match f with
  | IsConstant ->
      Domain.Val.is_constant value
  | IsImmutable ->
      (* raise (TODO "How to eval isImmutable?") *)
      true


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
      (* raise (TODO "How to eval isFunctionOf?") *)
      true


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


let debug_check ~get_summary specs id_valid_map =
  List.iter specs ~f:(fun (Specification.{mthd; id} as spec) ->
      let summaries = get_summary mthd in
      let debug_file = id ^ ".debug" in
      let debug_msg =
        List.fold (List.filter summaries ~f:SpecCheckerDomain.is_npe_alternative) ~init:""
          ~f:(fun debug_msg summary ->
            let result = String.Map.find_exn id_valid_map id in
            String.concat ~sep:""
              [ debug_msg
              ; F.asprintf "====== Summary ======@.%a@.%a@. - Result: %b@." Domain.pp summary Specification.pp spec
                  result ])
      in
      if String.equal debug_msg "" then () else print_to_file ~msg:debug_msg ~filename:debug_file)


let check ~get_summary specs : Row.t =
  let summaries_patititioned =
    let add_summary acc spec =
      let proc_name = spec.Specification.mthd in
      match Procname.Map.find_opt proc_name acc with
      | None ->
          Procname.Map.add proc_name [spec] acc
      | Some specs ->
          Procname.Map.add proc_name (spec :: specs) acc
    in
    List.fold specs ~init:Procname.Map.empty ~f:add_summary
  in
  let initial_validity_map =
    List.fold specs ~init:String.Map.empty ~f:(fun acc Specification.{id} ->
        String.Map.add_exn acc ~key:id ~data:true)
  in
  let eval_state specs id_valid_map astate =
    eval_term_cache := AccessExpr.Map.empty ;
    List.fold ~init:id_valid_map specs ~f:(fun acc Specification.{id; post} ->
        String.Map.change acc id ~f:(function
          | Some false ->
              Some false
          | _ ->
              let is_valid = eval_formula astate post in
              Some is_valid))
  in
  let id_valid_map =
    Procname.Map.fold
      (fun proc_name specs acc ->
        let summaries = get_summary proc_name |> List.filter ~f:Domain.is_npe_alternative in
        List.fold summaries ~init:acc ~f:(eval_state specs))
      summaries_patititioned initial_validity_map
  in
  if Config.debug_mode then debug_check ~get_summary specs id_valid_map ;
  String.Map.fold id_valid_map ~init:[] ~f:(fun ~key:id ~data:is_valid acc -> acc @ [(id, is_valid)])


let launch ~get_summary =
  let specs = Specification.from_marshal_all () in
  let row = check ~get_summary specs in
  Row.write_to_csv row (Config.results_dir ^/ "verify.csv")
