open! IStd
open! Vocab
module Val = SymDom.Val
module Domain = SpecCheckerDomain

(** constants *)
module Node = InstrNode

module MValue = NullModel.MValue
module Pos = NullModel.Pos

let null_pos = -1

let is_model_null = function Val.Vheap (Null (_, pos)) -> Int.equal null_pos pos | _ -> false

let find_model_index astate node instr arg_values =
  List.find_mapi arg_values ~f:(fun i v ->
      let equal_values = Domain.equal_values astate v in
      if List.exists equal_values ~f:is_model_null then
        let instr_node = Node.of_pnode node instr in
        Some (instr_node, i)
      else None)


let exec_model astate proc_desc node instr (ret_id, _) arg_typs callee pos mval =
  let astate = Domain.add_model astate pos mval in
  let instr_node = Node.of_pnode node instr in
  match mval with
  | [MValue.NULL], _ when Procname.is_constructor callee ->
      (* new A(null) -> null *)
      let value = Domain.Val.make_null ~pos:null_pos instr_node in
      let[@warning "-8"] Exp.Var id, _ = List.hd_exn arg_typs in
      [Domain.store_reg astate id value]
  | [MValue.NULL], _ ->
      let value = Domain.Val.make_null ~pos:null_pos instr_node in
      [Domain.store_reg astate ret_id value]
  | [MValue.Const const], _ ->
      let value = Domain.eval astate node instr (Exp.Const const) in
      [Domain.store_reg astate ret_id value]
  | [MValue.Skip], _ ->
      [astate]
  | [MValue.Exn _], _ ->
      let exn_value = Domain.Val.make_allocsite instr_node |> Domain.Val.to_exn in
      let ret_loc = Procdesc.get_ret_var proc_desc |> Domain.Loc.of_pvar in
      let astate' = Domain.store_loc astate ret_loc exn_value |> Domain.set_exception in
      [astate']
  | _ ->
      (* TODO: define model execution *)
      raise (TODO (F.asprintf "undefined model execution: %a at %a" MValue.pp mval Pos.pp pos))


let exec astate null_model proc_desc node instr (ret_id, ret_typ) arg_typs callee =
  let arg_values = List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp) in
  match find_model_index astate node instr arg_values with
  | Some model_pos -> (
      L.d_printfln "*** Found model_index %a ***" Pos.pp model_pos ;
      match NullModel.find_opt model_pos null_model with
      | Some mvalues ->
          L.d_printfln "[SUCC] to find model: %a" NullModel.MValueSet.pp mvalues ;
          List.concat_map (NullModel.MValueSet.elements mvalues)
            ~f:(exec_model astate proc_desc node instr (ret_id, ret_typ) arg_typs callee model_pos)
      | None ->
          L.d_printfln "[FAIL] to find model, the state will be invalidated" ;
          [] )
  | None ->
      L.d_printfln "(* No model index in %a *)" (Pp.seq Domain.Val.pp) arg_values ;
      []
