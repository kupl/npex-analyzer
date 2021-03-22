open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Node = InstrNode

type exec =
     Domain.t
  -> Procdesc.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> Procname.t
  -> Ident.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> Domain.t list

type model = (Procname.t -> Sil.instr -> bool) * exec

let cast : model =
  let is_model callee _ = String.equal "__cast" (Procname.get_method callee) in
  let exec astate _ node instr _ (ret_id, _) arg_typs =
    (* ret_typ of__cast is Boolean, but is actually pointer type *)
    let arg_exp, _ = List.hd_exn arg_typs in
    (* TODO: check the logic is correct *)
    let value = Domain.eval astate node instr arg_exp in
    (* let value = Domain.Val.make_extern instr_node Typ.void_star in *)
    [Domain.store_reg astate ret_id value]
  in
  (is_model, exec)


let instanceof : model =
  let is_model callee _ = String.equal "__instanceof" (Procname.get_method callee) in
  let exec astate _ node instr callee (ret_id, _) arg_typs =
    let instr_node = Node.of_pnode node instr in
    (* TODO: add type checking by using sizeof_exp and get_class_name_opt *)
    match arg_typs with
    | [(arg_exp, _); (Exp.Sizeof {typ}, _)] ->
        let arg_value = Domain.eval astate node instr arg_exp in
        let typ_value = Typ.to_string typ |> Domain.Val.make_string in
        let null_cond op = Domain.PathCond.make_physical_equals op arg_value (Domain.Val.make_null instr_node) in
        let null_states =
          Domain.add_pc astate (null_cond Binop.Eq)
          |> List.map ~f:(fun astate' -> Domain.store_reg astate' ret_id Domain.Val.zero)
        in
        let non_null_states =
          Domain.add_pc astate (null_cond Binop.Ne)
          |> List.concat_map ~f:(fun astate' ->
                 Domain.bind_extern_value astate' instr_node (ret_id, Typ.int) callee [arg_value; typ_value])
        in
        null_states @ non_null_states
    | _ ->
        L.(die InternalError) "wrong invariant of instanceof"
  in
  (is_model, exec)


let unwrap_exception : model =
  let is_model callee _ = String.equal "__unwrap_exception" (Procname.get_method callee) in
  let exec astate _ node instr _ (ret_id, _) arg_typs =
    let arg_exp, _ = List.hd_exn arg_typs in
    try
      let value = Domain.eval astate node instr arg_exp |> Domain.Val.unwrap_exn in
      [Domain.unwrap_exception (Domain.store_reg astate ret_id value)]
    with Unexpected msg -> L.(die InternalError) "%s@.%a@." msg Domain.pp astate
  in
  (is_model, exec)


let invoke : model =
  let is_model callee instr =
    match instr with
    | Sil.Call (_, _, arg_typs, _, _) ->
        String.equal "invoke" (Procname.get_method callee) && Int.equal (List.length arg_typs) 3
    | _ ->
        false
  in
  let exec astate proc_desc node instr callee (ret_id, _) arg_typs =
    let[@warning "-8"] ((mthd_exp, _) :: (this_exp, _) :: (arg_arr_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let mthd_value = Domain.eval astate node instr mthd_exp in
    let this_value = Domain.eval astate node instr this_exp in
    let arg_arr_value = Domain.eval astate node instr arg_arr_exp in
    let arg_values =
      let arg_arr_loc = Domain.Val.to_loc arg_arr_value in
      let rec collect_arg_values acc i loc =
        let index_loc = Domain.Loc.append_index ~index:(SymDom.SymExp.of_intlit (IntLit.of_int i)) loc in
        if Domain.is_unknown_loc astate index_loc then acc
        else collect_arg_values (acc @ [Domain.read_loc astate index_loc]) (i + 1) index_loc
      in
      let arg_values = collect_arg_values [] 0 arg_arr_loc in
      mthd_value :: this_value :: arg_values
    in
    let ex_state = Domain.bind_exn_extern astate instr_node (Procdesc.get_ret_var proc_desc) callee arg_values in
    let normal_state = Domain.bind_extern_value astate instr_node (ret_id, Typ.void_star) callee arg_values in
    normal_state @ ex_state
  in
  (is_model, exec)


let getter : model =
  (* Modeling getter method (e.g., p.getField() returns p.field) *)
  let is_model callee instr =
    match instr with
    | Sil.Call (_, _, arg_typs, _, {cf_virtual}) when cf_virtual ->
        String.is_prefix (Procname.get_method callee) ~prefix:"get"
        && List.hd_exn arg_typs |> snd |> Typ.is_pointer
    | _ ->
        false
  in
  let exec astate _ node instr callee (ret_id, ret_typ) arg_typs =
    let fieldname = String.chop_prefix_exn (Procname.get_method callee) ~prefix:"get" |> String.uncapitalize in
    let instr_node = Node.of_pnode node instr in
    let this_type_loc =
      let this_loc =
        let arg_exp, _ = List.hd_exn arg_typs in
        Domain.eval_lv astate node instr arg_exp
      in
      let field_class = Typ.Name.Java.from_string (String.capitalize fieldname) in
      let field_name = Fieldname.make field_class fieldname in
      Domain.Loc.append_field this_loc ~fn:field_name
    in
    let value =
      if Domain.is_unknown_loc astate this_type_loc then Domain.Val.make_extern instr_node ret_typ
      else Domain.read_loc astate this_type_loc
    in
    let astate_field_stored = Domain.store_loc astate this_type_loc value in
    [Domain.store_reg astate_field_stored ret_id value]
  in
  (is_model, exec)


let hasNext : model =
  (* TODO: more precise modeling with next 
   * Current: a.hasNext() with same allocsite will return other value by a.next() *)
  let is_model callee _ = String.equal "hasNext" (Procname.get_method callee) in
  let exec astate _ _ _ _ (ret_id, _) _ = [Domain.store_reg astate ret_id Domain.Val.intTop] in
  (is_model, exec)


(* let next : model =
  let is_model callee instr =
    match instr with
    | Sil.Call (_, _, arg_typs, _, {cf_virtual}) when cf_virtual && Int.equal (List.length arg_typs) 1 ->
        String.equal "next" (Procname.get_method callee)
    | _ ->
        false
  in
  let exec astate _ node instr _ (ret_id, _) arg_typs = [] in
  (is_model, exec) *)

let models : model list = [cast; instanceof; unwrap_exception; invoke; getter; hasNext]

let find_model_opt callee instr = List.find models ~f:(fun (is_model, _) -> is_model callee instr)

let is_model callee instr = find_model_opt callee instr |> Option.is_some

let exec_model : exec =
 fun astate proc_desc node instr callee (ret_id, ret_typ) arg_typs ->
  match find_model_opt callee instr with
  | Some (_, exec) ->
      exec astate proc_desc node instr callee (ret_id, ret_typ) arg_typs
  | None ->
      []
