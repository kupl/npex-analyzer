open! IStd
open! Vocab
module F = Format
module L = Logging

type t = {deref_field: string; node: InterNode.t; instr: Sil.instr; null_exp: Exp.t; null_access_expr: AccessExpr.t}

let pp fmt {node; instr; null_exp; null_access_expr} =
  F.fprintf fmt "@[<v2>{ " ;
  F.fprintf fmt "IR node: %a@," InterNode.pp node ;
  F.fprintf fmt "SIL instruction: %a@," (Sil.pp_instr ~print_types:true Pp.text) instr ;
  F.fprintf fmt "IR null-expr: %a@," Exp.pp null_exp ;
  F.fprintf fmt "AccessExpr of null-expr: %a@," AccessExpr.pp null_access_expr ;
  F.fprintf fmt "Entry Method of null-expr: %a@," AccessExpr.pp null_access_expr


let pp_IR_nullpoint fmt (node, instr, null_exp) =
  F.fprintf fmt "@[<v2>{ " ;
  F.fprintf fmt "IR node: %a@," InterNode.pp (InterNode.of_pnode node) ;
  F.fprintf fmt "SIL instruction: %a@," (Sil.pp_instr ~print_types:true Pp.text) instr ;
  F.fprintf fmt "IR null-expr: %a@," Exp.pp null_exp


let find_npe program loc deref_field =
  let instr_nodes =
    Program.find_node_with_location program loc
    |> List.map ~f:InterNode.pnode_of
    |> List.concat_map ~f:InstrNode.list_of_pnode
  in
  let node, instr, null_exp, null_access_expr =
    let find_aexpr_from_exp_opt pdesc node instr ~deref_field exp =
      match AccessExpr.from_IR_exp_opt pdesc exp with
      | Some aexpr when String.equal deref_field (AccessExpr.get_deref_field aexpr) ->
          Some (node, instr, exp, aexpr)
      | Some _ ->
          (* let aexpr_field = AccessExpr.get_deref_field aexpr in
             L.progress "%s is not matched to %s: %b@." deref_field aexpr_field (String.equal deref_field aexpr_field) ; *)
          None
      | None ->
          L.progress "[Warning]: %a is unconvertable at %a@." Exp.pp exp InstrNode.pp
            (InstrNode.of_pnode node instr) ;
          None
    in
    List.find_map_exn instr_nodes ~f:(fun instr_node ->
        let node = InstrNode.inode_of instr_node |> InterNode.pnode_of in
        let instr = InstrNode.get_instr instr_node in
        let pdesc = Procdesc.Node.get_proc_name node |> Program.pdesc_of program in
        (* L.progress " - finding nullpoint from %a@." InstrNode.pp instr_node ; *)
        if Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.Start_node then
          let formals = Procdesc.get_pvar_formals pdesc in
          List.map ~f:(fun (pv, _) -> Exp.Lvar pv) formals
          |> List.find_map ~f:(find_aexpr_from_exp_opt pdesc node instr ~deref_field)
        else
          match instr with
          | Sil.Call ((ret_id, _), _, arg_typs, _, _) as instr ->
              let exprs = Exp.Var ret_id :: List.map ~f:fst arg_typs in
              List.find_map exprs ~f:(find_aexpr_from_exp_opt pdesc node instr ~deref_field)
          | Sil.Load {id} as instr ->
              find_aexpr_from_exp_opt pdesc node instr ~deref_field (Exp.Var id)
          | Sil.Store {e2= Exp.Const (Const.Cint intlit) as e2} as instr
            when IntLit.isnull intlit && String.equal deref_field "null" ->
              (* Null source *)
              Some (node, instr, e2, AccessExpr.null)
          | _ ->
              None)
  in
  let nullpoint : t = {deref_field; node= InterNode.of_pnode node; instr; null_exp; null_access_expr} in
  nullpoint


let from_error_report program filepath : t =
  (* Parse JSON file *)
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let json = read_json_file_exn filepath in
  let open Yojson.Basic.Util in
  let deref_location =
    let file = json |> member "filepath" |> to_string |> source_file_from_string source_files in
    let line = json |> member "line" |> to_int in
    Location.{line; file; col= -1}
  in
  let deref_field = json |> member "deref_field" |> to_string in
  find_npe program deref_location deref_field


let from_alarm_report program filepath : t =
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let open Yojson.Basic.Util in
  let json = read_json_file_exn filepath |> to_list |> List.hd_exn in
  let deref_location =
    let line = json |> member "line" |> to_int in
    let file = json |> member "file" |> to_string |> source_file_from_string source_files in
    Location.{line; file; col= -1}
  in
  let deref_field =
    let msg_description = json |> member "qualifier" |> to_string in
    let null_expression = List.nth_exn (String.split msg_description ~on:'`') 1 in
    (* let msg_null_pointer = String.chop_suffix_exn ~suffix:"could be null" msg_description in
       let null_expression = List.nth_exn (String.split msg_null_pointer ~on:'`') 1 in *)
    let last_expression = List.hd_exn (List.rev (String.split null_expression ~on:'.')) in
    List.hd_exn (String.split last_expression ~on:'(')
  in
  find_npe program deref_location deref_field


let nullpoint_list = ref []

let get_nullpoint_list program =
  if List.is_empty !nullpoint_list then
    let results = List.map Config.error_report_json ~f:(from_error_report program) in
    if List.is_empty results then L.(die ExternalError) "No NullPoint Matched to error report@."
    else (
      nullpoint_list := results ;
      results )
  else !nullpoint_list


let get_line {node} = (InterNode.get_loc node).Location.line

let get_procname {node} = InterNode.get_proc_name node

let get_method np = Procname.get_method (get_procname np)

let get_pdesc np = Option.value_exn (Procdesc.load (get_procname np))
