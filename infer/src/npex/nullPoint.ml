open! IStd
open! Vocab
module F = Format
module L = Logging

type t = {deref_field: string; node: InterNode.t; instr: Sil.instr; null_exp: Exp.t; null_access_expr: AccessExpr.t}
[@@deriving compare]

let dummy =
  { deref_field= ""
  ; node= InterNode.dummy (Procname.from_string_c_fun "NPEX_normal")
  ; instr= Sil.skip_instr
  ; null_exp= Const (Cint IntLit.zero)
  ; null_access_expr= AccessExpr.dummy }


let equal = [%compare.equal: t]

let pp fmt {node; instr; null_exp; null_access_expr} =
  F.fprintf fmt "@[<v2>{ " ;
  F.fprintf fmt "IR node: %a@," InterNode.pp node ;
  F.fprintf fmt "SIL instruction: %a@," (Sil.pp_instr ~print_types:true Pp.text) instr ;
  F.fprintf fmt "IR null-expr: %a@," Exp.pp null_exp ;
  F.fprintf fmt "AccessExpr of null-expr: %a@," AccessExpr.pp null_access_expr ;
  F.fprintf fmt "Entry Method of null-expr: %a }@]" AccessExpr.pp null_access_expr


let pp_IR_nullpoint fmt (node, instr, null_exp) =
  F.fprintf fmt "@[<v2>{ " ;
  F.fprintf fmt "IR node: %a@," InterNode.pp (InterNode.of_pnode node) ;
  F.fprintf fmt "SIL instruction: %a@," (Sil.pp_instr ~print_types:true Pp.text) instr ;
  F.fprintf fmt "IR null-expr: %a }@]" Exp.pp null_exp


let find_npe ~debug program loc deref_field : t list =
  let instr_nodes =
    Program.find_node_with_location program loc
    |> List.map ~f:InterNode.pnode_of
    |> List.concat_map ~f:InstrNode.list_of_pnode
    |> List.sort ~compare:InstrNode.compare
  in
  let find_aexpr_from_exp_opt pdesc node instr ~deref_field exp =
    match AccessExpr.from_IR_exp_opt pdesc exp with
    | Some aexpr when String.equal deref_field (AccessExpr.get_deref_field aexpr) ->
        Some {deref_field; node= InterNode.of_pnode node; instr; null_exp= exp; null_access_expr= aexpr}
    | Some aexpr ->
        let aexpr_field = AccessExpr.get_deref_field aexpr in
        L.(debug Analysis Verbose)
          "%s is not matched to %s: %b@." deref_field aexpr_field (String.equal deref_field aexpr_field) ;
        None
    | None ->
        L.(debug Analysis Verbose)
          "[Warning]: %a is unconvertable at %a@." Exp.pp exp InstrNode.pp (InstrNode.of_pnode node instr) ;
        None
  in
  if debug then L.progress "find null point in @[%a@]@." (Pp.seq ~sep:"\n" InstrNode.pp) instr_nodes ;
  List.filter_map instr_nodes ~f:(fun instr_node ->
      let node = InstrNode.inode_of instr_node |> InterNode.pnode_of in
      let instr = InstrNode.get_instr instr_node in
      let pdesc = Procdesc.Node.get_proc_name node |> Program.pdesc_of program in
      (* L.progress " - finding nullpoint from %a@." InstrNode.pp instr_node ; *)
      if Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.Start_node then
        (* TODO: find field of parameters *)
        let formals = Procdesc.get_pvar_formals pdesc in
        List.map ~f:(fun (pv, _) -> Exp.Lvar pv) formals
        |> List.find_map ~f:(find_aexpr_from_exp_opt pdesc node instr ~deref_field)
      else
        match instr with
        | Sil.Call ((ret_id, _), _, arg_typs, _, _) as instr ->
            let exprs = Exp.Var ret_id :: List.map ~f:fst arg_typs in
            List.find_map exprs ~f:(find_aexpr_from_exp_opt pdesc node instr ~deref_field)
        | Sil.Load {id} when Ident.is_none id ->
            None
        | Sil.Load {id} as instr ->
            find_aexpr_from_exp_opt pdesc node instr ~deref_field (Exp.Var id)
        | Sil.Store {e2= Exp.Const (Const.Cint intlit) as e2} as instr
          when IntLit.isnull intlit && String.equal deref_field "null" ->
            (* Null source *)
            Some
              {deref_field; node= InterNode.of_pnode node; instr; null_exp= e2; null_access_expr= AccessExpr.null}
        | _ ->
            None)


let from_error_report ~debug program filepath : t list =
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
  find_npe ~debug program deref_location deref_field

let nullpoint_list = ref []


let get_nullpoint_list ?(debug = false) program : t list =
  if List.is_empty !nullpoint_list then
    let results =
      List.concat_map Config.error_report_json ~f:(fun json ->
          try from_error_report ~debug program json with Unexpected msg -> L.progress "[ERROR]: %s@." msg ; [])
    in
    if List.is_empty results then L.(die ExternalError) "No NullPoint Matched to error report@."
    else (
      nullpoint_list := results ;
      results )
  else !nullpoint_list


let get_line {node} = (InterNode.get_loc node).Location.line

let get_procname {node} = InterNode.get_proc_name node

let get_method np = Procname.get_method (get_procname np)

let get_pdesc np = Option.value_exn (Procdesc.load (get_procname np))

let get_node {node} = node
