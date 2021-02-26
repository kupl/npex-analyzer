open! IStd
open! Vocab
module F = Format
module Node = Program.Node
module NSet = Program.NSet

type t =
  { mthd: Procname.t
  ; conditional: (InstrNode.t * InstrNode.t) option
  ; is_checking_nullness: bool
  ; null_exp: Exp.t
  ; skipped_nodes: NSet.t
  ; null_exec_nodes: NSet.t }

let pp fmt {mthd; conditional; is_checking_nullness; null_exp; skipped_nodes; null_exec_nodes} =
  match conditional with
  | Some (null_cond, _) ->
      F.fprintf fmt
        "@[<v> mthd: %a@,\
         conditional: %a@,\
         is_checking_nullness: %b@,\
         null_exp: %a@,\
         skipped_nodes: @[<v>%a@]@,\
         null_exec_nodes: @[<v>%a@]@,"
        Procname.pp mthd InstrNode.pp null_cond is_checking_nullness Exp.pp null_exp NSet.pp skipped_nodes NSet.pp
        null_exec_nodes
  | None ->
      F.fprintf fmt "Init-null-src patch (mthd: %a, null_exp: %a)" Procname.pp mthd Exp.pp null_exp


let identify_nodes_at_patched_lines program json =
  let open Yojson.Basic.Util in
  let source_path = json |> member "original_filepath" |> to_string in
  let lines = json |> member "patched_lines" |> to_list |> List.map ~f:to_int in
  let locations =
    List.map lines ~f:(fun line ->
        let file = source_file_from_string (Program.get_files program) source_path in
        Location.{line; file; col= -1})
  in
  List.concat_map locations ~f:(fun loc -> Program.find_node_with_location program loc)
  |> List.sort ~compare:Node.compare


let from_json program json : t =
  let patched_nodes = identify_nodes_at_patched_lines program json in
  L.progress "Patched nodes: %a@." (Pp.seq Node.pp ~sep:"\n") patched_nodes ;
  let deref_fields =
    List.map Config.error_report_json ~f:(fun filepath ->
        let open Yojson.Basic.Util in
        read_json_file_exn filepath |> member "deref_field" |> to_string)
  in
  let is_checking_nullness, null_exp = (ref false, ref Exp.null) in
  let null_cond =
    List.find_map patched_nodes ~f:(fun node ->
        let mthd = Node.get_proc_name node in
        let f instr =
          match instr with
          | Sil.Prune (UnOp (Unop.LNot, BinOp (Binop.Ne, null_ptr, Const (Cint intlit)), _), _, _, _)
            when IntLit.isnull intlit ->
              (* TODO: deref_field should be provided to find null_cond *)
              let null_aexpr = AccessExpr.from_IR_exp (Program.pdesc_of program mthd) null_ptr in
              if List.mem deref_fields (AccessExpr.get_deref_field null_aexpr) ~equal:String.equal then (
                is_checking_nullness := false ;
                null_exp := null_ptr ;
                Some (InstrNode.make node instr) )
              else None
          | Sil.Prune (BinOp (Binop.Eq, null_ptr, Const (Cint lit)), _, _, _) when IntLit.isnull lit ->
              let null_aexpr = AccessExpr.from_IR_exp (Program.pdesc_of program mthd) null_ptr in
              if List.mem deref_fields (AccessExpr.get_deref_field null_aexpr) ~equal:String.equal then (
                is_checking_nullness := true ;
                null_exp := null_ptr ;
                Some (InstrNode.make node instr) )
              else None
          | _ ->
              None
        in
        Instrs.find_map (Node.get_instrs node) ~f)
  in
  let non_null_cond =
    (* TODO: find non-null-cond by null-cond *)
    List.find_map patched_nodes ~f:(fun node ->
        let f instr =
          match instr with
          | Sil.Prune (UnOp (Unop.LNot, BinOp (Binop.Eq, _, Const (Cint intlit)), _), _, _, _)
            when IntLit.isnull intlit ->
              Some (InstrNode.make node instr)
          | Sil.Prune (BinOp (Binop.Ne, _, Const (Cint lit)), _, _, _) when IntLit.isnull lit ->
              Some (InstrNode.make node instr)
          | _ ->
              None
        in
        Instrs.find_map (Node.get_instrs node) ~f)
  in
  match (null_cond, non_null_cond) with
  | Some null_cond, Some non_null_cond ->
      let skipped_nodes, null_exec_nodes =
        ( Program.dom_reachables_of ~forward:true ~reflexive:false program
            (NSet.singleton (InstrNode.inode_of non_null_cond))
        , Program.dom_reachables_of ~forward:true ~reflexive:false program
            (NSet.singleton (InstrNode.inode_of null_cond)) )
      in
      let conditional = Some (null_cond, non_null_cond) in
      { mthd= InstrNode.get_proc_name null_cond
      ; conditional
      ; is_checking_nullness= !is_checking_nullness
      ; null_exp= !null_exp
      ; skipped_nodes
      ; null_exec_nodes }
  | None, None ->
      (* Currently, init-source patches are not supported. They should be given as a ternary patch *)
      let msgs =
        List.concat_map patched_nodes ~f:(fun n ->
            Instrs.fold (Node.get_instrs n) ~init:[] ~f:(fun acc instr ->
                let msg =
                  F.asprintf "[Instr in patched_nodes]: %a@." (Sil.pp_instr ~print_types:true Pp.text) instr
                in
                msg :: acc))
      in
      L.(die ExternalError) "Could not find patch@.%s@." (String.concat ~sep:"\n" msgs)
  | Some cond, None | None, Some cond ->
      L.(die InternalError) "Only one prune instr of null checking is found@. - %a@." InstrNode.pp cond


let get_method {mthd} = mthd

let get_null_exp {null_exp} = null_exp

let get_interesting_nodes {skipped_nodes; null_exec_nodes} =
  NSet.elements (NSet.union skipped_nodes null_exec_nodes)


let _cached = ref None

let create program ~patch_json_path =
  match Utils.read_json_file patch_json_path with
  | Ok json -> (
    match !_cached with
    | None ->
        let patch = from_json program json in
        _cached := Some patch ;
        patch
    | Some patch ->
        patch )
  | Error msg ->
      L.(die InternalError "Could not read or parse error report in %s:@\n%s@." patch_json_path msg)
