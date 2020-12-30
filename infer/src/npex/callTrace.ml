open! IStd
open! Vocab
module L = Logging
module F = Format
module Node = InterNode
module LocMap = PrettyPrintable.MakePPMap (Location)

let proc_from_loc program loc : Procname.t =
  let nodes = Program.find_node_with_location program loc in
  Node.get_proc_name (List.hd_exn nodes)


let equal_method callee_name proc_name = String.equal callee_name (Procname.get_method proc_name)

let is_feasible_call program instr callee =
  let pdesc = Program.pdesc_of program callee in
  let formals = Procdesc.get_formals pdesc in
  match instr with
  | Sil.Call (_, Const (Cfun procname), _, _, _) when Procname.is_constructor procname ->
      Procname.equal procname callee
  | Sil.Call ((_, ret_typ), _, arg_typs, _, _) when Int.equal (List.length arg_typs) (List.length formals) ->
      let ret_typ' = Procdesc.get_ret_type pdesc in
      List.fold2_exn ~init:(Program.is_consistent_type ret_typ ret_typ') arg_typs formals
        ~f:(fun acc (_, arg_typ) (_, fm_typ) -> acc && Program.is_consistent_type arg_typ fm_typ)
  | Sil.Call _ ->
      false
  | _ ->
      L.(die InternalError) "%a is not call node" (Sil.pp_instr ~print_types:true Pp.text) instr


let find_instr_node _ callee_name nodes =
  let nodes =
    List.filter_map nodes ~f:(fun node ->
        Instrs.find_map (Node.get_instrs node) ~f:(function
          | Sil.Call (_, Const (Cfun procname), _, _, _) as instr when equal_method callee_name procname ->
              Some (InstrNode.make node instr)
          | _ ->
              None))
  in
  if List.length nodes > 1 && not (String.equal "<init>" callee_name) then
    L.progress "[WARNING]: nodes with same call name : %s at %a@." callee_name Location.pp_file_pos
      (InstrNode.get_loc (List.hd_exn nodes)) ;
  nodes


let find_init_node _ class_name nodes =
  List.filter_map nodes ~f:(fun node ->
      Instrs.find_map (Node.get_instrs node) ~f:(function
        | Sil.Call (_, Const (Cfun procname), _, _, _) as instr when Procname.is_constructor procname -> (
          match Procname.get_class_name procname with
          | Some class_name' when String.equal class_name class_name' ->
              Some (InstrNode.make node instr)
          | _ ->
              None )
        | _ ->
            None))


(* |> List.filter ~f:(fun node -> List.is_empty (Program.callees_of_instr_node program node)) *)

let find_instr_from_loc_callee_name program loc callee_name =
  let nodes = Program.find_node_with_location program loc in
  let nodes_matching_callee_name = find_instr_node program callee_name nodes in
  if List.is_empty nodes_matching_callee_name then
    let nodes_matching_callee_class = find_init_node program callee_name nodes in
    if List.is_empty nodes_matching_callee_class then (
      if String.contains callee_name '$' then () (* e.g., access$200, #Jacocoinit *)
      else
        (* L.(die InternalError) *)
        L.progress "[WARNING]: Cannot find call_instr to call %s at %a:@.%a@." callee_name Location.pp_file_pos loc
          (Pp.seq ~sep:"\n" (Sil.pp_instr ~print_types:true Pp.text))
          (List.concat_map (List.map nodes ~f:Node.pnode_of) ~f:get_instrs_list) ;
      [] )
    else nodes_matching_callee_class
  else nodes_matching_callee_name


let add_init program init_nodes =
  List.iter init_nodes ~f:(fun instr_node ->
      match InstrNode.get_instr instr_node with
      | Sil.Call (_, Const (Cfun procname), _, _, _)
        when Procname.is_constructor procname && Program.is_undef_proc program procname ->
          Program.add_library_call program instr_node
      | Sil.Call (_, Const (Cfun procname), _, _, _) when Procname.is_constructor procname ->
          Program.add_call_edge program instr_node procname
      | _ ->
          ())


let callgraph_from_trace program trace : unit =
  let _ =
    List.fold trace ~init:None ~f:(fun call_instr_node_opt (loc, info) ->
        match (call_instr_node_opt, info) with
        | Some call_instr_nodes, ErrInfo.Entry ->
            let callee = proc_from_loc program loc in
            (* For class init *)
            if String.equal "<clinit>" (Procname.get_method callee) then (
              add_init program call_instr_nodes ; Program.add_entry program callee ; None )
            else (
              List.iter call_instr_nodes ~f:(fun node ->
                  if is_feasible_call program (InstrNode.get_instr node) callee then
                    Program.add_call_edge program node callee
                  else Program.add_library_call program node) ;
              None )
        | Some call_instr_nodes, ErrInfo.Call callee_name ->
            let instr_nodes = find_instr_from_loc_callee_name program loc callee_name in
            List.iter call_instr_nodes ~f:(Program.add_library_call program) ;
            if List.is_empty instr_nodes then None else Some instr_nodes
        | Some call_instr_nodes, ErrInfo.Sink ->
            List.iter call_instr_nodes ~f:(Program.add_library_call program) ;
            None
        | None, ErrInfo.Entry ->
            let callee = proc_from_loc program loc in
            Program.add_entry program callee ; None
        | None, ErrInfo.Sink ->
            None
        | None, ErrInfo.Call callee_name ->
            let instr_nodes = find_instr_from_loc_callee_name program loc callee_name in
            if List.is_empty instr_nodes then None else Some instr_nodes
        | _, ErrInfo.Normal ->
            None)
  in
  ()


let from_alarm program trace =
  callgraph_from_trace program trace ;
  Program.print_callgraph program "callgraph.dot"
