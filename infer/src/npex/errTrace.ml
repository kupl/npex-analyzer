open! IStd
open! Vocab
module L = Logging
module F = Format
module Node = InterNode

type node_kind = Intra | Call | CallRet | Entry | Sink [@@deriving compare]

type node = InstrNode.t * node_kind [@@deriving compare]

let equal_node_kind = [%compare.equal: node_kind]

let equal_node = [%compare.equal: node]

let to_string_node_kind = function
  | Intra ->
      "Intra"
  | Call ->
      "Call"
  | CallRet ->
      "CallRet"
  | Entry ->
      "Entry"
  | Sink ->
      "Sink"


let pp_node fmt (instr_node, node_kind) =
  F.fprintf fmt "(%a, %s)" InstrNode.pp instr_node (to_string_node_kind node_kind)


type t = node list

let pp fmt path = F.fprintf fmt "%a" (Pp.seq ~sep:"\n" pp_node) path

module APath = struct
  type t = {path: node Array.t; last: int; visited: InstrNode.Set.t list; callstack: InstrNode.t list}

  let pp fmt {path; last; visited; callstack} =
    F.fprintf fmt "==== Path info ====@. - Path: %a@. - Last: %a@. - Visited: %a@. - Callstack: %a@.==========@."
      (Pp.seq ~sep:"\n" pp_node) (Array.to_list path) pp_node path.(last) (Pp.seq InstrNode.Set.pp ~sep:"\n")
      visited (Pp.seq InstrNode.pp) callstack


  let get_last {path; last} = path.(last)

  let last_callsite {callstack} = List.hd callstack

  let make_node instr_node node_kind : node = (instr_node, node_kind)

  let append_path {path; last; visited; callstack} node : t option =
    let last_node = path.(last) in
    let[@warning "-8"] (cur_visited :: rest_visited) = visited in
    let path = Array.append path (Array.create ~len:1 node) in
    let last = last + 1 in
    match (snd last_node, snd node) with
    | Call, Entry when List.mem callstack ~equal:InstrNode.equal (fst last_node) ->
        None
    | Call, Entry ->
        Some {path; last; visited= InstrNode.Set.empty :: visited; callstack= fst last_node :: callstack}
    | Intra, CallRet ->
        Some {path; last; visited= rest_visited; callstack= List.tl_exn callstack}
    | _ -> (
      match InstrNode.get_kind (fst node) with
      | (Stmt_node _ | Prune_node _) when InstrNode.Set.mem (fst node) cur_visited ->
          (* Visited *)
          None
      | Prune_node _ ->
          (* Record new visited *)
          let visited' = InstrNode.Set.add (fst node) cur_visited :: rest_visited in
          Some {path; last; visited= visited'; callstack}
      | _ ->
          (* No record for non-prune node *)
          Some {path; last; visited; callstack} )


  let init node = {path= Array.create ~len:1 node; last= 0; visited= [InstrNode.Set.empty]; callstack= []}

  let to_trace {path} = Array.to_list path
end

let callees_of_instr program instr_node = Program.callees_of_instr_node program instr_node

let paths_from_entry program entry_proc ~is_last : t list =
  let initial_path : APath.t =
    let entry_node = Program.get_entry_instr_node program entry_proc in
    APath.make_node entry_node Entry |> APath.init
  in
  let append_path (path : APath.t) instr_node : APath.t option =
    let InstrNode.{inode; instr} = instr_node in
    if InterNode.is_entry inode then APath.append_path path (APath.make_node instr_node Entry)
    else
      match (APath.get_last path, instr) with
      | _, Sil.Call (_, Const (Cfun procname), _, _, _) when List.is_empty (callees_of_instr program instr_node) ->
          if Program.is_library_call program instr_node then
            APath.append_path path (APath.make_node instr_node Intra)
          else if String.is_prefix (Procname.get_method procname) ~prefix:"__" then
            APath.append_path path (APath.make_node instr_node Intra)
          else (
            L.progress "Callees of %a is empty@." InstrNode.pp instr_node ;
            None )
      | (node, Intra), Sil.Call _
        when Procname.equal (InstrNode.get_proc_name node) (InstrNode.get_proc_name instr_node) ->
          APath.append_path path (APath.make_node instr_node Call)
      | (node, Intra), Sil.Call _ when InstrNode.is_exit node ->
          APath.append_path path (APath.make_node instr_node CallRet)
      | (_, Call), _ when InstrNode.is_entry instr_node ->
          APath.append_path path (APath.make_node instr_node Entry)
      | _ ->
          APath.append_path path (APath.make_node instr_node Intra)
  in
  let rec run_worklist worklist acc =
    if List.is_empty worklist then acc
    else
      let[@warning "-8"] (work :: rest) = worklist in
      L.progress "number of worklist : %d@." (List.length worklist) ;
      if Config.debug_mode then L.progress "@.===WORK===@.%a@." APath.pp work ;
      match APath.get_last work with
      | node, Intra when is_last node ->
          run_worklist rest (work :: acc)
      | node, Intra when InstrNode.is_exit node && Procname.equal entry_proc (InstrNode.get_proc_name node) ->
          run_worklist rest acc
      | node, Intra when InstrNode.is_exit node -> (
        match APath.last_callsite work with
        | Some callsite -> (
          match append_path work callsite with
          | Some nextwork ->
              run_worklist (nextwork :: rest) acc
          | None ->
              run_worklist rest acc )
        | None ->
            run_worklist rest acc )
      | node, Intra | node, CallRet | node, Entry ->
          let succs = Program.succ_instr_node program node in
          let next_works = List.filter_map succs ~f:(append_path work) in
          run_worklist (next_works @ rest) acc
      | node, Call ->
          let callees = callees_of_instr program node in
          (* call-node -> callee-entry *)
          let next_works =
            List.filter_map callees ~f:(fun callee ->
                L.progress "[DEBUG]: callee: %a@." Procname.pp callee ;
                let next_node = Program.get_entry_instr_node program callee in
                append_path work next_node)
          in
          run_worklist (next_works @ rest) acc
      | _ ->
          acc
  in
  run_worklist [initial_path] [] |> List.map ~f:APath.to_trace


let paths_from_callgraph program nullpoint =
  let NullPoint.{node; instr} = nullpoint in
  List.fold (Program.get_entries program) ~init:[] ~f:(fun acc entry_proc ->
      let paths =
        paths_from_entry program entry_proc ~is_last:(fun last_node ->
            InstrNode.equal (InstrNode.make node instr) last_node)
      in
      paths @ acc)


let from_call_trace program nullpoint =
  let traces = paths_from_callgraph program nullpoint in
  if Config.debug_mode then L.progress "===PATH===@.%a@.====@." (Pp.seq ~sep:"\n\n" pp) traces ;
  traces
