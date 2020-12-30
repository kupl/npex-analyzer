open! IStd
open! Vocab
module L = Logging
module F = Format
module Node = InterNode

type t = {path: node Array.t; last: int; visited: InstrNode.Set.t list; callstack: InstrNode.t list}

and node = InstrNode.t * node_kind [@@deriving compare]

and node_kind = Intra | Call | CallRet | Entry | Sink [@@deriving compare]

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


let pp fmt {path; last; visited} =
  F.fprintf fmt "==== Path info ====@. - Path: %a@. - Last: %a@. - Visited: %a@." (Pp.seq ~sep:"\n" pp_node)
    (Array.to_list path) pp_node path.(last) (Pp.seq InstrNode.Set.pp ~sep:"\n") visited


let get_last {path; last} = path.(last)

let last_callsite {callstack} = List.hd callstack

let make_node instr_node node_kind : node = (instr_node, node_kind)

let append_path {path; last; visited; callstack} node : t option =
  let pid_current = InstrNode.get_proc_name (fst path.(last)) in
  let pid_target = InstrNode.get_proc_name (fst node) in
  let[@warning "-8"] (cur_visited :: rest_visited) = visited in
  if Procname.equal pid_current pid_target then
    match InstrNode.get_kind (fst node) with
    | Prune_node _ when InstrNode.Set.mem (fst node) cur_visited ->
        (* Visited *)
        None
    | Prune_node _ ->
        (* Record new visited *)
        let visited' = InstrNode.Set.add (fst node) cur_visited :: rest_visited in
        Some {path= Array.append path (Array.create ~len:1 node); last= last + 1; visited= visited'; callstack}
    | _ ->
        (* No record for non-prune node *)
        Some {path= Array.append path (Array.create ~len:1 node); last= last + 1; visited; callstack}
  else
    let path = Array.append path (Array.create ~len:1 node) in
    let last = last + 1 in
    match (snd path.(last - 1), snd node) with
    | Call, Entry ->
        Some {path; last; visited= InstrNode.Set.empty :: visited; callstack= fst path.(last - 1) :: callstack}
    | Intra, CallRet ->
        Some {path; last; visited= rest_visited; callstack= List.tl_exn callstack}
    (* | Intra, Entry ->
          Some {path; last; visited= [InstrNode.Set.empty]} *)
    | _ ->
        L.(die InternalError) "[%a] to [%a] is not continuous edge@." pp_node path.(last - 1) pp_node node


let init node = {path= Array.create ~len:1 node; last= 0; visited= [InstrNode.Set.empty]; callstack= []}

let to_trace {path} = Array.to_list path
