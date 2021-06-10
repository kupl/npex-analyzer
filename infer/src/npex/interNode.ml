open! IStd
open! Vocab
module F = Format
module L = Logging

module InterNode = struct
  type t = Procname.t * Procdesc.Node.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let to_string (pid, n) =
    F.asprintf "%s-%a" (Procname.to_simplified_string ~withclass:true pid) Procdesc.Node.pp n


  let hash = Hashtbl.hash <<< to_string

  let create pid n = (pid, n)

  let pp fmt (pid, n) = F.fprintf fmt "(%a_%a)" Procname.pp pid Procdesc.Node.pp n

  let get_proc_name (proc_name, _) = proc_name

  let get_loc (_, pnode) = Procdesc.Node.get_loc pnode

  let get_succs (pid, pnode) = List.map (Procdesc.Node.get_succs pnode) ~f:(fun n -> (pid, n))

  let get_instrs (_, pnode) = Procdesc.Node.get_instrs pnode

  let get_kind (_, n) = Procdesc.Node.get_kind n

  let is_entry (_, n) = match Procdesc.Node.get_kind n with Start_node -> true | _ -> false

  let is_exit (_, n) = match Procdesc.Node.get_kind n with Exit_node -> true | _ -> false

  let pnode_of (_, pnode) = pnode

  let of_pnode pnode = (Procdesc.Node.get_proc_name pnode, pnode)

  let dummy proc : t = (proc, Procdesc.Node.dummy proc)
end

include InterNode

let pp_pnode fmt pnode = pp fmt (of_pnode pnode)

module Map = PrettyPrintable.MakePPMap (InterNode)
module Set = PrettyPrintable.MakePPSet (InterNode)
