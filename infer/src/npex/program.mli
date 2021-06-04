open! IStd
open! Vocab

module Node : module type of InterNode

module NSet : module type of PrettyPrintable.MakePPSet (Node)

module type IntraCfg = sig
  module G : module type of Graph.Imperative.Digraph.ConcreteBidirectional (Node)

  type t
end

type t

val build : unit -> t

val to_marshal : t -> unit

val from_marshal : unit -> t

val add_call_edge : t -> InstrNode.t -> Procname.t -> unit

val callers_of_instr_node : t -> InstrNode.t -> Procname.t list

val callees_of_instr_node : t -> InstrNode.t -> Procname.t list

val callers_of_proc : t -> Procname.t -> Procname.t list

val callees_of_proc : t -> Procname.t -> Procname.t list

val is_library_call : t -> InstrNode.t -> bool

val add_library_call : t -> InstrNode.t -> unit

val add_entry : t -> Procname.t -> unit

val get_entries : t -> Procname.t list

val has_instr : f:(Sil.instr -> bool) -> Node.t -> bool

val pdesc_of : t -> Procname.t -> Procdesc.t

val all_procs : t -> Procname.Set.t

val all_nodes : t -> InterNode.t list

val all_instr_nodes : t -> InstrNode.t list

val cg_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> Procname.Set.t -> Procname.Set.t

val cfg_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val dom_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val pdom_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val is_reachable : t -> Node.t -> Node.t -> bool

val is_undef_proc : t -> Procname.t -> bool

val dom : t -> Node.t -> Node.t -> bool

val pdom : t -> Node.t -> Node.t -> bool

val pred : t -> Node.t -> Node.t list

val succ : t -> Node.t -> Node.t list

val pred_instr_node : t -> InstrNode.t -> InstrNode.t list

val succ_instr_node : t -> InstrNode.t -> InstrNode.t list

val get_files : t -> SourceFile.t list

val get_nodes : t -> Procname.t -> Node.t list

val get_exit_node : t -> Procname.t -> Node.t

val get_entry_node : t -> Procname.t -> Node.t

val get_exit_instr_node : t -> Procname.t -> InstrNode.t

val get_entry_instr_node : t -> Procname.t -> InstrNode.t

val find_node_with_location : t -> Location.t -> Node.t list

val type_hierachy : t -> Typ.t -> Typ.t -> bool

val is_consistent_type : Typ.t -> Typ.t -> bool

val has_annot : t -> string -> Procname.t -> bool

val print_callgraph : t -> string -> unit

val slice_virtual_calls : t -> unit

val slice_procs_except : t -> Procname.Set.t -> unit
