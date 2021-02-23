open! IStd
module Node = Program.Node
module NSet = Program.NSet

type t =
  { mthd: Procname.t
  ; conditional: (InstrNode.t * InstrNode.t) option
  ; is_checking_nullness: bool
  ; null_exp: Exp.t
  ; skipped_nodes: NSet.t
  ; null_exec_nodes: NSet.t }

val pp : Format.formatter -> t -> unit

val get_method : t -> Procname.t

val get_null_exp : t -> Exp.t

val get_interesting_nodes : t -> Node.t list

val create : Program.t -> patch_json_path:string -> t
