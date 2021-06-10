module Loc = SymDom.Loc
module Val = SymDom.Val
module PathCond = SymDom.PathCond
module PC = SymDom.PC
module Reg = SymDom.Reg
module Mem = SymDom.Mem

type t =
  { reg: Reg.t
  ; mem: Mem.t
  ; pc: PC.t
  ; is_npe_alternative: bool
  ; is_exceptional: bool
  ; applied_models: NullModel.t
  ; probability: float
  ; fault: NullPoint.t option
  ; nullptrs: Val.Set.t
  ; executed_procs: Procname.Set.t
  ; is_infer_failed: bool }

val pp : Format.formatter -> t -> unit

val leq : lhs:t -> rhs:t -> bool

val bottom : t

val is_bottom : t -> bool

val init : Procdesc.t -> t

val is_unknown_loc : t -> Loc.t -> bool

val is_unknown_id : t -> Ident.t -> bool

val is_valid_pc : t -> PathCond.t -> bool

val is_npe_alternative : t -> bool

val is_exceptional : t -> bool

val is_infer_failed : t -> bool

val is_inferred : t -> bool

val is_fault_null : t -> Val.t -> bool

val joinable : t -> t -> bool

val unify : t -> t -> t * t

val all_values : t -> Val.Set.t

val equal_values : t -> Val.t -> Val.t list

val inequal_values : t -> Val.t -> Val.t list

val collect_summary_symbols : t -> Val.Set.t

val resolve_unknown_loc : t -> Typ.t -> Loc.t -> t

val resolve_summary : t -> actual_values:Val.t list -> formals:(Pvar.t * Typ.t) list -> t -> t option

val bind_exn_extern : t -> InstrNode.t -> Pvar.t -> Procname.t -> Val.t list -> t list

val bind_extern_value : t -> InstrNode.t -> Ident.t * Typ.t -> Procname.t -> Val.t list -> t list

val eval : ?pos:int -> t -> Procdesc.Node.t -> Sil.instr -> Exp.t -> Val.t

val eval_lv : t -> Procdesc.Node.t -> Sil.instr -> Exp.t -> Loc.t

val remove_temps : t -> line:int -> Var.t list -> t

val remove_pvar : t -> line:int -> pv:Pvar.t -> t

val remove_locals : t -> pdesc:Procdesc.t -> t

val replace_value : t -> src:Val.t -> dst:Val.t -> t

val read_loc : t -> Loc.t -> Val.t

val read_id : t -> Ident.t -> Val.t

val store_loc : t -> Loc.t -> Val.t -> t

val store_reg : t -> Ident.t -> Val.t -> t

val add_model : t -> NullModel.Pos.t -> NullModel.MValue.t -> t list

val set_exception : t -> t

val set_fault : t -> nullpoint:NullPoint.t -> t

val set_infer_failed : t -> t

val get_nullptrs : t -> Val.Set.t

val set_nullptrs : t -> Val.Set.t -> t

val add_executed_proc : t -> Procname.t -> t

val add_pc : ?is_branch:bool -> t -> PathCond.t -> t list

val remove_unreachables : t -> t

val mark_npe_alternative : t -> t

val unwrap_exception : t -> t

val append_ctx : t -> int -> t

val weak_join : t -> t -> t

val merge : t list -> t list

val cardinal : t -> int
