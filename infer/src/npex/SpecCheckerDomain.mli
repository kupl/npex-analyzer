module Loc = SymDom.Loc
module Val = SymDom.Val
module PathCond = SymDom.PathCond
module PC = SymDom.PC

module Reg : module type of WeakMap.Make (Ident) (Val)

module Mem : module type of WeakMap.Make (Loc) (Val)

type t = {reg: Reg.t; mem: Mem.t; pc: PC.t; is_npe_alternative: bool; is_exceptional: bool}

val pp : Format.formatter -> t -> unit

val leq : lhs:t -> rhs:t -> bool

val bottom : t

val is_bottom : t -> bool

val init_with_formals : (Pvar.t * Typ.t) list -> t

val is_unknown_loc : t -> Loc.t -> bool

val is_unknown_id : t -> Ident.t -> bool

val is_valid_pc : t -> PathCond.t -> bool

val is_npe_alternative : t -> bool

val is_exceptional : t -> bool

val joinable : t -> t -> bool

val all_values : t -> Val.Set.t

val equal_values : t -> Val.t -> Val.t list

val inequal_values : t -> Val.t -> Val.t list

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

val set_exception : t -> t

val add_pc : t -> PathCond.t -> t list

val mark_npe_alternative : t -> t

val unwrap_exception : t -> t

val append_ctx : t -> int -> t

val weak_join : t -> t -> t

val cardinal : t -> int
