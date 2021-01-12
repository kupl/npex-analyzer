module Loc = SymDom.Loc
module Val = SymDom.Val
module PathCond = SymDom.PathCond
module PC = SymDom.PC

module Reg : module type of WeakMap.Make (Ident) (Val)

module Mem : module type of WeakMap.Make (Loc) (Val)

module SymTbl : module type of PrettyPrintable.MakePPMonoMap (Loc) (Val)

type t = {reg: Reg.t; mem: Mem.t; symtbl: SymTbl.t; pc: PC.t; is_npe_alternative: bool; is_exceptional: bool}

type get_summary = Procname.t -> t option

val pp : Format.formatter -> t -> unit

val leq : lhs:t -> rhs:t -> bool

val bottom : t

val fold_memory : t -> init:'a -> f:('a -> Loc.t -> Val.t -> 'a) -> 'a

val init_with_formals : (Pvar.t * Typ.t) list -> t

val is_unknown_loc : t -> Loc.t -> bool

val is_unknown_id : t -> Ident.t -> bool

val resolve_unknown_loc : t -> Typ.t -> Loc.t -> t

val resolve_summary : t -> actual_values:Val.t list -> formals:(Pvar.t * Typ.t) list -> t -> t option

val eval : ?pos:int -> t -> Procdesc.Node.t -> Sil.instr -> Exp.t -> Val.t

val eval_lv : t -> Exp.t -> Loc.t

val remove_temps : t -> Var.t list -> t

val remove_pvar : t -> pv:Pvar.t -> t

val remove_locals : t -> locals:Pvar.t list -> t

val read_loc : t -> Loc.t -> Val.t

val read_symtbl : t -> Loc.t -> Val.t

val store_loc : t -> Loc.t -> Val.t -> t

val store_reg : t -> Ident.t -> Val.t -> t

val add_pc : t -> PathCond.t -> t list

val get_path_conditions : t -> PathCond.t list

val is_valid_pc : t -> PathCond.t -> bool

val pc_to_formula : t -> Specification.Conjunctions.t

val is_npe_alternative : t -> bool

val mark_npe_alternative : t -> t

val loc_to_access_expr : t -> Loc.t -> AccessExpr.t option

val is_exceptional : t -> bool

val set_exception : t -> t

val unwrap_exception : t -> t
