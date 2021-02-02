open! IStd
module F = Format

type t = AccessExpr of Pvar.t * access list | Primitive of Const.t

and access = FieldAccess of Fieldname.t | MethodCallAccess of method_call | ArrayAccess of t

and method_call = Procname.t * t list [@@deriving compare]

val compare : t -> t -> int

val equal : t -> t -> bool

val equal_base : t -> Pvar.t -> bool

val equal_access : access -> access -> bool

val pp : F.formatter -> t -> unit

val pp_access : F.formatter -> access -> unit

val to_string : t -> string

val of_pvar : Pvar.t -> t

val of_const : Const.t -> t

val get_base : t -> Pvar.t

val get_deref_field : t -> string

val is_local : Procdesc.t -> t -> bool

val is_sub_expr : sub:t -> t -> bool

val replace_sub : src:t -> dst:t -> t -> t

val replace_base : dst:t -> t -> t

val append_access : t -> access -> t

val dummy : t

val from_IR_exp : Procdesc.t -> Exp.t -> t

val from_IR_exp_opt : Procdesc.t -> Exp.t -> t option

val contain_method_call_access : t -> bool

val bind_pdesc : Procdesc.t -> unit

val null : t

val zero : t

val one : t

module Set : PrettyPrintable.PPSet with type elt = t

module Map : PrettyPrintable.PPMap with type key = t

val is_abstract : t -> bool

val is_concrete : t -> bool
