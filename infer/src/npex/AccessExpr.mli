open! IStd
module F = Format

type t = base * access list [@@deriving compare]

and base = Formal of Pvar.t | Variable of Pvar.t | Primitive of Const.t

and access = FieldAccess of Fieldname.t | MethodCallAccess of method_call | ArrayAccess of t

and method_call = Procname.t * t list

val compare : t -> t -> int

val equal : t -> t -> bool

val equal_wo_formal : t -> t -> bool

val pp : F.formatter -> t -> unit

val of_pvar : Pvar.t -> t

val of_formal : Pvar.t -> t

val of_const : Const.t -> t

val get_deref_field : t -> string

val is_local : Procdesc.t -> t -> bool

val is_sub_expr : sub:t -> t -> bool

val is_var : t -> bool

val contains_method_access : t -> bool

val replace_sub : t -> src:t -> dst:t -> t

val replace_by_map : t -> f:(t -> t) -> t

val append_access : t -> access -> t

val dummy : t

val from_IR_exp : Procdesc.t -> Exp.t -> t

val from_IR_exp_opt : Procdesc.t -> Exp.t -> t option

val contain_method_call_access : t -> bool

val bind_pdesc : Procdesc.t -> unit

val null : t

val zero : t

val one : t

val has_duplicates : t -> bool

module Set : PrettyPrintable.PPSet with type elt = t

module Map : PrettyPrintable.PPMap with type key = t

val is_abstract : t -> bool

val is_concrete : t -> bool

val is_different_type : t -> t -> bool

val is_recursive : t -> bool
