open! IStd
module Domain = SpecCheckerDomain

module APSet : AbstractDomain.FiniteSetS with type elt = AccessExpr.t

type t

type get_summary = Procname.t -> t option

val pp : Format.formatter -> t -> unit

val empty : t

val resolve_summary : Domain.t -> actual_values:Domain.Val.t list -> callee_pdesc:Procdesc.t -> t -> Domain.t list

val to_summary : Procdesc.t -> Domain.t list -> t

val get_disjuncts : t -> Domain.t list
