open! IStd
module Domain = SpecCheckerDomain

type t = Domain.t list

type get_summary = Domain.get_summary

val pp : Format.formatter -> t -> unit

val resolve_summary : Domain.t -> actual_values:Domain.Val.t list -> callee_pdesc:Procdesc.t -> t -> t
