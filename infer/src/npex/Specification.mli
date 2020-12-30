open! IStd

module Formula : sig
  type formula = Atom of atom | Neg of formula

  and atom = True | Predicate of func * term list

  and func = Unary of unop | Binary of binop

  and unop = IsConstant | IsImmutable

  and binop = Equals | IsFunctionOf

  and term = AccessExpr.t [@@deriving compare]

  val pp_formula : Format.formatter -> formula -> unit

  val true_formula : formula

  val app_of : func -> term list -> atom

  val get_func_and_terms : formula -> func * term list
end

type t = {mthd: Procname.t; pre: Formula.formula; post: Formula.formula; id: string [@comapre.ignore]}
[@@deriving compare]

val pp : Format.formatter -> t -> unit

val create : prefix:string -> mthd:Procname.t -> pre:Formula.formula -> post:Formula.formula -> t

val from_marshal_all : unit -> t list

val to_marshal_all : t list -> unit

module Conjunctions : PrettyPrintable.PPSet with type elt = Formula.formula

module Set : PrettyPrintable.PPSet with type elt = t
