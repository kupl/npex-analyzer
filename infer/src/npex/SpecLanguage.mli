open! IStd

type formula = Atom of atom | Neg of atom

and atom = True | Predicate of func * term list

and func = Unary of unop | Binary of binop

and unop = IsConstant | IsImmutable

and binop = Equals | IsFunctionOf

and term = AccessExpr.t [@@deriving compare]

val pp_formula : Format.formatter -> formula -> unit

val app_of : func -> term list -> atom

val get_func_and_terms : formula -> func * term list
