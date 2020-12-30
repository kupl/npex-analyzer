open! IStd
module F = Format
module L = Logging

type formula = Atom of atom | Neg of atom

and atom = True | Predicate of func * term list

and func = Unary of unop | Binary of binop

and unop = IsConstant | IsImmutable

and binop = Equals | IsFunctionOf

and term = AccessExpr.t [@@deriving compare]

let rec pp_formula fmt = function
  | Atom atom ->
      F.fprintf fmt "%a" pp_atom atom
  | Neg atom ->
      F.fprintf fmt "!(%a)" pp_atom atom


and pp_atom fmt = function
  | True ->
      F.fprintf fmt "%s" "True"
  | Predicate (func, terms) ->
      F.fprintf fmt "%a(%a)" pp_func func pp_term_list terms


and pp_func fmt = function Unary unop -> pp_unop fmt unop | Binary binop -> pp_binop fmt binop

and pp_unop fmt = function
  | IsConstant ->
      F.fprintf fmt "%s" "IsConstant"
  | IsImmutable ->
      F.fprintf fmt "%s" "IsImmutable"


and pp_binop fmt = function
  | Equals ->
      F.fprintf fmt "%s" "Equals"
  | IsFunctionOf ->
      F.fprintf fmt "%s" "IsFunctionOf"


and pp_term = AccessExpr.pp

and pp_term_list fmt terms = Pp.comma_seq ~print_env:Pp.text pp_term fmt terms

let app_of func terms = Predicate (func, terms)

let get_func_and_terms = function
  | Atom (Predicate (fn, ts)) | Neg (Predicate (fn, ts)) ->
      (fn, ts)
  | formula ->
      L.(die InternalError "Formula %a has no predicate" pp_formula formula)
