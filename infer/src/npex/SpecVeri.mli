open! IStd

val pp_states : Format.formatter -> SpecCheckerDomain.t list -> unit

val pp_normal_and_infered :
  Format.formatter -> (SpecCheckerDomain.t list * SpecCheckerDomain.t list) -> unit

val get_feasible_disjuncts_opt :
  SpecCheckerDomain.t list -> (SpecCheckerDomain.t list * SpecCheckerDomain.t list) option

val launch :
     get_summary:(Procname.t -> SpecCheckerSummary.t)
  -> get_original_summary:(Procname.t -> SpecCheckerSummary.t)
  -> unit
