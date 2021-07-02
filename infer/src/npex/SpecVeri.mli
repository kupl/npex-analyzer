open! IStd

val pp_states : Format.formatter -> SpecCheckerDomain.t list -> unit

val pp_max : Format.formatter -> SpecCheckerDomain.t list -> unit

val launch :
     get_summary:(Procname.t -> SpecCheckerSummary.t)
  -> get_original_summary:(Procname.t -> SpecCheckerSummary.t)
  -> unit
