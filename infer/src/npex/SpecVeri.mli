open! IStd

val launch :
     get_summary:(Procname.t -> SpecCheckerSummary.t)
  -> get_original_summary:(Procname.t -> SpecCheckerSummary.t)
  -> unit
