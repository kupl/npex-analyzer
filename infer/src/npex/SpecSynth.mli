open! IStd

val launch : get_summary:(Procname.t -> SpecCheckerSummary.t) -> unit

val checker : SpecCheckerSummary.t InterproceduralAnalysis.t -> SpecCheckerSummary.t option
