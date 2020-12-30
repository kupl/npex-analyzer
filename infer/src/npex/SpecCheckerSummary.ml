open! IStd
module Domain = SpecCheckerDomain

type t = Domain.t list

let pp = Pp.seq Domain.pp ~sep:"\n"

type get_summary = Domain.get_summary

let resolve_summary astate ~actual_values ~formals callee_summaries =
  List.filter_map callee_summaries ~f:(fun callee_summary ->
      Domain.resolve_summary astate ~actual_values ~formals callee_summary)
