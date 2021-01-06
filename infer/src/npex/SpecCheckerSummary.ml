open! IStd
module Domain = SpecCheckerDomain
module F = Format

type t = Domain.t list

(* let pp = Pp.seq Domain.pp ~sep:"\n" *)
let pp f disjuncts =
  let pp_disjuncts f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i Domain.pp disjunct)
  in
  F.fprintf f "%d disjuncts:@.%a@." (List.length disjuncts) pp_disjuncts disjuncts


type get_summary = Domain.get_summary

let resolve_summary astate ~actual_values ~formals callee_summaries =
  List.filter_map callee_summaries ~f:(fun callee_summary ->
      Domain.resolve_summary astate ~actual_values ~formals callee_summary)
