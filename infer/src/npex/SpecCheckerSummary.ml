open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain

type t = StateWithFeature.t list

let get_disjuncts t = List.map t ~f:StateWithFeature.get_astate

let get_local_disjuncts t = List.map t ~f:StateWithFeature.get_local_astate

let pp f t =
  let pp_elements f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i StateWithFeature.pp disjunct)
  in
  F.fprintf f "%d disjuncts:@.%a@." (List.length t) pp_elements t


type get_summary = Procname.t -> t option

let empty : t = []

let to_summary proc_desc disjuncts =
  L.(debug Analysis Quiet)
    "@.---- Analysis time result of %a ----@." Procname.pp (Procdesc.get_proc_name proc_desc) ;
  debug_time_finalize () ;
  let disjuncts = join_list disjuncts ~joinable:Domain.joinable ~join:Domain.weak_join ~pp:Domain.pp in
  let summary = List.map ~f:(StateWithFeature.from_state proc_desc) disjuncts |> StateWithFeature.merge in
  (* L.progress "State pruning : %d -> %d of %a@." (List.length disjuncts_local_removed) (List.length summary)
     Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  summary


let get_only_normals : t -> t = List.filter ~f:(not <<< Domain.is_inferred <<< StateWithFeature.get_astate)

module CtxCounter = SymDom.Counter (Procname)

let append_ctx callee astate =
  let cnt = CtxCounter.get callee in
  Domain.append_ctx astate cnt


let resolve_summary astate ~actual_values ~callee_pdesc callee_summaries =
  let formals = Procdesc.get_pvar_formals callee_pdesc in
  let callee_unreachable_removed =
    List.map ~f:StateWithFeature.get_astate callee_summaries
    (* FIXME: bottom state implys identity function, it would be better not to remove it *)
    |> Domain.merge
    (* |> join_list ~joinable:Domain.joinable ~join:Domain.weak_join ~pp:Domain.pp *)
    |> List.map ~f:(append_ctx (Procdesc.get_proc_name callee_pdesc))
  in
  L.d_printfln "Join callee summaries before resolution: got %d from %d"
    (List.length callee_unreachable_removed)
    (List.length callee_summaries) ;
  List.filter_map callee_unreachable_removed ~f:(fun callee_summary ->
      Domain.resolve_summary astate ~actual_values ~formals callee_summary)
