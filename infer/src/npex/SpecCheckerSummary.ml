open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
module Features = SpecCheckerFeatures
module Loc = Domain.Loc
module Val = Domain.Val
module Mem = Domain.Mem
module PC = Domain.PC
module SymHeap = SymDom.SymHeap

module StateWithFeature = struct
  type t = {astate: Domain.t [@compare.ignore]; features: Features.t} [@@deriving compare]

  let equal = [%compare.equal: t]

  let get_astate {astate} = astate

  let get_features {features} = features

  let from_state proc_desc astate = {astate; features= Features.from_state proc_desc astate}

  let pp fmt {astate; features} =
    F.fprintf fmt "== StateWithFeature ==@, - State: %a@, - Features: %a" Domain.pp astate Features.pp features
end

module SFSet = PrettyPrintable.MakePPSet (StateWithFeature)

type t = StateWithFeature.t list

let get_disjuncts t = List.map t ~f:StateWithFeature.get_astate

let pp f t =
  let pp_elements f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i StateWithFeature.pp disjunct)
  in
  F.fprintf f "%d disjuncts:@.%a@." (List.length t) pp_elements t


type get_summary = Procname.t -> t option

let empty : t = []

let merge disjuncts =
  let representatives = SFSet.of_list disjuncts |> SFSet.elements in
  List.map representatives ~f:(fun (StateWithFeature.{astate; features} as swf) ->
      let mergable_states =
        List.filter disjuncts ~f:(StateWithFeature.equal swf)
        |> List.map ~f:(fun StateWithFeature.{astate} -> astate)
      in
      let astate_joined = List.fold mergable_states ~init:astate ~f:Domain.weak_join in
      StateWithFeature.{astate= astate_joined; features})


let compute_reachables_from (Domain.{mem} as astate) =
  let pc_relevant v = Domain.equal_values astate v @ Domain.equal_values astate v in
  let pointsto_val =
    Mem.fold
      (fun l v acc ->
        match l with
        | Loc.Var pv when Pvar.is_return pv ->
            Val.Set.add v acc
        | (Loc.Field (Loc.Var gv, _) | Loc.Index (Loc.Var gv, _)) when Pvar.is_global gv ->
            Val.Set.add v acc
        | (Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _)) when SymHeap.is_symbolic sh ->
            Val.Set.add (Val.Vheap sh) acc |> Val.Set.add v
        | _ when Val.is_symbolic v ->
            Val.Set.add v acc
        | _ ->
            acc)
      mem Val.Set.empty
  in
  Val.Set.elements pointsto_val
  |> List.concat_map ~f:pc_relevant
  |> List.concat_map ~f:Val.get_subvalues
  |> Val.Set.of_list


let remove_unreachables (Domain.{mem; pc} as astate) =
  let all_heaps =
    Domain.all_values astate |> Val.Set.elements |> List.concat_map ~f:Val.get_subvalues |> Val.Set.of_list
  in
  let reachable_heaps = compute_reachables_from astate in
  let unreachable_heaps = Val.Set.diff all_heaps reachable_heaps in
  let is_unreachable_value v =
    List.exists (Val.get_subvalues v) ~f:(fun subval -> Val.Set.mem subval unreachable_heaps)
  in
  let mem' =
    Mem.filter
      (fun l v ->
        match l with
        | (Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _))
          when Val.Set.mem (Val.Vheap sh) unreachable_heaps ->
            false
        | _ ->
            not (is_unreachable_value v))
      mem
  in
  let pc' =
    PC.filter_by_value ~f:(fun v -> List.exists (Val.get_subvalues v) ~f:(not <<< is_unreachable_value)) pc
  in
  Domain.{astate with mem= mem'; pc= pc'}


let remove_local (Domain.{mem; pc} as astate) ~formals ~ret_var =
  let unreachable_locs =
    Mem.fold
      (fun l _ acc -> if Loc.is_temp l || Loc.is_ill_temp l then Loc.Set.add l acc else acc)
      mem Loc.Set.empty
  in
  let mem' = Loc.Set.fold Mem.remove unreachable_locs mem in
  let pc' = pc in
  Domain.{astate with mem= mem'; pc= pc'}


let to_summary proc_desc disjuncts =
  (* L.progress "Converting to summary... of %a@." Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  let formals = Procdesc.get_pvar_formals proc_desc in
  let ret_var = Procdesc.get_ret_var proc_desc in
  let disjuncts_local_removed =
    List.map disjuncts ~f:(remove_local ~formals ~ret_var) |> List.map ~f:remove_unreachables
  in
  let summary = List.map ~f:(StateWithFeature.from_state proc_desc) disjuncts_local_removed |> merge in
  (* L.progress "State pruning : %d -> %d of %a@." (List.length disjuncts_local_removed) (List.length summary)
     Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  summary


module CtxCounter = SymDom.Counter (Procname)

let append_ctx callee astate =
  let cnt = CtxCounter.get callee in
  Domain.append_ctx astate cnt


let resolve_summary astate ~actual_values ~callee_pdesc callee_summaries =
  let formals = Procdesc.get_pvar_formals callee_pdesc in
  List.map ~f:StateWithFeature.get_astate callee_summaries
  |> List.map ~f:(append_ctx (Procdesc.get_proc_name callee_pdesc))
  |> List.filter_map ~f:(fun callee_summary ->
         Domain.resolve_summary astate ~actual_values ~formals callee_summary)
