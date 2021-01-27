open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
module Loc = Domain.Loc
module Val = Domain.Val
module ValSet = AbstractDomain.FiniteSet (Val)
module Mem = Domain.Mem
module PC = Domain.PC

module StateWithFeature = struct
  type t = {astate: Domain.t [@compare.ignore]; features: StateFormula.t} [@@deriving compare]

  let get_astate {astate} = astate

  let from_state proc_desc astate = {astate; features= StateFormula.from_state proc_desc astate}

  let pp fmt {astate; features} =
    F.fprintf fmt "== StateWithFeature ==@. - State: %a@. - Features: %a" Domain.pp astate StateFormula.pp features
end

module SFSet = PrettyPrintable.MakePPSet (StateWithFeature)

type t = Domain.t list

(* let pp = Pp.seq Domain.pp ~sep:"\n" *)
let pp f disjuncts =
  let pp_disjuncts f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i Domain.pp disjunct)
  in
  F.fprintf f "%d disjuncts:@.%a@." (List.length disjuncts) pp_disjuncts disjuncts


type get_summary = Domain.get_summary

let reachable_locs mem formals =
  let module Cache = PrettyPrintable.MakePPMonoMap (Loc) (Bool) in
  let module LocMap = WeakMap.Make (Loc) (Loc.Set) in
  let field_map =
    Mem.fold
      (fun l _ acc ->
        match l with
        | Loc.Field (l', _) ->
            LocMap.weak_update l' (Loc.Set.singleton l) acc
        | Loc.Index l' ->
            LocMap.weak_update l' (Loc.Set.singleton l) acc
        | _ ->
            acc)
      mem LocMap.empty
  in
  let _cache = ref Cache.empty in
  let rec _reachable_locs worklist donelist reachables =
    if Loc.Set.is_empty worklist then reachables
    else
      let work = Loc.Set.choose worklist in
      let donelist' = Loc.Set.add work donelist in
      let next_locs =
        let field_locs = LocMap.find work field_map in
        match Mem.find work mem with
        | Val.Vheap symheap ->
            Loc.Set.add (Loc.SymHeap symheap) field_locs
        | _ ->
            field_locs
      in
      let worklist' = Loc.Set.diff (Loc.Set.union next_locs worklist) donelist' in
      let reachables' = Loc.Set.union reachables next_locs in
      _reachable_locs worklist' donelist' reachables'
  in
  let init =
    Mem.fold
      (fun l _ acc ->
        match l with
        | (Loc.Var pv | Loc.Field (Loc.Var pv, _)) when Pvar.is_global pv ->
            (* Global variable may have no pvar as location *)
            Loc.Set.add l acc
        | Loc.Var pv when List.mem formals pv ~equal:Pvar.equal ->
            Loc.Set.add l acc
        | _ ->
            acc)
      mem Loc.Set.empty
  in
  let results = _reachable_locs init Loc.Set.empty init in
  (* L.progress "@.===== compute reachable locs =====@." ;
     L.progress " - Mem: %a@." Mem.pp mem ;
     L.progress " - Init: %a@." Loc.Set.pp init ;
     L.progress " - Reachables: %a@." Loc.Set.pp results ; *)
  results


let reachable_values mem reachable_locs =
  Mem.fold (fun l v acc -> if Loc.Set.mem l reachable_locs then ValSet.add v acc else acc) mem ValSet.empty


let remove_local (Domain.{mem; pc} as astate) ~formals ~ret_var =
  let reachable_locs = reachable_locs mem (ret_var :: List.map formals ~f:fst) in
  let reachable_values = reachable_values mem reachable_locs in
  let unreachable_locs =
    Mem.fold (fun l _ acc -> if Loc.Set.mem l reachable_locs then acc else Loc.Set.add l acc) mem Loc.Set.empty
  in
  (* L.d_printf " - reachable_locs : %a@. - unreachable_locs : %a@." Loc.Set.pp reachable_locs Loc.Set.pp
     unreachable_locs ; *)
  let mem' = Loc.Set.fold Mem.remove unreachable_locs mem in
  let pc' = PC.filter_by_pred pc ~f:(fun v -> Val.is_constant v || ValSet.mem v reachable_values) in
  Domain.{astate with mem= mem'; pc= pc'}


let resolve_summary astate ~actual_values ~callee_pdesc callee_summaries =
  let formals = Procdesc.get_pvar_formals callee_pdesc in
  let ret_var = Procdesc.get_ret_var callee_pdesc in
  let summaries_local_removed = List.map callee_summaries ~f:(remove_local ~formals ~ret_var) in
  L.d_printfln "====== summaries local removed ======@. - %a@.==========================" pp
    summaries_local_removed ;
  let summaries_pruned =
    summaries_local_removed
    |> List.map ~f:(StateWithFeature.from_state callee_pdesc)
    |> SFSet.of_list
    |> SFSet.elements
    |> List.map ~f:StateWithFeature.get_astate
  in
  (* L.progress "State pruning from %d to %d@." (List.length summaries_local_removed) (List.length summaries_pruned) ; *)
  List.filter_map summaries_pruned ~f:(fun callee_summary ->
      Domain.resolve_summary astate ~actual_values ~formals callee_summary)
