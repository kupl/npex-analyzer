open! IStd
open! Vocab
module F = Format
module Domain = SpecCheckerDomain
module Features = SpecCheckerFeatures
module Val = Domain.Val
module Mem = Domain.Mem
module Loc = Domain.Loc
module PC = Domain.PC
module SymHeap = SymDom.SymHeap

module S = struct
  type t = {astate: Domain.t [@compare.ignore]; features: Features.t; astate_with_local: Domain.t [@compare.ignore]}
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let get_astate {astate} = astate

  let get_local_astate {astate_with_local} = astate_with_local

  let get_features {features} = features

  let compute_reachables_from (Domain.{mem} as astate) =
    let pc_relevant v = Domain.equal_values astate v @ Domain.inequal_values astate v in
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
    let is_reachable_loc = function
      | (Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _))
        when Val.Set.mem (Val.Vheap sh) unreachable_heaps ->
          false
      | _ ->
          true
    in
    let mem' = Mem.filter (fun l v -> is_reachable_loc l && not (is_unreachable_value v)) mem in
    let pc' =
      PC.filter_by_value ~f:(fun v -> List.exists (Val.get_subvalues v) ~f:(not <<< is_unreachable_value)) pc
    in
    Domain.{astate with mem= mem'; pc= pc'}


  let remove_local (Domain.{mem} as astate) =
    let local_locs =
      Mem.fold
        (fun l _ acc -> match l with Loc.TempVar _ | Loc.IllTempVar _ -> Loc.Set.add l acc | _ -> acc)
        mem Loc.Set.empty
    in
    Domain.{astate with mem= Loc.Set.fold Mem.remove local_locs mem}


  let from_state proc_desc astate =
    let astate_with_local = remove_local astate in
    let astate_wo_unreachables = remove_unreachables astate_with_local in
    {astate= astate_wo_unreachables; astate_with_local; features= Features.from_state proc_desc astate}


  let pp fmt {astate; features} =
    F.fprintf fmt "== StateWithFeature ==@, - State: %a@, - Features: %a" Domain.pp astate Features.pp features
end

include S
module Set = PrettyPrintable.MakePPSet (S)

let merge disjuncts = disjuncts

(* let representatives = Set.of_list disjuncts |> Set.elements in
   List.map representatives ~f:(fun ({astate; features; astate_with_local} as swf) ->
       let mergable_states = List.filter disjuncts ~f:(equal swf) in
       let astate_joined =
         List.fold mergable_states ~init:astate ~f:(fun acc_state to_merge ->
             Domain.weak_join acc_state to_merge.astate)
       in
       let astate_local_joined =
         List.fold mergable_states ~init:astate_with_local ~f:(fun acc_state to_merge ->
             Domain.weak_join acc_state to_merge.astate_with_local)
       in
       {astate= astate_joined; astate_with_local= astate_local_joined; features}) *)
