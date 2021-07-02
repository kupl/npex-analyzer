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

  let remove_local (Domain.{mem} as astate) =
    let local_locs =
      Mem.fold
        (fun l _ acc -> match l with Loc.TempVar _ | Loc.IllTempVar _ -> Loc.Set.add l acc | _ -> acc)
        mem Loc.Set.empty
    in
    Domain.
      {astate with reg= Reg.empty; mem= Loc.Set.fold Mem.remove local_locs mem; temps_to_remove= Domain.Vars.empty}


  let from_state proc_desc astate =
    let astate_with_local = remove_local astate in
    let astate_wo_unreachables = Domain.remove_unreachables astate_with_local in
    {astate= astate_wo_unreachables; astate_with_local; features= Features.from_state proc_desc astate}


  let pp fmt {astate_with_local; features} =
    F.fprintf fmt "== StateWithFeature ==@, - State: %a@, - Features: %a" Domain.pp astate_with_local Features.pp
      features
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
