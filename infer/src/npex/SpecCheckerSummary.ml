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
module APSet = AbstractDomain.FiniteSet (AccessExpr)

module Features = struct
  type t =
    { null_vars: APSet.t
    ; return_value: Val.t option
    ; npe_alternative: bool
    ; exceptional: bool
    ; non_null_vars: APSet.t }
  [@@deriving compare]

  let pp fmt {null_vars; non_null_vars; return_value} =
    let return_value_str =
      match return_value with Some v -> F.asprintf "   - return_value : %a@." Val.pp v | None -> ""
    in
    F.fprintf fmt "   - null_vars: %a@.   - non_null_vars: %a@.%s" APSet.pp null_vars APSet.pp non_null_vars
      return_value_str


  let from_state proc_desc astate =
    let ret_var = Procdesc.get_ret_var proc_desc in
    let formals = ret_var :: (Procdesc.get_pvar_formals proc_desc |> List.map ~f:fst) in
    (* null_feilds *)
    let null_vars =
      Mem.fold
        (fun l v acc ->
          match l with
          | Loc.Var pv when List.mem formals pv ~equal:Pvar.equal ->
              if List.exists (Domain.equal_values astate v) ~f:Val.is_null then
                APSet.add (AccessExpr.of_pvar pv) acc
              else acc
          | _ ->
              acc)
        Domain.(astate.mem)
        APSet.empty
    in
    let non_null_vars =
      Mem.fold
        (fun l v acc ->
          match l with
          | Loc.Var pv when List.mem formals pv ~equal:Pvar.equal ->
              if List.exists (Domain.inequal_values astate v) ~f:Val.is_null then
                APSet.add (AccessExpr.of_pvar pv) acc
              else acc
          | _ ->
              acc)
        Domain.(astate.mem)
        APSet.empty
    in
    let return_value =
      match Domain.read_loc astate (Loc.of_pvar ret_var) with
      | Val.Vheap (Allocsite _) | Val.Vheap (Extern _) | Val.Vheap (Symbol _) ->
          None
      | Val.Vint (Extern _) ->
          None
      | _ as v ->
          Some v
    in
    let npe_alternative = Domain.is_npe_alternative astate in
    let exceptional = Domain.is_exceptional astate in
    {null_vars; return_value; npe_alternative; exceptional; non_null_vars}
end

module StateWithFeature = struct
  type t = {astate: Domain.t [@compare.ignore]; features: Features.t} [@@deriving compare]

  let get_astate {astate} = astate

  let get_features {features} = features

  let from_state proc_desc astate = {astate; features= Features.from_state proc_desc astate}

  let pp fmt {astate; features} =
    F.fprintf fmt "== StateWithFeature ==@. - State: %a@. - Features: %a" Domain.pp astate Features.pp features
end

module SFSet = PrettyPrintable.MakePPSet (StateWithFeature)

type t = StateWithFeature.t list

let get_disjuncts t = List.map t ~f:StateWithFeature.get_astate

(* let pp = Pp.seq Domain.pp ~sep:"\n" *)
let pp f t =
  let pp_elements f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i StateWithFeature.pp disjunct)
  in
  F.fprintf f "%d disjuncts:@.%a@." (List.length t) pp_elements t


type get_summary = Procname.t -> t option

let empty : t = []

let reachable_locs mem formals =
  let module Cache = PrettyPrintable.MakePPMonoMap (Loc) (Bool) in
  let module LocMap = WeakMap.Make (Loc) (Loc.Set) in
  let field_map =
    Mem.fold
      (fun l _ acc ->
        match l with
        | Loc.Field (l', _) ->
            LocMap.weak_update l' (Loc.Set.singleton l) acc
        | Loc.Index (l', _) ->
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
  (* let reachable_locs = reachable_locs mem (ret_var :: List.map formals ~f:fst) in
     let reachable_values = reachable_values mem reachable_locs in
     let unreachable_locs =
       Mem.fold (fun l _ acc -> if Loc.Set.mem l reachable_locs then acc else Loc.Set.add l acc) mem Loc.Set.empty
     in *)
  (* L.d_printf " - reachable_locs : %a@. - unreachable_locs : %a@." Loc.Set.pp reachable_locs Loc.Set.pp
     unreachable_locs ; *)
  let unreachable_locs =
    Mem.fold
      (fun l _ acc -> if Loc.is_temp l || Loc.is_ill_temp l then Loc.Set.add l acc else acc)
      mem Loc.Set.empty
  in
  let mem' = Loc.Set.fold Mem.remove unreachable_locs mem in
  (* let pc' = PC.filter_by_pred pc ~f:(fun v -> Val.is_constant v || ValSet.mem v reachable_values) in *)
  let pc' = pc in
  Domain.{astate with mem= mem'; pc= pc'}


let to_summary proc_desc disjuncts =
  (* L.progress "Converting to summary... of %a@." Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  let formals = Procdesc.get_pvar_formals proc_desc in
  let ret_var = Procdesc.get_ret_var proc_desc in
  let disjuncts_local_removed = List.map disjuncts ~f:(remove_local ~formals ~ret_var) in
  (* let disjuncts_local_removed = (* TODO: is it necessary? *) disjuncts in *)
  let summary =
    List.map ~f:(StateWithFeature.from_state proc_desc) disjuncts_local_removed |> SFSet.of_list |> SFSet.elements
  in
  (* L.progress "State pruning : %d -> %d of %a@." (List.length disjuncts_local_removed) (List.length summary)
     Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  summary


module CtxCounter = SymDom.Counter (InstrNode)

let append_ctx instr_node astate =
  let cnt = CtxCounter.get instr_node in
  Domain.append_ctx astate cnt


let resolve_summary astate instr_node ~actual_values ~callee_pdesc callee_summaries =
  let formals = Procdesc.get_pvar_formals callee_pdesc in
  List.map ~f:StateWithFeature.get_astate callee_summaries
  |> List.map ~f:(append_ctx instr_node)
  |> List.filter_map ~f:(fun callee_summary ->
         Domain.resolve_summary astate ~actual_values ~formals callee_summary)
