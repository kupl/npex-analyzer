open! IStd
open! Vocab
module F = Format
module L = Logging

type result = Valid | Satisfiable | UnSAT | Unknown

let to_string_result = function
  | Valid ->
      "Valid"
  | Satisfiable ->
      "Satisfiable"
  | UnSAT ->
      "UnSAT"
  | Unknown ->
      "Unknown"


module type S = sig
  include PrettyPrintable.PrintableEquatableOrderedType

  val zero : t

  val is_abstract : t -> bool (* v1 == v1 is even not valid. they are abstracted values *)

  val is_concrete : t -> bool (* v1 == v2 is invalid statement for any concrete value v1, v2 *)

  val is_different_type : t -> t -> bool (* v1 == v2 is invalid statement for any different type of values *)

  val is_recursive : t -> bool (* value which contains other values e.g., foo(v) *)

  val replace_sub : t -> src:t -> dst:t -> t

  val replace_by_map : t -> f:(t -> t) -> t
end

module Make (Val : S) = struct
  type t = PEquals of Val.t * Val.t | Not of t | Equals of Val.t * Val.t [@@deriving compare]

  let rec sorted =
    let sort_vars (v1, v2) =
      let order = Val.compare v1 v2 in
      if Int.( <= ) order 0 then (v1, v2) else (v2, v1)
    in
    function
    | PEquals (v1, v2) ->
        let v1, v2 = sort_vars (v1, v2) in
        PEquals (v1, v2)
    | Not x ->
        Not (sorted x)
    | Equals (v1, v2) ->
        let v1, v2 = sort_vars (v1, v2) in
        Equals (v1, v2)


  let compare x y = compare (sorted x) (sorted y)

  let equal = [%compare.equal: t]

  let rec pp fmt = function
    | PEquals (v1, v2) ->
        F.fprintf fmt "%a == %a" Val.pp v1 Val.pp v2
    | Not (PEquals (v1, v2)) ->
        F.fprintf fmt "%a != %a" Val.pp v1 Val.pp v2
    | Not pc ->
        F.fprintf fmt "Not (%a)" pp pc
    | Equals (v1, v2) ->
        F.fprintf fmt "Equals (%a, %a)" Val.pp v1 Val.pp v2


  let rec replace_value x ~src ~dst =
    let result =
      match x with
      | PEquals (v1, v2) ->
          PEquals (Val.replace_sub v1 ~src ~dst, Val.replace_sub v2 ~src ~dst)
      | Not x ->
          Not (replace_value x ~src ~dst)
      | Equals (v1, v2) ->
          Equals (Val.replace_sub v1 ~src ~dst, Val.replace_sub v2 ~src ~dst)
    in
    sorted result


  let rec replace_by_map ~f x =
    let result =
      match x with
      | PEquals (v1, v2) ->
          PEquals (Val.replace_by_map ~f v1, Val.replace_by_map ~f v2)
      | Not x ->
          Not (replace_by_map ~f x)
      | Equals (v1, v2) ->
          Equals (Val.replace_by_map ~f v1, Val.replace_by_map ~f v2)
    in
    sorted result


  let true_cond = PEquals (Val.zero, Val.zero) (* top *)

  let false_cond = Not true_cond

  let is_true = equal true_cond

  let is_false = equal false_cond

  let rec contains_absval = function
    | (PEquals (v1, v2) | Equals (v1, v2)) when Val.is_abstract v1 || Val.is_abstract v2 ->
        true
    | Not x ->
        contains_absval x
    | _ ->
        false


  let rec check = function
    | _ as x when contains_absval x ->
        Satisfiable
    | PEquals (v1, v2) when Val.equal v1 v2 ->
        Valid
    | PEquals (v1, v2) when Val.is_concrete v1 && Val.is_concrete v2 ->
        UnSAT
    | PEquals (v1, v2) when Val.is_different_type v1 v2 ->
        UnSAT
    | Not cond -> (
      match check cond with Valid -> UnSAT | Satisfiable -> Satisfiable | UnSAT -> Valid | Unknown -> Unknown )
    | _ ->
        (* TODO: add *)
        Unknown


  let is_valid x = match check x with Valid -> true | _ -> false

  let is_invalid x = match check x with UnSAT -> true | _ -> false

  let rec contains_with_pred ~f = function
    | PEquals (v1, v2) | Equals (v1, v2) ->
        f v1 && f v2
    | Not x ->
        contains_with_pred ~f x


  let make_negation = function Not x -> x | _ as x -> Not x

  let make_physical_equals binop v1 v2 =
    (* if v1 or v2 contain symbol, then make condition
       else if no symbol in v1 or v2, it evaluates to true or false *)
    (* let[@warning "-8"] [v1; v2] = List.sort [v1; v2] ~compare:Val.compare in *)
    let order = Val.compare v1 v2 in
    let v1, v2 = if Int.( <= ) order 0 then (v1, v2) else (v2, v1) in
    (* L.d_printfln "Make physical equals from (%s, %a, %a)" (Binop.str Pp.text binop) Val.pp v1 Val.pp v2 ; *)
    match (binop, v1, v2) with
    | Binop.Eq, _, _ when Int.equal order 0 ->
        true_cond
    | Binop.Ne, _, _ when Int.equal order 0 ->
        false_cond
    | Binop.Eq, v1, v2 ->
        PEquals (v1, v2)
    | Binop.Ne, v1, v2 ->
        Not (PEquals (v1, v2))
    | _ ->
        (* TODO: implement less than, greater than, etc.*)
        raise (TODO (F.asprintf "non equal condition(%s) are not supported" (Binop.str Pp.text binop)))


  let rec vals_of_path_cond = function
    | PEquals (v1, v2) | Equals (v1, v2) ->
        [v1; v2]
    | Not pc ->
        vals_of_path_cond pc
end

module MakePC (Val : S) = struct
  module ValSet = PrettyPrintable.MakePPSet (Val)
  module PathCond = Make (Val)
  module PCSet = PrettyPrintable.MakePPSet (PathCond)
  module ConstMap = PrettyPrintable.MakePPMonoMap (Val) (Val)

  module InEqualMap = struct
    include PrettyPrintable.MakePPMonoMap (Val) (ValSet)

    let add_elt v c t =
      match find_opt v t with Some consts -> add v (ValSet.add c consts) t | None -> add v (ValSet.singleton c) t
  end

  type t = {pc_set: PCSet.t; const_map: ConstMap.t; inequal_map: InEqualMap.t; branches: PCSet.t}

  let to_pc_set {pc_set; const_map; inequal_map} =
    (* TODO: it may have scalability issues *)
    ConstMap.fold (fun v const -> PCSet.add (PathCond.make_physical_equals Binop.Eq v const)) const_map pc_set
    |> InEqualMap.fold
         (fun v consts -> ValSet.fold (fun c -> PathCond.make_physical_equals Binop.Ne v c |> PCSet.add) consts)
         inequal_map


  let all_values {pc_set; const_map; inequal_map} =
    List.concat_map (PCSet.elements pc_set) ~f:PathCond.vals_of_path_cond
    |> ValSet.of_list
    |> ConstMap.fold (fun v c acc -> ValSet.add v acc |> ValSet.add c) const_map
    |> InEqualMap.fold (fun v consts -> ValSet.add v consts |> ValSet.union) inequal_map
    |> ValSet.elements


  let get_branches {branches} = branches

  let empty = {pc_set= PCSet.empty; const_map= ConstMap.empty; branches= PCSet.empty; inequal_map= InEqualMap.empty}

  let is_bottom {pc_set; const_map} = PCSet.is_empty pc_set && ConstMap.is_empty const_map

  let compare pc1 pc2 = PCSet.compare (to_pc_set pc1) (to_pc_set pc2)

  let to_string {pc_set; const_map} =
    let const_map_str =
      ConstMap.fold
        (fun v c acc -> String.concat [acc; F.asprintf "(ConstMap) %a == %a@." Val.pp v Val.pp c])
        const_map ""
    in
    PCSet.fold
      (fun cond acc -> String.concat [acc; F.asprintf "(NonConst) %a@." PathCond.pp cond])
      pc_set const_map_str


  let pp_set fmt x = PCSet.pp fmt (to_pc_set x)

  let pp fmt {const_map; pc_set; branches; inequal_map} = 
  F.fprintf fmt
    "@[<v 2> - ConstMap:@, %a@]@. 
     @[<v 2> - InequalMap:@, %a@]@. 
     @[<v 2> - PathConds:@, %a@]@. 
     @[<v 2> - BranchConds:@, %a@]@."
    ConstMap.pp const_map InEqualMap.pp inequal_map PCSet.pp pc_set PCSet.pp branches
    [@@ocamlformat "disable"]

  let debug_if_invalid_pc transitives original_cond =
    if List.exists transitives ~f:PathCond.is_invalid then
      L.d_printfln "Invalid condition generated by %a" PathCond.pp original_cond


  let update_const_map pc transitives =
    (* TODO: it may have scalability issues *)
    let const_map, inequal_map =
      PCSet.fold
        (fun cond (const_acc, inequal_acc) ->
          match cond with
          | PathCond.PEquals (v1, v2) when Val.is_concrete v1 && not (Val.is_concrete v2) ->
              (ConstMap.add v2 v1 const_acc, inequal_acc)
          | PathCond.PEquals (v1, v2) when Val.is_concrete v2 && not (Val.is_concrete v1) ->
              (ConstMap.add v1 v2 const_acc, inequal_acc)
          | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.is_concrete v1 && not (Val.is_concrete v2) ->
              (const_acc, InEqualMap.add_elt v2 v1 inequal_acc)
          | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.is_concrete v2 && not (Val.is_concrete v1) ->
              (const_acc, InEqualMap.add_elt v1 v2 inequal_acc)
          | _ ->
              (const_acc, inequal_acc))
        transitives (pc.const_map, pc.inequal_map)
    in
    let pc_set =
      PCSet.map
        (* v -> c, v2 = v => v2 = c *)
        (PathCond.replace_by_map ~f:(fun v ->
             match ConstMap.find_opt v const_map with Some const -> const | None -> v))
        transitives
      (* remove trivial condition (e.g., c = c) *)
      |> PCSet.filter (not <<< PathCond.is_valid)
      (* remove constant inequal condition (e.g., v != c) *)
      |> PCSet.filter (function
           | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.is_concrete v1 && not (Val.is_concrete v2) ->
               false
           | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.is_concrete v2 && not (Val.is_concrete v1) ->
               false
           | _ ->
               true)
    in
    {pc with pc_set; const_map; inequal_map}


  let compute_transitives pathcond pc =
    let pc_set = to_pc_set pc in
    let replace_pathcond_by_equals =
      PCSet.fold
        (fun cond acc ->
          match cond with
          | PathCond.PEquals (v1', v2') ->
              let cond_gen1 = PathCond.replace_value pathcond ~src:v1' ~dst:v2' in
              let cond_gen2 = PathCond.replace_value pathcond ~src:v2' ~dst:v1' in
              if Config.debug_mode then debug_if_invalid_pc [cond_gen1; cond_gen2] cond ;
              PCSet.add cond_gen1 acc |> PCSet.add cond_gen2
          | _ ->
              acc)
        pc_set PCSet.empty
    in
    let replace_pc_set_by_pathcond =
      match pathcond with
      | PathCond.PEquals (v1, v2) ->
          let pc_set_to_add1 = PCSet.map (PathCond.replace_value ~src:v1 ~dst:v2) pc_set in
          let pc_set_to_add2 = PCSet.map (PathCond.replace_value ~src:v2 ~dst:v1) pc_set in
          let pc_set_to_add = PCSet.union pc_set_to_add1 pc_set_to_add2 in
          if Config.debug_mode then debug_if_invalid_pc (PCSet.elements pc_set_to_add) pathcond ;
          PCSet.union pc_set_to_add pc_set
      | _ ->
          pc_set
    in
    let to_add = PCSet.union replace_pathcond_by_equals replace_pc_set_by_pathcond in
    PCSet.add pathcond pc_set |> PCSet.union to_add


  let compute_transitives pathcond ({pc_set; const_map; inequal_map} as pc) =
    match pathcond with
    | PathCond.PEquals (v1, v2) when Val.is_concrete v1 || Val.is_concrete v2 -> (
        (* v = c *)
        let v, c = if Val.is_concrete v1 then (v2, v1) else (v1, v2) in
        match ConstMap.find_opt v const_map with
        | Some c' when Val.equal c c' ->
            (* already v = c, useless *)
            pc
        | Some c' ->
            (* already v = c', invalid *)
            let cond_gen = PathCond.make_physical_equals Binop.Eq c c' in
            if Config.debug_mode then debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Eq v c') ;
            {pc with pc_set= PCSet.add cond_gen pc_set}
        | None -> (
            let const_map' = ConstMap.add v c const_map in
            match InEqualMap.find_opt v inequal_map with
            | Some consts when ValSet.exists (Val.equal c) consts ->
                (* already v != c, invalid *)
                let cond_gen = PathCond.make_physical_equals Binop.Ne c c in
                if Config.debug_mode then
                  debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Ne v c) ;
                {pc with pc_set= PCSet.add cond_gen pc_set; const_map= const_map'}
            | _ ->
                let inequal_map' = InEqualMap.remove v inequal_map in
                let transitives =
                  compute_transitives pathcond pc
                  (* TODO: may implement more efficient, but unreadable algorithm as follows *)
                  (* PCSet.map (PathCond.replace_value ~src:v ~dst:c) pc_set in
                     let transitives' =
                       (* v = foo (v1, v2) -> c, c(v2) -> c' => foo (v1, c') -> c *)
                       if Val.is_recursive v then
                         let v' =
                           Val.replace_by_map v ~f:(fun v ->
                               match ConstMap.find_opt v const_map with Some c' -> c' | None -> v)
                         in
                         PCSet.add (PathCond.make_physical_equals Binop.Eq v' c) transitives
                       else transitives
                     in
                     let transitives'' =
                       (* v' = foo (v1, v2) -> c', c(v2) -> c' => foo (v1, c') -> c *)
                       ConstMap.fold
                         (fun v' c' acc ->
                           if Val.is_recursive v then
                             let v'' = Val.replace_sub ~src:v ~dst:c v' in
                             PCSet.add (PathCond.make_physical_equals Binop.Eq v'' c') acc
                           else acc)
                         const_map transitives' *)
                in
                update_const_map {pc with const_map= const_map'; inequal_map= inequal_map'} transitives ) )
    | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.is_concrete v1 || Val.is_concrete v2 -> (
        (* v != c *)
        let v, c = if Val.is_concrete v1 then (v2, v1) else (v1, v2) in
        match InEqualMap.find_opt v inequal_map with
        | Some consts when ValSet.mem c consts ->
            (* already v != c, useless *)
            pc
        | _ -> (
            let inequal_map' = InEqualMap.add_elt v c inequal_map in
            match ConstMap.find_opt v const_map with
            (* already v = c, invalid *)
            | Some c' when Val.equal c c' ->
                let cond_gen = PathCond.make_physical_equals Binop.Ne c c in
                if Config.debug_mode then
                  debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Eq v c) ;
                {pc with pc_set= PCSet.add cond_gen pc_set; inequal_map= inequal_map'}
            | Some _ ->
                (* already v = c', useless *)
                pc
            | None ->
                let transitives = compute_transitives pathcond pc in
                update_const_map {pc with inequal_map= inequal_map'} transitives ) )
    | _ ->
        let transitives = compute_transitives pathcond pc in
        update_const_map pc transitives


  let is_valid pathcond pc = PathCond.is_valid pathcond || PCSet.mem pathcond (to_pc_set pc)

  let is_invalid {pc_set} = PCSet.exists PathCond.is_invalid pc_set

  let add ?(is_branch = false) pathcond pc =
    if PathCond.contains_absval pathcond || PathCond.is_valid pathcond then pc
    else if PathCond.is_invalid pathcond then {pc with pc_set= PCSet.add pathcond pc.pc_set}
    else
      let pc' = compute_transitives pathcond pc in
      if is_branch then {pc' with branches= PCSet.add pathcond pc'.branches} else pc'


  let replace_by_map ~f {pc_set; const_map; branches; inequal_map} =
    let pc_set = PCSet.map (PathCond.replace_by_map ~f) pc_set in
    let const_map = ConstMap.fold (fun v const -> ConstMap.add (f v) (f const)) const_map ConstMap.empty in
    let branches = PCSet.map (PathCond.replace_by_map ~f) branches in
    let inequal_map =
      InEqualMap.fold (fun v consts -> InEqualMap.add (f v) (ValSet.map f consts)) inequal_map InEqualMap.empty
    in
    {pc_set; const_map; branches; inequal_map}


  let replace_value {pc_set; const_map; branches; inequal_map} ~(src : Val.t) ~(dst : Val.t) =
    let pc_set = PCSet.map (PathCond.replace_value ~src ~dst) pc_set in
    let branches = PCSet.map (PathCond.replace_value ~src ~dst) branches in
    let f = Val.replace_sub ~src ~dst in
    let const_map = ConstMap.fold (fun v const -> ConstMap.add (f v) (f const)) const_map ConstMap.empty in
    let inequal_map =
      InEqualMap.fold (fun v consts -> InEqualMap.add (f v) (ValSet.map f consts)) inequal_map InEqualMap.empty
    in
    {pc_set; const_map; branches; inequal_map}


  let join pc1 pc2 = PCSet.fold add (to_pc_set pc2) pc1

  let diff pc1 pc2 = PCSet.fold add (PCSet.diff (to_pc_set pc1) (to_pc_set pc2)) empty

  let merge pc1 pc2 = PCSet.fold add (PCSet.inter (to_pc_set pc1) (to_pc_set pc2)) empty

  let check_sat ?(print_unsat = false) pc1 pc2 =
    let pc_unioned = join pc1 pc2 in
    let result = not (is_invalid pc_unioned) in
    if print_unsat then
      L.progress "===== check sat =====@. - lhs: %a@. - rhs: %a@. - unioned: %a@. - result: %b@." pp pc1 pp pc2 pp
        pc_unioned result ;
    result


  let check_sat_branch pc1 pc2 =
    let pc_unioned = PCSet.fold add pc1.branches empty |> PCSet.fold add pc2.branches in
    not (is_invalid pc_unioned)


  let check_valid ?(print_invalid = false) pc1 pc2 =
    let pc_set1 = PCSet.filter (not <<< PathCond.is_valid) (to_pc_set pc1) in
    let pc_set2 = PCSet.filter (not <<< PathCond.is_valid) (to_pc_set pc2) in
    let result = (* TODO: check *) PCSet.equal pc_set1 pc_set2 in
    if print_invalid then
      L.progress "===== check validity ====@. - lhs: %a@. - rhs: %a@. - result: %b@." pp pc1 pp pc2 result ;
    result


  let equal_values {const_map} v =
    (* only returns constant values *)
    match ConstMap.find_opt v const_map with Some const -> [v; const] | None -> [v]


  let equal_constant_opt {const_map} v = ConstMap.find_opt v const_map

  let inequal_values {inequal_map} v =
    match InEqualMap.find_opt v inequal_map with Some consts -> ValSet.elements consts | None -> []


  let filter ~f {pc_set; const_map; branches; inequal_map} =
    let pc_set = PCSet.filter f pc_set in
    let const_map = ConstMap.filter (fun v c -> f (PathCond.PEquals (v, c))) const_map in
    let branches = PCSet.filter f branches in
    let inequal_map =
      InEqualMap.mapi (fun v consts -> ValSet.filter (fun c -> f (PathCond.PEquals (v, c))) consts) inequal_map
    in
    {pc_set; const_map; branches; inequal_map}


  let filter_by_value ~f {pc_set; const_map; branches; inequal_map} =
    let pc_set = PCSet.filter (PathCond.contains_with_pred ~f) pc_set in
    let const_map = ConstMap.filter (fun v c -> f v || f c) const_map in
    let branches = PCSet.filter (PathCond.contains_with_pred ~f) branches in
    let inequal_map = InEqualMap.filter (fun v consts -> f v || ValSet.exists f consts) inequal_map in
    {pc_set; const_map; branches; inequal_map}


  let weak_join ~lhs ~rhs =
    let pc_set = PCSet.inter lhs.pc_set rhs.pc_set in
    let branches = PCSet.inter lhs.branches rhs.branches in
    let all_symbolic_values =
      all_values lhs @ all_values rhs |> List.filter ~f:(not <<< Val.is_concrete) |> ValSet.of_list
    in
    let inequal_map =
      InEqualMap.merge
        (fun _ c1_opt c2_opt ->
          match (c1_opt, c2_opt) with
          | Some consts1, Some consts2 ->
              Some (ValSet.inter consts1 consts2)
          | _ ->
              None)
        lhs.inequal_map rhs.inequal_map
    in
    ValSet.fold
      (fun v acc ->
        match (ConstMap.find_opt v lhs.const_map, ConstMap.find_opt v rhs.const_map) with
        | Some c1, Some c2 when Val.equal c1 c2 ->
            (* v -> c, v -> c => v -> c *)
            {acc with const_map= ConstMap.add v c1 acc.const_map}
        | Some _, Some _ ->
            (* v -> c1, v -> c2 => merge v != c1s, v != c2s to v != c1s inter c2s *)
            acc
        | Some c1, None -> (
          match List.find (inequal_values rhs v) ~f:Val.is_concrete with
          | Some c2 when Val.equal c1 c2 ->
              acc
          | Some c2 ->
              (* e.g., join (x = "", x != null) => x != null *)
              {acc with inequal_map= InEqualMap.add_elt v c2 acc.inequal_map}
          | None ->
              acc )
        | None, Some c2 -> (
          match List.find (inequal_values lhs v) ~f:Val.is_concrete with
          | Some c1 when Val.equal c1 c2 ->
              acc
          | Some c1 ->
              (* e.g., join (x = "", x != null) => x != null *)
              {acc with inequal_map= InEqualMap.add_elt v c1 acc.inequal_map}
          | None ->
              acc )
        | None, None ->
            acc)
      all_symbolic_values
      {pc_set; const_map= ConstMap.empty; branches; inequal_map}


  (* ConstMap.merge
         (fun v c1_opt c2_opt ->
           match (c1_opt, c2_opt) with
           | Some c1, Some c2 when Val.equal c1 c2 ->
               Some c1
           | Some _, Some _ ->
               None
           | Some c1, None when
               List.exists (inequal_values rhs v) ~f:Val.equal c1 ->

           | None, Some c2 ->
               None
           | None, None ->
               None)
         lhs.const_map rhs.const_map
     in
     {pc_set; const_map} *)

  let invalid = {empty with pc_set= PCSet.singleton PathCond.false_cond}

  let cardinal {pc_set; const_map} = PCSet.cardinal pc_set + ConstMap.cardinal const_map
end
