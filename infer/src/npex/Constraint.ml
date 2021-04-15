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

  val replace_sub : t -> src:t -> dst:t -> t

  val replace_by_map : t -> f:(t -> t) -> t
end

module Make (Val : S) = struct
  type t = PEquals of Val.t * Val.t | Not of t | Equals of Val.t * Val.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let compare x y =
    let rec _compare x y =
      match (x, y) with
      | PEquals (v1, v2), PEquals (v1', v2') ->
          let first_compare = Val.compare v1 v1' in
          if Int.equal first_compare 0 then Val.compare v2 v2' else first_compare
      | PEquals _, _ ->
          1
      | _, PEquals _ ->
          -1
      | Not x, Not y ->
          _compare x y
      | x, y ->
          compare x y
    in
    _compare x y


  (* TODO: do it *)
  let rec pp fmt = function
    | PEquals (v1, v2) ->
        F.fprintf fmt "%a == %a" Val.pp v1 Val.pp v2
    | Not (PEquals (v1, v2)) ->
        F.fprintf fmt "%a != %a" Val.pp v1 Val.pp v2
    | Not pc ->
        F.fprintf fmt "Not (%a)" pp pc
    | Equals (v1, v2) ->
        F.fprintf fmt "Equals (%a, %a)" Val.pp v1 Val.pp v2


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
  module PathCond = Make (Val)
  module PCSet = PrettyPrintable.MakePPSet (PathCond)
  module ConstMap = PrettyPrintable.MakePPMonoMap (Val) (Val)

  type t = {pc_set: PCSet.t; const_map: ConstMap.t}

  let to_pc_set {pc_set; const_map} =
    (* TODO: it may have scalability issues *)
    ConstMap.fold (fun v const -> PCSet.add (PathCond.make_physical_equals Binop.Eq v const)) const_map pc_set


  let all_values {pc_set; const_map} =
    let values_in_non_const = List.concat_map (PCSet.elements pc_set) ~f:PathCond.vals_of_path_cond in
    let values_in_const = ConstMap.fold (fun v c acc -> v :: c :: acc) const_map [] in
    values_in_const @ values_in_non_const


  let empty = {pc_set= PCSet.empty; const_map= ConstMap.empty}

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


  let pp fmt x = Pp.of_string ~f:to_string fmt x

  let debug_if_invalid_pc transitives original_cond =
    if List.exists transitives ~f:PathCond.is_invalid then
      L.d_printfln "Invalid condition generated by %a" PathCond.pp original_cond


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


  let is_valid pathcond pc = PathCond.is_valid pathcond || PCSet.mem pathcond pc.pc_set

  let is_invalid {pc_set} = PCSet.exists PathCond.is_invalid pc_set

  let update_const_map pc transitives =
    (* TODO: it may have scalability issues *)
    let const_map =
      PCSet.fold
        (fun cond acc ->
          match cond with
          | PathCond.PEquals (v1, v2) when Val.is_concrete v1 && not (Val.is_concrete v2) ->
              ConstMap.add v2 v1 acc
          | PathCond.PEquals (v1, v2) when Val.is_concrete v2 && not (Val.is_concrete v1) ->
              ConstMap.add v1 v2 acc
          | _ ->
              acc)
        transitives pc.const_map
    in
    let pc_set =
      PCSet.map
        (PathCond.replace_by_map ~f:(fun v ->
             match ConstMap.find_opt v const_map with Some const -> const | None -> v))
        transitives
      |> PCSet.filter (not <<< PathCond.is_valid)
    in
    {pc_set; const_map}


  let add pathcond pc =
    if PathCond.contains_absval pathcond || PathCond.is_valid pathcond then pc
    else if PathCond.is_invalid pathcond then {pc with pc_set= PCSet.add pathcond pc.pc_set}
    else
      let transitives = compute_transitives pathcond pc in
      update_const_map pc transitives


  let replace_by_map ~f {pc_set; const_map} =
    let pc_set = PCSet.map (PathCond.replace_by_map ~f) pc_set in
    let const_map = ConstMap.fold (fun v const -> ConstMap.add (f v) (f const)) const_map ConstMap.empty in
    {pc_set; const_map}


  let replace_value {pc_set; const_map} ~(src : Val.t) ~(dst : Val.t) =
    let pc_set = PCSet.map (PathCond.replace_value ~src ~dst) pc_set in
    let const_map =
      ConstMap.fold (fun v const -> ConstMap.add (Val.replace_sub ~src ~dst v) const) const_map ConstMap.empty
    in
    {pc_set; const_map}


  let join pc1 pc2 = PCSet.fold add (to_pc_set pc2) pc1

  let merge pc1 pc2 = PCSet.fold add (PCSet.inter (to_pc_set pc1) (to_pc_set pc2)) empty

  let check_sat pc1 pc2 =
    let pc_unioned = join pc1 pc2 in
    let result = not (is_invalid pc_unioned) in
    let debug_msg =
      if Config.debug_mode then
        F.asprintf "===== check sat =====@. - lhs: %a@. - rhs: %a@. - unioned: %a@. - result: %b@." pp pc1 pp pc2
          pp pc_unioned result
      else F.asprintf "===== check sat =====@. - lhs: %a@. - rhs: %a@. - result: %b@." pp pc1 pp pc2 result
    in
    if Config.debug_mode then L.progress "%s" debug_msg ;
    result


  let check_valid pc1 pc2 =
    let pc_set1 = PCSet.filter (not <<< PathCond.is_valid) (to_pc_set pc1) in
    let pc_set2 = PCSet.filter (not <<< PathCond.is_valid) (to_pc_set pc2) in
    let result = (* TODO: check *) PCSet.equal pc_set1 pc_set2 in
    let debug_msg =
      F.asprintf "===== check validity ====@. - lhs: %a@. - rhs: %a@. - result: %b@." pp pc1 pp pc2 result
    in
    if Config.debug_mode then L.progress "%s" debug_msg ;
    result


  let equal_values {pc_set; const_map} v =
    match ConstMap.find_opt v const_map with
    | Some const ->
        [v; const]
    | None ->
        PCSet.fold
          (function
            | PathCond.PEquals (v1, v2) when Val.equal v1 v ->
                fun acc -> v2 :: acc
            | PathCond.PEquals (v1, v2) when Val.equal v2 v ->
                fun acc -> v1 :: acc
            | _ ->
                fun acc -> acc)
          pc_set [v]


  let inequal_values {pc_set} v =
    PCSet.fold
      (function
        | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.equal v1 v ->
            fun acc -> v2 :: acc
        | PathCond.Not (PathCond.PEquals (v1, v2)) when Val.equal v2 v ->
            fun acc -> v1 :: acc
        | _ ->
            fun acc -> acc)
      pc_set []


  let filter_by_value ~f {pc_set; const_map} =
    let pc_set = PCSet.filter (PathCond.contains_with_pred ~f) pc_set in
    let const_map = ConstMap.filter (fun v c -> f v || f c) const_map in
    {pc_set; const_map}


  let cardinal {pc_set; const_map} = PCSet.cardinal pc_set + ConstMap.cardinal const_map
end
