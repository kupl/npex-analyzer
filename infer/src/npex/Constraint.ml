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
end

module Make (Val : S) = struct
  type t = PEquals of Val.t * Val.t | Not of t | Equals of Val.t * Val.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let compare x y =
    match (x, y) with
    | PEquals (v1, v2), PEquals (v1', v2') ->
        let first_compare = Val.compare v1 v1' in
        if Int.equal first_compare 0 then Val.compare v2 v2' else first_compare
    | PEquals _, _ ->
        1
    | _, PEquals _ ->
        -1
    | x, y ->
        compare x y


  let rec replace_value x ~src ~dst =
    match x with
    | PEquals (v1, v2) ->
        let v1', v2' = ((if phys_equal src v1 then dst else v1), if phys_equal src v2 then dst else v2) in
        PEquals (v1', v2')
    | Not x ->
        Not (replace_value x ~src ~dst)
    | Equals (v1, v2) ->
        let v1', v2' = ((if phys_equal src v1 then dst else v1), if phys_equal src v2 then dst else v2) in
        Equals (v1', v2')


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
    | Not cond -> (
      match check cond with Valid -> UnSAT | Satisfiable -> Satisfiable | UnSAT -> Valid | Unknown -> Unknown )
    | _ ->
        (* TODO: add *)
        Unknown


  let is_valid x = match check x with Valid -> true | _ -> false

  let is_invalid x = match check x with UnSAT -> true | _ -> false

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


  let make_negation = function Not x -> x | _ as x -> Not x

  let make_physical_equals binop v1 v2 =
    (* if v1 or v2 contain symbol, then make condition
       else if no symbol in v1 or v2, it evaluates to true or false *)
    (* let[@warning "-8"] [v1; v2] = List.sort [v1; v2] ~compare:Val.compare in *)
    let order = Val.compare v1 v2 in
    let v1, v2 = if Int.( <= ) order 0 then (v1, v2) else (v2, v1) in
    L.d_printfln "Make physical equals from (%s, %a, %a)" (Binop.str Pp.text binop) Val.pp v1 Val.pp v2 ;
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


  let rec vals_of_path_cond = function
    | PEquals (v1, v2) | Equals (v1, v2) ->
        [v1; v2]
    | Not pc ->
        vals_of_path_cond pc
end

module MakePC (Val : S) = struct
  module PathCond = Make (Val)
  include AbstractDomain.FiniteSet (PathCond)

  let compute_transitives pathcond pc =
    let open PathCond in
    let pc_to_add =
      fold
        (fun cond acc ->
          match (pathcond, cond) with
          | PEquals (v1, v2), PEquals (v1', v2') when Val.equal v1 v1' ->
              add (PEquals (v2, v2')) acc
          | PEquals (v1, v2), PEquals (v2', v1') when Val.equal v1 v1' ->
              add (PEquals (v2, v2')) acc
          | PEquals (v2, v1), PEquals (v1', v2') when Val.equal v1 v1' ->
              add (PEquals (v2, v2')) acc
          | PEquals (v2, v1), PEquals (v2', v1') when Val.equal v1 v1' ->
              add (PEquals (v2, v2')) acc
          | PEquals (v1, v2), Not (PEquals (v1', v2')) when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | PEquals (v1, v2), Not (PEquals (v2', v1')) when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | PEquals (v2, v1), Not (PEquals (v1', v2')) when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | PEquals (v2, v1), Not (PEquals (v2', v1')) when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | Not (PEquals (v1, v2)), PEquals (v1', v2') when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | Not (PEquals (v1, v2)), PEquals (v2', v1') when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | Not (PEquals (v2, v1)), PEquals (v1', v2') when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | Not (PEquals (v2, v1)), PEquals (v2', v1') when Val.equal v1 v1' ->
              add (Not (PEquals (v2, v2'))) acc
          | _ ->
              acc)
        pc (singleton pathcond)
    in
    map PathCond.sorted pc_to_add


  let is_valid pathcond pc = PathCond.is_valid pathcond || mem pathcond pc

  let add pathcond pc =
    if PathCond.contains_absval pathcond || PathCond.is_valid pathcond then pc
    else if PathCond.is_invalid pathcond then singleton PathCond.false_cond
    else
      let transitives = compute_transitives pathcond pc in
      union pc (filter (fun cond -> not (PathCond.is_valid cond)) transitives)


  let replace_value pc ~(src : Val.t) ~(dst : Val.t) = map (PathCond.replace_value ~src ~dst) pc

  let check_sat pc1 pc2 =
    let pc_unioned = fold add pc1 pc2 in
    let result = not (exists PathCond.is_invalid pc_unioned) in
    let debug_msg =
      F.asprintf "===== check sat =====@. - lhs: %a@. - rhs: %a@. - unioned: %a@. - result: %b@." pp pc1 pp pc2 pp
        pc_unioned result
    in
    L.progress "%s" debug_msg ; result


  let check_valid pc1 pc2 =
    let result = (* TODO: check *) equal pc1 pc2 in
    let debug_msg =
      F.asprintf "===== check validity ====@. - lhs: %a@. - rhs: %a@. - result: %b@." pp pc1 pp pc2 result
    in
    L.progress "%s" debug_msg ; result
end
