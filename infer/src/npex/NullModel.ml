open! IStd
open! Vocab

module Pos = struct
  type t = InstrNode.t * int [@@deriving compare]

  let pp fmt (InstrNode.{inode; instr}, pos) =
    let null_access_str =
      match instr with
      | Sil.Call (_, Const (Cfun procname), _, _, {cf_virtual}) when cf_virtual ->
          let method_name = Procname.get_method procname in
          if Int.equal pos 0 then F.asprintf "NULL.%s(_)" method_name
          else F.asprintf "_.%s(%d-th NULL)" method_name pos
      | Sil.Call (_, Const (Cfun procname), _, _, _) ->
          let method_name = Procname.get_method procname in
          F.asprintf "_.%s(%d-th NULL)" method_name pos
      | _ ->
          ""
    in
    F.fprintf fmt "%s (%a)" null_access_str Location.pp_line (InterNode.get_loc inode)
end

module MValue = struct
  type t = model_exp list * prob [@@deriving compare]

  and model_exp =
    (* TODO: design static field (e.g., Collections.EMPTY_SET) *)
    | NULL
    | Const of Const.t
    | Param of int
    | Assign of model_exp * model_exp
    | Call of Procname.t * model_exp list
    | Skip
    | Exn of string
    | NonNull

  and prob = float

  let equal = [%compare.equal: t]

  let no_apply = ([], 0.5)

  let rec pp_model_exp fmt = function
    | NULL ->
        F.fprintf fmt "NULL"
    | Const c ->
        (Const.pp Pp.text) fmt c
    | Param i ->
        F.fprintf fmt "(#%d)" i
    | Assign (lhs, rhs) ->
        F.fprintf fmt "%a := %a" pp_model_exp lhs pp_model_exp rhs
    | Call (proc, args) ->
        F.fprintf fmt "%s(%a)" (Procname.get_method proc) (Pp.seq ~sep:"," pp_model_exp) args
    | Skip ->
        F.fprintf fmt "SKIP"
    | Exn exn_type ->
        F.fprintf fmt "throw new %s" exn_type
    | NonNull ->
        F.fprintf fmt "NonNull"


  let make_null ~prob : t = ([NULL], prob)

  let make_const ~prob const : t = ([Const const], prob)

  let make_skip ~prob : t = ([Skip], prob)

  let make_exn ~prob exn_type : t = ([Exn exn_type], prob)

  let make_nonnull ~prob : t = ([NonNull], prob)

  let from_string_opt mval_str ~prob : t option =
    match mval_str with
    | "0" | "false" ->
        Some (make_const ~prob (Const.Cint IntLit.zero))
    | "1" | "true" ->
        Some (make_const ~prob (Const.Cint IntLit.one))
    | "0.0" ->
        Some (make_const ~prob (Const.Cfloat 0.0))
    | "null" ->
        Some (make_null ~prob)
    | "NPEX_SKIP_VALUE" | "\"NPEX_SKIP_VALUE\"" ->
        Some (make_skip ~prob)
    | "NPEXNonLiteral" ->
        Some (make_nonnull ~prob)
    | "\"\"" ->
        Some (make_const ~prob (Const.Cstr ""))
    | "\"null\"" ->
        Some (make_const ~prob (Const.Cstr "null"))
    | _ ->
        (* TODO: *)
        L.progress "[WARNING]: model value %s is not resolved@." mval_str ;
        None


  let pp fmt (model_exp_list, prob) = F.fprintf fmt "%f (%a)" prob (Pp.seq ~sep:" ; " pp_model_exp) model_exp_list
end

module MValueSet = PrettyPrintable.MakePPSet (MValue)
include PrettyPrintable.MakePPMonoMap (Pos) (MValueSet)

let joinable lhs rhs =
  (* TODO: should apply same model for same deref-field *)
  fold
    (fun pos mval_lhs acc ->
      if acc then
        match find_opt pos rhs with
        | Some mval_rhs when MValueSet.equal mval_lhs mval_rhs ->
            acc
        | Some _ ->
            false
        | None ->
            true
      else acc)
    lhs true


let weak_join ~lhs ~rhs =
  union
    (fun pos mval1 mval2 ->
      if MValueSet.equal mval1 mval2 then Some mval1
      else
        raise
          (Unexpected
             (F.asprintf "Not Joinable! (%a -> %a and %a)" Pos.pp pos MValueSet.pp mval1 MValueSet.pp mval2)))
    lhs rhs


let model = ref empty

let add_element pos mval t =
  match find_opt pos t with
  | Some mvalues ->
      add pos (MValueSet.add mval mvalues) t
  | None ->
      add pos (MValueSet.singleton mval) t


module LocField = struct
  type t = {loc: Location.t; invoked_field: string; index: int} [@@deriving compare]

  let pp fmt {loc; invoked_field} = F.fprintf fmt "%s (%a)" invoked_field Location.pp_file_pos loc

  let make loc invoked_field index = {loc; invoked_field; index}
end

module LocFieldNodeMap = struct
  include PrettyPrintable.MakePPMonoMap (LocField) (InstrNode)

  let construct pdesc =
    let all_instr_nodes = Procdesc.get_nodes pdesc |> List.concat_map ~f:InstrNode.list_of_pnode in
    List.fold all_instr_nodes ~init:empty ~f:(fun acc instr_node ->
        let loc = InstrNode.get_loc instr_node in
        match InstrNode.get_instr instr_node with
        | Sil.Call (_, Const (Cfun procname), _, _, _) ->
            let invoked_field = Procname.get_method procname in
            add (LocField.make loc invoked_field 0) instr_node acc
        | _ ->
            acc)
end

module LocFieldMValueMap = struct
  include PrettyPrintable.MakePPMonoMap (LocField) (MValueSet)

  let _cached = ref empty

  let add_elt k v t =
    match find_opt k t with
    | Some mvals ->
        add k (MValueSet.add v mvals) t
    | None ->
        add k (MValueSet.singleton v) t


  let from_json filepath : t =
    L.progress "@.Parse json@." ;
    let open Yojson.Basic.Util in
    let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
    let site_model_list = read_json_file_exn filepath |> to_list in
    let parse_and_collect acc site_model =
      let filename = site_model |> member "site" |> member "source_path" |> to_string in
      try
        let loc =
          let site_model = site_model |> member "site" in
          let file = source_file_from_string source_files filename in
          let line = site_model |> member "lineno" |> to_int in
          Location.{line; file; col= -1}
        in
        (*TODO: resolve model index by function type *)
        let model_index =
          let _model_index = site_model |> member "null_pos" |> to_int in
          let invo_kind = site_model |> member "key" |> member "invo_kind" |> to_string in
          if String.equal invo_kind "STATIC" then _model_index else _model_index + 1
        in
        let invoked_field = site_model |> member "site" |> member "deref_field" |> to_string in
        let mvalues =
          site_model
          |> member "proba"
          |> to_assoc
          |> List.filter_map ~f:(fun (mval_str, prob_json) ->
                 let prob = prob_json |> to_float in
                 MValue.from_string_opt mval_str ~prob)
        in
        let mvalues_top3 =
          (* HEURISTICS for state explosion *)
          (* TODO: or remove it by pruning states with too low probability *)
          let compare_prob (_, l_prob) (_, r_prob) = (r_prob -. l_prob) *. 100.0 |> Int.of_float in
          list_top_n mvalues ~compare:compare_prob ~n:3
        in
        List.fold mvalues_top3 ~init:acc ~f:(fun acc mval ->
            add_elt (LocField.make loc invoked_field model_index) mval acc)
      with Unexpected _ ->
        L.progress "[WARNING]: could not find source file %s from captured files@." filename ;
        acc
    in
    List.fold site_model_list ~init:empty ~f:parse_and_collect


  let get () : t =
    if is_empty !_cached then (
      _cached := from_json Config.npex_model_json ;
      !_cached )
    else !_cached


  let marshalled_path = Filename.concat Config.results_dir "loc_field_mvalue_map.data"

  let to_marshal t = Utils.with_file_out marshalled_path ~f:(fun oc -> Marshal.to_channel oc t [])

  let from_marshal () : t =
    if not (is_empty !_cached) then !_cached
    else
      let loc_field_mvalue_map =
        try Utils.with_file_in marshalled_path ~f:Marshal.from_channel
        with _ ->
          let _loc_field_mvalue_map = from_json Config.npex_model_json in
          (* L.progress "@.================================================================" ;
             L.progress "@.%a@." pp _loc_field_mvalue_map ;
             L.progress "================================================================@." ; *)
          to_marshal _loc_field_mvalue_map ; _loc_field_mvalue_map
      in
      _cached := loc_field_mvalue_map ;
      !_cached
end

let compute_probability t =
  let sum = fold (fun _ mvals acc -> (MValueSet.choose mvals |> snd) +. acc) t 0.5 in
  sum /. Float.of_int (cardinal t + 1)


let construct pdesc : t =
  (* OPTIMIZE: only construct null_model for each proc_desc *)
  let loc_field_node_map = LocFieldNodeMap.construct pdesc in
  let loc_field_mvalue_map = LocFieldMValueMap.from_marshal () in
  LocFieldNodeMap.fold
    (fun loc_field instr_node acc ->
      let possible_indice = [0; 1; 2] in
      List.fold possible_indice ~init:acc ~f:(fun acc index ->
          (* For null.toString(),
             * index = 0
             * index in json = -1
           * For SystemLib.write(null),
             * index = 0
             * index in json = 0 *)
          let loc_field = LocField.{loc_field with index= index + loc_field.index} in
          match LocFieldMValueMap.find_opt loc_field loc_field_mvalue_map with
          | Some mvalues ->
              let pos : Pos.t = (instr_node, index) in
              add pos mvalues acc
          | None ->
              acc))
    loc_field_node_map empty
