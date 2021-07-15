open! IStd
open! Vocab
module MExp = ModelDomain.MExp
module MValue = ModelDomain.MValue
module Pos = ModelDomain.Pos
module Key = ModelDomain.Key
module MExps = PrettyPrintable.MakePPSet (MExp)
module MValueSet = PrettyPrintable.MakePPSet (MValue)
include PrettyPrintable.MakePPMonoMap (Pos) (MValueSet)

let is_applicable pos mval t =
  for_all
    (fun pos' mvals' ->
      (not (Key.equal (Pos.to_key pos) (Pos.to_key pos'))) || MValue.equal_wo_prob mval (MValueSet.choose mvals'))
    t


let joinable lhs rhs =
  (* TODO: should apply same model for same deref-field *)
  for_all (fun pos mvals_lhs -> is_applicable pos (MValueSet.choose mvals_lhs) rhs) lhs


let weak_join ~lhs ~rhs =
  union
    (fun pos mval1 mval2 ->
      if MValue.equal_wo_prob (MValueSet.choose mval1) (MValueSet.choose mval2) then Some mval1
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
        let type_str = site_model |> member "key" |> member "return_type" |> to_string in
        let kind_str = site_model |> member "key" |> member "invo_kind" |> to_string in
        let mvalues =
          site_model
          |> member "proba"
          |> to_assoc
          |> List.filter_map ~f:(fun (mval_str, prob_json) ->
                 let prob = prob_json |> to_float in
                 MValue.from_string_opt ~mval_str ~type_str ~kind_str ~prob)
        in
        let mvalues_top3 =
          (* HEURISTICS for state explosion *)
          (* TODO: or remove it by pruning states with too low probability *)
          let compare_prob (_, l_prob) (_, r_prob) = (r_prob -. l_prob) *. 100.0 |> Int.of_float in
          (* remove model value with less than 1% *)
          list_top_n mvalues ~compare:compare_prob ~n:3 |> List.filter ~f:(fun (_, prob) -> Float.( > ) prob 0.01)
        in
        L.(debug Analysis Verbose) "Top 3 values: %a@." (Pp.seq MValue.pp) mvalues_top3 ;
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
  (* exclude no_apply model *)
  let no_apply_filtered = filter (fun _ v -> not (MValue.equal MValue.no_apply (MValueSet.choose v))) t in
  let sum = fold (fun _ mvals acc -> (MValueSet.choose mvals |> snd) +. acc) no_apply_filtered 0.5 in
  sum /. Float.of_int (cardinal no_apply_filtered + 1)


let construct pdesc : t =
  (* OPTIMIZE: only construct null_model for each proc_desc *)
  let loc_field_node_map = LocFieldNodeMap.construct pdesc in
  let loc_field_mvalue_map = LocFieldMValueMap.from_marshal () in
  LocFieldNodeMap.fold
    (fun loc_field instr_node acc ->
      let possible_indice = [0; 1; 2; 3] in
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


let mexps_from_mvalues : MValueSet.t -> MExps.t =
 fun mvalues ->
  let mvalue_list : MValue.t list = MValueSet.elements mvalues in
  List.map mvalue_list ~f:fst |> MExps.of_list
