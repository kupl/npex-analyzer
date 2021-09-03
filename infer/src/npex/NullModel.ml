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
    let parse_mvalues site_model member_field ~type_str ~kind_str =
      member member_field site_model
      |> to_assoc
      |> List.filter_map ~f:(fun (mval_str, prob_json) ->
             let prob = prob_json |> to_float in
             if Float.equal prob 0.0 then None else MValue.from_string_opt ~mval_str ~type_str ~kind_str ~prob)
    in
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
        let null_mvalues = parse_mvalues site_model "null_proba" ~type_str ~kind_str in
        let non_null_mvalues = parse_mvalues site_model "proba" ~type_str ~kind_str in
        let mvalues = null_mvalues @ non_null_mvalues in
        List.fold mvalues ~init:acc ~f:(fun acc mval ->
            add_elt (LocField.make loc invoked_field model_index) mval acc)
      with Unexpected msg ->
        (* L.(debug V) "[WARNING]: error occurs during parsing null model values:@.%s@." msg ; *)
        L.(debug Analysis Verbose) "[WARNING]: could not find source file %s from captured files@." filename ;
        acc
    in
    List.fold site_model_list ~init:empty ~f:parse_and_collect


  let get () : t =
    if is_empty !_cached then (
      _cached := from_json Config.npex_model_json ;
      String.Set.iter !ModelDomain.unresolved ~f:(fun model_str ->
          L.(debug Analysis Quiet) "Unresolve model string: %s@." model_str) ;
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
  (* let no_apply_filtered = filter (fun _ v -> not (MValue.equal MValue.no_apply (MValueSet.choose v))) t in *)
  let sum = fold (fun _ mvals acc -> (MValueSet.choose mvals |> snd) +. acc) t 0.5 in
  sum /. Float.of_int (cardinal t + 1)


let filter_feasible_top3_values instr_node mvalues =
  let mvalues = MValueSet.elements mvalues in
  let null_mvalue, non_null_mvalues =
    match List.partition_tf mvalues ~f:(fun (mexp, _) -> MExp.is_null mexp) with
    | [], non_null_mvalues ->
        (([MExp.NULL], 0.0), non_null_mvalues)
    | null_mvalue :: _, non_null_mvalues ->
        (null_mvalue, non_null_mvalues)
  in
  let is_feasible ret_typ arg_typs (mexps, _) =
    let has_valid_arg_pos = function MExp.Param i when i >= List.length arg_typs -> false | _ -> true in
    let _is_feasible = function
      | MExp.Param i when i >= List.length arg_typs ->
          false
      | MExp.Param i
        when (not (Typ.equal ret_typ (List.nth_exn arg_typs i |> snd)))
             || Typ.equal ret_typ Typ.pointer_to_java_lang_object ->
          false
      | MExp.Call ("EQ", args) ->
          Typ.is_int ret_typ && List.for_all args ~f:has_valid_arg_pos
      | MExp.Call (_, args) ->
          List.for_all args ~f:has_valid_arg_pos
      | MExp.NULL when not (Typ.is_pointer ret_typ) ->
          false
      | _ ->
          true
    in
    List.for_all mexps ~f:_is_feasible
  in
  let mvalues_top3 mvalues =
    (* HEURISTICS for state explosion *)
    (* TODO: or remove it by pruning states with too low probability *)
    let compare_prob (_, l_prob) (_, r_prob) =
      try (r_prob -. l_prob) *. 100.0 |> Int.of_float
      with _ -> L.(die InternalError) "%a@." (Pp.seq MValue.pp) mvalues
    in
    (* remove model value with less than 1% *)
    list_top_n mvalues ~compare:compare_prob ~n:3 |> MValueSet.of_list
  in
  match InstrNode.get_instr instr_node with
  | Sil.Call ((_, ret_typ), Const (Cfun callee), arg_typs, _, _)
    when not (Procname.is_constructor callee || is_feasible ret_typ arg_typs null_mvalue) ->
      (* No NULL *)
      let feasibles, infeasibles = List.partition_tf non_null_mvalues ~f:(is_feasible ret_typ arg_typs) in
      let infeasible_prob = List.fold infeasibles ~init:0.0 ~f:(fun acc (_, prob) -> prob +. acc) in
      let feasibles =
        List.filter feasibles ~f:(fun (_, prob) -> Float.( > ) prob 0.01)
        |> List.map ~f:(fun (mexp, prob) -> (mexp, prob /. (1.0 -. infeasible_prob)))
      in
      let mvalues_top3 = mvalues_top3 feasibles in
      L.(debug Analysis Verbose) "Top 3 values: %a@." MValueSet.pp mvalues_top3 ;
      mvalues_top3
  | Sil.Call ((_, ret_typ), Const (Cfun callee), arg_typs, _, _) ->
      let feasibles, infeasibles = List.partition_tf non_null_mvalues ~f:(is_feasible ret_typ arg_typs) in
      (* L.progress "Feasibles, Infeasbiles of %a@.Feasibles: %a@. Infeasibles: %a@." (Pp.seq MValue.pp) mvalues
         (Pp.seq MValue.pp) feasibles (Pp.seq MValue.pp) infeasibles ; *)
      if List.is_empty feasibles then MValueSet.singleton null_mvalue
      else
        let infeasible_prob = List.fold infeasibles ~init:0.0 ~f:(fun acc (_, prob) -> prob +. acc) in
        if Float.( > ) infeasible_prob 0.99 then MValueSet.empty
        else
          let feasibles =
            List.filter feasibles ~f:(fun (_, prob) -> Float.( > ) prob 0.01)
            |> List.map ~f:(fun (mexp, prob) ->
                   (mexp, prob *. (1.0 -. snd null_mvalue) /. (1.0 -. infeasible_prob)))
          in
          (* L.progress "Lifted Feasibles: %a (%f)@." (Pp.seq MValue.pp) feasibles infeasible_prob ; *)
          let mvalues_top3 = mvalues_top3 (null_mvalue :: feasibles) in
          L.(debug Analysis Verbose) "Top 3 values: %a@." MValueSet.pp mvalues_top3 ;
          mvalues_top3
  | _ ->
      MValueSet.empty


let construct pdesc : t =
  (* OPTIMIZE: only construct null_model for each proc_desc *)
  let loc_field_mvalue_map = LocFieldMValueMap.from_marshal () in
  let instr_nodes = Procdesc.get_nodes pdesc |> List.concat_map ~f:InstrNode.list_of_pnode in
  List.fold instr_nodes ~init:empty ~f:(fun acc instr_node ->
      let possible_indice = [0; 1; 2; 3] in
      List.fold possible_indice ~init:acc ~f:(fun acc index ->
          (* For null.toString(),
             * index = 0
             * index in json = -1
           * For SystemLib.write(null),
             * index = 0
             * index in json = 0 *)
          let loc = InstrNode.get_loc instr_node in
          match InstrNode.get_instr instr_node with
          | Sil.Call (_, Const (Cfun procname), _, _, _) -> (
              let invoked_field = Procname.get_method procname in
              let loc_field = LocField.make loc invoked_field index in
              match LocFieldMValueMap.find_opt loc_field loc_field_mvalue_map with
              | Some mvalues ->
                  let pos : Pos.t = (instr_node, index) in
                  (* L.progress "filter mvalues of %a: %a@." Pos.pp pos MValueSet.pp mvalues ; *)
                  let mvalues_top3 = filter_feasible_top3_values instr_node mvalues in
                  (* L.progress "MValues of %a: %a@." Pos.pp pos MValueSet.pp mvalues_top3 ; *)
                  add pos mvalues_top3 acc
              | None ->
                  acc )
          | _ ->
              acc))


let mexps_from_mvalues : MValueSet.t -> MExps.t =
 fun mvalues ->
  let mvalue_list : MValue.t list = MValueSet.elements mvalues in
  List.map mvalue_list ~f:fst |> MExps.of_list
