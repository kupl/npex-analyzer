open! IStd
open! Vocab
module L = Logging
module F = Format
module CFG = SpecChecker.CFG
module Val = SymDom.Val

module Fault = struct
  type ftype = NullAssign | NullConst | NullDeref | Parameter [@@deriving compare]

  let to_string_ftype = function
  | NullAssign -> "NullAssign"
  | NullConst -> "NullConst"
  | NullDeref -> "NullDereference"
  | Parameter -> "Parameter"
  [@@ocamlformat "disable"]

  type t = {location: InstrNode.t; nullexp: AccessExpr.t; fault_type: ftype} [@@deriving compare]

  let pp fmt {location; nullexp; fault_type} = F.fprintf fmt 
    "@[<v 2> - Location: %a@] 
     @[<v 2> - NullExp: %a@] 
     @[<v 2> - DerefField: %s@] 
     @[<v 2> - Fault Type: %s@]"
    InstrNode.pp location AccessExpr.pp nullexp (AccessExpr.get_deref_field nullexp) (to_string_ftype fault_type)
    [@@ocamlformat "disable"]
end

module Faults = AbstractDomain.FiniteSet (Fault)
module ExecutedProcs = AbstractDomain.FiniteSet (Procname)
module Domain = AbstractDomain.Pair (Faults) (ExecutedProcs)
module Summary = Domain

let empty = (Faults.bottom, ExecutedProcs.bottom)

let parse_trace_nodes program =
  let open Yojson.Basic.Util in
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let json = read_json_file_exn "traces.json" in
  let traces = json |> to_list in
  let results =
    List.concat_map traces ~f:(fun trace_json ->
        try
          let loc =
            let file = trace_json |> member "filepath" |> to_string |> source_file_from_string source_files in
            let line = trace_json |> member "line" |> to_int in
            Location.{line; file; col= -1}
          in
          Program.find_node_with_location program loc
        with _ -> [])
  in
  let nullpoints = NullPoint.get_nullpoint_list program |> List.map ~f:NullPoint.get_node in
  if List.exists results ~f:(List.mem nullpoints ~equal:InterNode.equal) then results else []


let parse_trace program =
  let trace_nodes = parse_trace_nodes program in
  let target_procs = List.map trace_nodes ~f:fst in
  Program.slice_virtual_calls program (Procname.Set.of_list target_procs) (Procname.Set.of_list target_procs) ;
  target_procs


let check_instr proc_desc post null_values node instr : Domain.t option =
  let location = InstrNode.of_pnode node instr in
  let open SpecCheckerDomain in
  let is_target_null_exp exp ~pos =
    (* x = null; // localize "x" as null-src
         x.foo(); // TODO: localize "x"
         x.goo(); // should not be localized since x != null
    *)
    let is_nullable value astate =
      if List.mem (inequal_values astate value) Val.default_null ~equal:Val.equal then (
        ( if Config.debug_mode then
          match AccessExpr.from_IR_exp_opt proc_desc exp with
          | Some aexpr ->
              L.progress "%a is not nullable (%a)@." AccessExpr.pp aexpr Location.pp_file_pos
                (Procdesc.Node.get_loc node)
          | None ->
              L.progress "%a is not nullable (%a)@." Exp.pp exp Location.pp_file_pos (Procdesc.Node.get_loc node)
        ) ;
        false )
      else true
    in
    (* use phys_equal to is_target not to collect other null sources *)
    let is_target value =
      let result = List.mem (Val.Set.elements null_values) value ~equal:phys_equal in
      L.(debug Analysis Verbose)
        "@.[CheckInstr %a]@.  %a is target values? %b (%a)@." InstrNode.pp location Val.pp value result Val.Set.pp
        null_values ;
      result
    in
    List.exists post ~f:(fun astate ->
        try
          let value = eval astate ~pos node instr exp in
          is_target value && is_nullable value astate
        with _ ->
          L.(debug Analysis Verbose)
            "@.[CheckInstr %a]@.  failed to evaluate %a@." InstrNode.pp location Exp.pp exp ;
          false)
  in
  let check_exp exp ~pos =
    match AccessExpr.from_IR_exp_opt proc_desc exp with
    | Some nullexp when AccessExpr.equal nullexp AccessExpr.null ->
        if is_target_null_exp exp ~pos then Some Fault.{location; nullexp; fault_type= NullConst} else None
    | Some nullexp ->
        (* let is_target =
             List.exists astates ~f:(fun astate -> Val.Set.mem (eval astate ~pos node instr exp) null_values)
           in
           L.progress "check if %a is target_null: %b (%a)@." AccessExpr.pp nullexp is_target Location.pp_file_pos
             (Procdesc.Node.get_loc node) ; *)
        if is_target_null_exp exp ~pos then Some Fault.{location; nullexp; fault_type= NullAssign} else None
    | None when is_target_null_exp exp ~pos ->
        L.progress "Failed to convert null-exp %a to access expression at %a" Exp.pp exp InstrNode.pp location ;
        None
    | None ->
        None
  in
  let fault_opt =
    match instr with
    | Sil.Call ((ret_id, ret_typ), _, arg_typs, _, _) ->
        List.find_mapi ((Exp.Var ret_id, ret_typ) :: arg_typs) ~f:(fun pos (arg_exp, _) -> check_exp arg_exp ~pos)
    | Sil.Store {e2} ->
        check_exp e2 ~pos:0
    | _ ->
        None
  in
  match fault_opt with
  | Some fault ->
      let executed_procs =
        List.fold post ~init:ExecutedProcs.empty ~f:(fun acc astate ->
            Procname.Set.fold (fun proc -> ExecutedProcs.add proc) SpecCheckerDomain.(astate.executed_procs) acc)
      in
      Some (Faults.singleton fault, executed_procs)
  | _ ->
      None


let check_node proc_desc post nullvalues node : Domain.t =
  Instrs.fold (CFG.instrs node) ~init:empty ~f:(fun acc instr ->
      let post_opt = check_instr proc_desc post nullvalues node instr in
      match post_opt with Some post -> Domain.join post acc | _ -> acc)


let _reachables = ref Procname.Set.empty

let reachable_from_traces program =
  if Procname.Set.is_empty !_reachables then (
    let traces = parse_trace program in
    let nullproc = NullPoint.get_nullpoint_list program |> List.hd_exn |> NullPoint.get_procname in
    let reachables =
      if List.is_empty traces then
        Program.cg_reachables_of ~forward:true ~reflexive:true program (Procname.Set.singleton nullproc)
      else Program.cg_reachables_of ~forward:true ~reflexive:true program (Procname.Set.of_list traces)
    in
    _reachables := reachables ;
    reachables )
  else !_reachables


let checker ({InterproceduralAnalysis.proc_desc} as interproc) : Summary.t option =
  (* let proc_name = Procdesc.get_proc_name proc_desc in *)
  let cfg = CFG.from_pdesc proc_desc in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let analysis_data =
    SpecChecker.DisjReady.analysis_data (InterproceduralAnalysis.bind_payload interproc ~f:snd)
  in
  let program = analysis_data.SpecChecker.DisjReady.program in
  (* L.progress "reachable from traces: %a@." Procname.Set.pp (reachable_from_traces program) ; *)
  let inv_map =
    (* HEURISTICS: ignore class initializer which may be called at main procedure. *)
    if Procname.is_java_class_initializer proc_name then SpecChecker.CFG.Node.IdMap.empty
    else if not (Procname.Set.mem proc_name (reachable_from_traces program)) then SpecChecker.CFG.Node.IdMap.empty
    else SpecChecker.cached_compute_invariant_map analysis_data
  in
  let specchecker_summaries =
    SpecChecker.compute_summary proc_desc cfg inv_map |> SpecCheckerSummary.get_local_disjuncts
  in
  let nullvalues =
    CFG.fold_nodes cfg ~init:Val.Set.empty ~f:(fun acc node ->
        match SpecChecker.Analyzer.extract_state (CFG.Node.id node) inv_map with
        | Some {post} ->
            List.fold post ~init:acc ~f:(fun acc astate ->
                Val.Set.union acc (SpecCheckerDomain.get_nullptrs astate))
        | None ->
            acc)
  in
  if Val.Set.is_empty nullvalues then Some (Faults.empty, ExecutedProcs.empty)
  else
    let faults, executed_procs =
      CFG.fold_nodes cfg ~init:empty ~f:(fun acc node ->
          match SpecChecker.Analyzer.extract_state (CFG.Node.id node) inv_map with
          | Some {post} ->
              Domain.join (check_node proc_desc post nullvalues node) acc
          | None ->
              acc)
    in
    if Config.debug_level_analysis > 0 && not (Val.Set.is_empty nullvalues) then
      L.progress " - find null value assigns@.   - null_values: %a@.   - method: %a   - faults: %a@." Val.Set.pp
        nullvalues Procname.pp proc_name Faults.pp faults ;
    let param_faults =
      Val.Set.fold
        (fun v acc ->
          match v with
          | Val.Vheap (SymDom.SymHeap.Symbol s) | Val.Vint (SymDom.SymExp.Symbol s) ->
              let nullexp = SymDom.Symbol.to_ap s in
              if AccessExpr.is_var nullexp then
                let location = InstrNode.of_pnode (Procdesc.get_start_node proc_desc) Sil.skip_instr in
                Faults.add Fault.{location; nullexp; fault_type= Parameter} acc
              else (* TODO: is it necessary? *)
                acc
          | _ ->
              acc)
        nullvalues Faults.empty
    in
    let executed_procs =
      (* let executed_procs_of_npe =
         List.filter specchecker_summaries ~f:SpecCheckerDomain.is_npe_alternative
         |> List.fold ~init:ExecutedProcs.empty ~f:(fun acc astate ->
                Procname.Set.fold (fun proc -> ExecutedProcs.add proc) SpecCheckerDomain.(astate.executed_procs) acc)
         in *)
      specchecker_summaries
      |> List.fold ~init:ExecutedProcs.empty ~f:(fun acc astate ->
             Procname.Set.fold (fun proc -> ExecutedProcs.add proc) SpecCheckerDomain.(astate.executed_procs) acc)
    in
    Some (Faults.union faults param_faults, executed_procs)


let collect_faults ~get_summary proc acc =
  match get_summary proc with Some summary -> Faults.union summary acc | None -> acc


let generate_npe_list faults =
  Faults.iter
    (fun Fault.{location; nullexp; fault_type} ->
      let Location.{file; line} = InstrNode.get_loc location in
      let proc_name = InstrNode.get_proc_name location in
      let class_name =
        match proc_name with
        | Procname.Java java ->
            Procname.Java.get_simple_class_name java
        | _ as proc ->
            L.(die ExternalError) "%a is not java method" Procname.pp proc
      in
      (* TODO: multiple access expressions? *)
      let deref_field = AccessExpr.get_deref_field nullexp in
      let json =
        let filepath_json = `String (SourceFile.to_string file) in
        let line_json = `Int line in
        let deref_field_json = `String deref_field in
        let npe_class_json = `String class_name in
        let npe_method_json = `String (Procname.get_method proc_name) in
        let fault_type_json = `String (Fault.to_string_ftype fault_type) in
        `Assoc
          [ ("filepath", filepath_json)
          ; ("line", line_json)
          ; ("deref_field", deref_field_json)
          ; ("npe_class", npe_class_json)
          ; ("npe_method", npe_method_json)
          ; ("fault_type", fault_type_json) ]
      in
      let filename = String.split (SourceFile.to_string file) ~on:'/' |> List.rev |> List.hd_exn in
      Utils.write_json_to_file (F.asprintf "npe_%s_%d.json" filename line) json)
    faults


(* 
let target_procs program nullpoint executed_procs trace_procs =
  Program.slice_virtual_calls program executed_procs trace_procs ;
  let rec single_caller program proc =
    let callers = Program.callers_of_proc program proc |> Procname.Set.of_list |> Procname.Set.inter trace_procs in
    match Procname.Set.elements callers with [pred] -> single_caller program pred | _ -> proc
  in
  let slice_by_entry program entry =
    let targets = Procname.Set.singleton entry |> Program.cg_reachables_of program in
    Program.slice_procs_except program targets
  in
  match Config.npex_test_method with
  | Some test_pname ->
      let sink_proc = NullPoint.get_procname nullpoint in
      let main_procs =
        Procname.Set.filter (String.equal test_pname <<< Procname.get_method) (Program.all_procs program)
        |> Procname.Set.filter (fun proc ->
               Procname.Set.mem sink_proc (Procname.Set.singleton proc |> Program.cg_reachables_of program))
      in
      let entry =
        single_caller program sink_proc
        (* if Procname.Set.is_empty main_procs then single_caller program sink_proc
           else Procname.Set.choose main_procs *)
      in
      L.progress " - test-main : %a@." Procname.pp entry ;
      slice_by_entry program entry ;
      (* HEURISTICS: localize upto single-caller of entry in sliced-callgraph *)
      (* let entry = single_caller program sink_proc in
         L.progress " - found entry : %a@." Procname.pp entry ;
         Program.add_entry program entry ;
         slice_by_entry program entry ; *)
      Program.print_callgraph program "sliced_callgraph.dot" ;
      Procname.Set.singleton entry |> Program.cg_reachables_of program
  | None ->
      L.(die ExternalError) "test method name is not given" *)

let result_to_json ~time ~target_procs ~executed_procs =
  let proc_json = `List (List.filter_map (Procname.Set.elements executed_procs) ~f:proc_to_json_opt) in
  let target_json = `List (List.filter_map (Procname.Set.elements target_procs) ~f:proc_to_json_opt) in
  let time_json = `Float (Float.of_int time /. 1000.0) in
  let json = `Assoc [("targets", target_json); ("procs", proc_json); ("time", time_json)] in
  Utils.with_file_out Config.npex_localizer_result ~f:(fun oc -> Yojson.Basic.to_channel oc json)


let filter_faults program faults =
  let traces = parse_trace_nodes program in
  Faults.filter
    (fun {location} ->
      let proc = InstrNode.get_proc_name location in
      let trace_nodes =
        if not (List.is_empty traces) then List.filter traces ~f:(Procname.equal proc <<< InterNode.get_proc_name)
        else [NullPoint.get_nullpoint_list program |> List.hd_exn |> NullPoint.get_node]
      in
      let reachable_nodes =
        List.filter trace_nodes ~f:(Program.is_reachable program (InstrNode.inode_of location))
      in
      (* L.progress "check %a reachables to one of %a@." (Pp.seq InterNode.pp) trace_nodes InstrNode.pp location ; *)
      L.progress "%a is reachable from %a@." (Pp.seq InterNode.pp) reachable_nodes InstrNode.pp location ;
      List.exists trace_nodes ~f:(Program.is_reachable program (InstrNode.inode_of location)))
    faults


let remove_irrelevant_procs_from_db program relevant_procs =
  let db = ResultsDatabase.get_database () in
  let irrelevant_procs = Procname.Set.diff (Program.all_procs program) relevant_procs in
  let proc_uids =
    Procname.Set.fold (fun procname acc -> Procname.to_unique_id procname :: acc) irrelevant_procs []
  in
  let irrelevant_source_files =
    let all_sources = SourceFiles.get_all () ~filter:(fun _ -> true) |> SourceFile.Set.of_list in
    let relevant_sources =
      Procname.Set.fold
        (fun procname acc ->
          match Procdesc.load procname with
          | Some pdesc ->
              SourceFile.Set.add Location.((pdesc |> Procdesc.get_loc).file) acc
          | _ ->
              acc)
        relevant_procs SourceFile.Set.empty
    in
    SourceFile.Set.diff all_sources relevant_sources
  in
  List.iter proc_uids ~f:(fun uid ->
      SqliteUtils.exec db ~log:"remove uid from ..."
        ~stmt:(Printf.sprintf {| DELETE FROM procedures WHERE proc_uid = "%s" |} uid)) ;
  SourceFile.Set.iter
    (fun source_file ->
      SqliteUtils.exec db ~log:"remove source_file from ..."
        ~stmt:
          (Printf.sprintf {| DELETE FROM source_files WHERE source_file = "%s" |}
             (SourceFile.SQLite.serialize source_file |> Sqlite3.Data.to_string_exn)))
    irrelevant_source_files ;
  SqliteUtils.exec db ~log:"drop specs" ~stmt:{| DROP TABLE specs |} ;
  SqliteUtils.exec db ~log:"Vacuum" ~stmt:"VACUUM"


let localize ~get_summary ~time program trace_procs =
  let nullpoint = NullPoint.get_nullpoint_list program |> List.hd_exn in
  let npe_fault =
    let node = NullPoint.(nullpoint.node) in
    let instr = NullPoint.(nullpoint.instr) in
    let nullexp = NullPoint.(nullpoint.null_access_expr) in
    Fault.{location= InstrNode.of_pnode (InterNode.pnode_of node) instr; nullexp; fault_type= NullDeref}
  in
  let trace_procs = Procname.Set.add (NullPoint.get_procname nullpoint) (Procname.Set.of_list trace_procs) in
  let executed_procs =
    Procname.Set.fold
      (fun proc ->
        let executed_procs = snd (get_summary proc) in
        ExecutedProcs.fold Procname.Set.add executed_procs)
      trace_procs Procname.Set.empty
  in
  L.progress "trace procs: %a@. Executed procs: %a@." Procname.Set.pp trace_procs Procname.Set.pp executed_procs ;
  let faults =
    Procname.Set.fold (Faults.union <<< fst <<< get_summary) trace_procs (Faults.singleton npe_fault)
    |> filter_faults program
  in
  L.progress "@.Faults: %a@." Faults.pp faults ;
  let executed_procs =
    if Procname.Set.is_empty executed_procs then Program.cg_reachables_of program trace_procs else executed_procs
  in
  result_to_json ~time ~target_procs:executed_procs ~executed_procs ;
  remove_irrelevant_procs_from_db program executed_procs ;
  generate_npe_list faults
