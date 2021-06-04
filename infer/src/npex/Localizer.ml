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

let check_instr proc_desc analysis_data pre null_values node instr : SpecCheckerDomain.t list * Fault.t option =
  let location = InstrNode.of_pnode node instr in
  let open SpecCheckerDomain in
  let post =
    List.concat_map pre ~f:(fun astate ->
        let post = SpecChecker.DisjReady.exec_instr astate analysis_data node instr in
        (* L.progress "@.=====Pre state at %a ======@." (Sil.pp_instr ~print_types:true Pp.text) instr ;
           L.progress "%a" SpecCheckerDomain.pp astate ;
           L.progress "@.=====Post state at %a ======@." (Sil.pp_instr ~print_types:true Pp.text) instr ;
           L.progress "%a" (Pp.seq SpecCheckerDomain.pp) post ;
           L.progress "@.===========================@." ; *)
        post)
  in
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
    let is_target value = List.mem (Val.Set.elements null_values) value ~equal:phys_equal in
    List.exists post ~f:(fun astate ->
        try
          let value = eval astate ~pos node instr exp in
          is_target value && is_nullable value astate
        with _ -> (* Some exceptional states may fail to evaluate expression *) false)
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
    | Sil.Call (_, _, arg_typs, _, _) ->
        List.find_mapi arg_typs ~f:(fun pos (arg_exp, _) -> check_exp arg_exp ~pos)
    | Sil.Store {e2} ->
        check_exp e2 ~pos:0
    | _ ->
        None
  in
  (post, fault_opt)


let check_node proc_desc analysis_data pre nullvalues node =
  let _, faults =
    Instrs.fold (CFG.instrs node) ~init:(pre, Faults.empty) ~f:(fun (states, faults) instr ->
        let new_states, new_faults = check_instr proc_desc analysis_data states nullvalues node instr in
        match new_faults with Some fault -> (new_states, Faults.add fault faults) | _ -> (new_states, faults))
  in
  faults


let checker ({InterproceduralAnalysis.proc_desc} as interproc) : Summary.t option =
  (* let proc_name = Procdesc.get_proc_name proc_desc in *)
  let cfg = CFG.from_pdesc proc_desc in
  let analysis_data =
    SpecChecker.DisjReady.analysis_data (InterproceduralAnalysis.bind_payload interproc ~f:snd)
  in
  let inv_map = SpecChecker.cached_compute_invariant_map analysis_data in
  let specchecker_summaries =
    SpecChecker.compute_summary proc_desc cfg inv_map |> SpecCheckerSummary.get_local_disjuncts
  in
  let nullvalues =
    List.fold specchecker_summaries ~init:Val.Set.empty ~f:(fun acc astate ->
        Val.Set.union acc (SpecCheckerDomain.get_nullptrs astate))
  in
  if Config.debug_level_analysis > 0 && not (Val.Set.is_empty nullvalues) then
    L.progress " - find null value assigns@.   - null_values: %a@.   - method: %a@." Val.Set.pp nullvalues
      Procname.pp (Procdesc.get_proc_name proc_desc) ;
  let faults =
    CFG.fold_nodes cfg ~init:Faults.empty ~f:(fun faults node ->
        match SpecChecker.Analyzer.extract_state (CFG.Node.id node) inv_map with
        | Some {pre} ->
            Faults.union (check_node proc_desc analysis_data pre nullvalues node) faults
        | None ->
            faults)
  in
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
    List.fold specchecker_summaries ~init:ExecutedProcs.empty ~f:(fun acc astate ->
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


let target_procs program nullpoint =
  let rec single_caller program proc =
    match Program.callers_of_proc program proc with [pred] -> single_caller program pred | _ -> proc
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
      let entry = if Procname.Set.is_empty main_procs then sink_proc else Procname.Set.choose main_procs in
      L.progress " - test-main : %a@." Procname.pp entry ;
      slice_by_entry program entry ;
      (* HEURISTICS: localize upto single-caller of entry in sliced-callgraph *)
      let entry = single_caller program sink_proc in
      L.progress " - found entry : %a@." Procname.pp entry ;
      Program.add_entry program entry ;
      slice_by_entry program entry ;
      Program.print_callgraph program "sliced_callgraph.dot" ;
      Procname.Set.singleton entry |> Program.cg_reachables_of program
  | None ->
      L.(die ExternalError) "test method name is not given"


let result_to_json ~time ~target_procs ~executed_procs =
  let proc_json = `List (List.filter_map (ExecutedProcs.elements executed_procs) ~f:proc_to_json_opt) in
  let target_json = `List (List.filter_map (Procname.Set.elements target_procs) ~f:proc_to_json_opt) in
  let time_json = `Float (Float.of_int time /. 1000.0) in
  let json = `Assoc [("targets", target_json); ("procs", proc_json); ("time", time_json)] in
  Utils.write_json_to_file Config.npex_localizer_result json


let localize ~get_summary ~time program =
  let nullpoint = NullPoint.get_nullpoint_list program |> List.hd_exn in
  let target_procs = target_procs program nullpoint in
  let faults = Procname.Set.fold (Faults.union <<< fst <<< get_summary) target_procs Faults.empty in
  let executed_procs =
    Procname.Set.fold (ExecutedProcs.union <<< snd <<< get_summary) target_procs ExecutedProcs.empty
  in
  L.progress "@.Faults: %a@." Faults.pp faults ;
  result_to_json ~time ~target_procs ~executed_procs ;
  generate_npe_list faults
