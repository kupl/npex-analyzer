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
module Summary = Faults

let check_instr proc_desc astates null_values node instr : Fault.t option =
  let location = InstrNode.of_pnode node instr in
  let open SpecCheckerDomain in
  (* try *)
  let is_target_null_exp exp ~pos =
    let is_nullable value astate =
      L.progress "check inequal_values: %a@." (Pp.seq Val.pp) (inequal_values astate value) ;
      not (List.mem (inequal_values astate value) Val.default_null ~equal:Val.equal)
    in
    let is_target value = Val.Set.mem value null_values in
    List.exists astates ~f:(fun astate ->
        let value = eval astate ~pos node instr exp in
        is_target value && is_nullable value astate)
  in
  let check_exp exp ~pos =
    if is_target_null_exp exp ~pos then (
      match AccessExpr.from_IR_exp_opt proc_desc exp with
      | Some nullexp when AccessExpr.equal nullexp AccessExpr.null ->
          Some Fault.{location; nullexp; fault_type= NullConst}
      | Some nullexp ->
          Some Fault.{location; nullexp; fault_type= NullAssign}
      | None ->
          L.progress "Failed to convert null-exp %a to access expression at %a" Exp.pp exp InstrNode.pp location ;
          None )
    else None
  in
  match instr with
  | Sil.Call (_, _, arg_typs, _, _) ->
      List.find_mapi arg_typs ~f:(fun pos (arg_exp, _) -> check_exp arg_exp ~pos)
  | Sil.Store {e2} ->
      check_exp e2 ~pos:0
  | _ ->
      None


(* with _ -> L.(die InternalError) "@.Invalid State:@.%a@." (Pp.seq pp) astates *)

let check_node proc_desc post nullvalues node =
  Instrs.fold (CFG.instrs node) ~init:Faults.empty ~f:(fun faults instr ->
      match check_instr proc_desc post nullvalues node instr with
      | Some fault ->
          Faults.add fault faults
      | _ ->
          faults)


let checker ({InterproceduralAnalysis.proc_desc} as interproc) =
  (* let proc_name = Procdesc.get_proc_name proc_desc in *)
  let cfg = CFG.from_pdesc proc_desc in
  let analysis_data =
    SpecChecker.DisjReady.analysis_data (InterproceduralAnalysis.bind_payload interproc ~f:snd)
  in
  let inv_map = SpecChecker.cached_compute_invariant_map analysis_data in
  let nullvalues =
    SpecChecker.compute_summary proc_desc cfg inv_map
    |> SpecCheckerSummary.get_local_disjuncts
    |> List.fold ~init:Val.Set.empty ~f:(fun acc astate ->
           Val.Set.union acc (SpecCheckerDomain.get_nullptrs astate))
  in
  let faults =
    CFG.fold_nodes cfg ~init:Faults.empty ~f:(fun faults node ->
        match SpecChecker.Analyzer.extract_state (CFG.Node.id node) inv_map with
        | Some {post} ->
            let non_exceptionals = List.filter post ~f:(not <<< SpecCheckerDomain.is_exceptional) in
            Faults.union (check_node proc_desc non_exceptionals nullvalues node) faults
        | None ->
            faults)
  in
  let param_faults =
    Val.Set.fold
      (fun v acc ->
        match v with
        | Val.Vheap (SymDom.SymHeap.Symbol s) | Val.Vint (SymDom.SymExp.Symbol s) ->
            let nullexp = SymDom.Symbol.to_ap s in
            let location = InstrNode.of_pnode (Procdesc.get_start_node proc_desc) Sil.skip_instr in
            Faults.add Fault.{location; nullexp; fault_type= Parameter} acc
        | _ ->
            acc)
      nullvalues Faults.empty
  in
  Some (Faults.union faults param_faults)


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
  match Config.npex_test_method with
  | Some test_pname ->
      let sink_proc = NullPoint.get_procname nullpoint in
      let main_procs =
        Procname.Set.filter (String.equal test_pname <<< Procname.get_method) (Program.all_procs program)
        |> Procname.Set.filter (fun proc ->
               Procname.Set.mem sink_proc (Procname.Set.singleton proc |> Program.cg_reachables_of program))
      in
      let entry =
        if Procname.Set.is_empty main_procs then
          let rec single_caller proc =
            match Program.callers_of_proc program proc with [pred] -> single_caller pred | _ -> proc
          in
          single_caller sink_proc
        else Procname.Set.choose main_procs
      in
      L.progress "Found entry : %a@." Procname.pp entry ;
      Program.add_entry program entry ;
      Procname.Set.singleton entry |> Program.cg_reachables_of program
  | None ->
      L.(die ExternalError) "test method name is not given"


let localize ~get_summary program =
  let nullpoint = NullPoint.get_nullpoint_list program |> List.hd_exn in
  let target_procs = target_procs program nullpoint in
  let faults = Procname.Set.fold (Faults.union <<< get_summary) target_procs Faults.empty in
  L.progress "@.Faults: %a@." Faults.pp faults ;
  generate_npe_list faults
