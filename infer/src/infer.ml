(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

(** Top-level driver that orchestrates build system integration, frontends, backend, and reporting *)

module CLOpt = CommandLineOption
module L = Logging

let run driver_mode =
  let open Driver in
  run_prologue driver_mode ;
  let changed_files = read_config_changed_files () in
  InferAnalyze.invalidate_changed_procedures changed_files ;
  capture driver_mode ~changed_files ;
  analyze_and_report driver_mode ~changed_files ;
  run_epilogue ()


let run driver_mode = ScubaLogging.execute_with_time_logging "run" (fun () -> run driver_mode)

let setup () =
  let db_start =
    let already_started = ref false in
    fun () ->
      if (not !already_started) && CLOpt.is_originator && DBWriter.use_daemon then (
        DBWriter.start () ;
        Epilogues.register ~f:DBWriter.stop ~description:"Stop Sqlite write daemon" ;
        already_started := true )
  in
  ( match Config.command with
  | Analyze ->
      ResultsDir.assert_results_dir "have you run capture before?"
  | Report | ReportDiff ->
      ResultsDir.create_results_dir ()
  | Capture | Compile | Run ->
      let driver_mode = Lazy.force Driver.mode_from_command_line in
      if
        Config.(
          (* In Buck mode, delete infer-out directories inside buck-out to start fresh and to
             avoid getting errors because some of their contents is missing (removed by
             [Driver.clean_results_dir ()]). *)
          (buck && Option.exists buck_mode ~f:BuckMode.is_clang_flavors) || genrule_mode)
        || not
             ( Driver.is_analyze_mode driver_mode
             || Config.(
                  continue_capture || infer_is_clang || infer_is_javac || reactive_mode
                  || incremental_analysis) )
      then ResultsDir.remove_results_dir () ;
      ResultsDir.create_results_dir () ;
      if
        CLOpt.is_originator && (not Config.continue_capture)
        && not (Driver.is_analyze_mode driver_mode)
      then (
        db_start () ;
        SourceFiles.mark_all_stale () )
  | Explore ->
      ResultsDir.assert_results_dir "please run an infer analysis first"
  | Debug ->
      ResultsDir.assert_results_dir "please run an infer analysis or capture first"
  | NPEX ->
      ( match Sys.is_directory Config.npex_summary_dir with
      | `Yes when Config.npex_launch_spec_inference ->
          Utils.rmtree Config.npex_summary_dir ;
          Utils.create_dir Config.npex_summary_dir
      | `Yes when Config.npex_launch_spec_verifier ->
          ()
      | `Yes ->
          ()
      | `No ->
          Utils.rmtree Config.npex_summary_dir ;
          Utils.create_dir Config.npex_summary_dir
      | `Unknown ->
          Utils.create_dir Config.npex_summary_dir ) ;
      ( match Sys.is_directory Config.npex_result_dir with
      | `Yes when Config.npex_launch_spec_inference ->
          Utils.rmtree Config.npex_result_dir ;
          Utils.create_dir Config.npex_result_dir
      | `Yes when Config.npex_launch_spec_verifier ->
          ()
      | `Yes ->
          ()
      | `No ->
          Utils.rmtree Config.npex_result_dir ;
          Utils.create_dir Config.npex_result_dir
      | `Unknown ->
          Utils.create_dir Config.npex_result_dir ) ;
      ResultsDir.assert_results_dir "please run an infer analysis or capture first"
  | Help ->
      () ) ;
  let has_result_dir =
    match Config.command with
    | Analyze | Capture | Compile | Debug | Explore | Report | ReportDiff | Run | NPEX ->
        true
    | Help ->
        false
  in
  if has_result_dir then (
    db_start () ;
    if CLOpt.is_originator then ResultsDir.RunState.add_run_to_sequence () ) ;
  has_result_dir


let print_active_checkers () =
  (if Config.print_active_checkers && CLOpt.is_originator then L.result else L.environment_info)
    "Active checkers: %a@."
    (Pp.seq ~sep:", " RegisterCheckers.pp_checker)
    (RegisterCheckers.get_active_checkers ())


let print_scheduler () =
  L.environment_info "Scheduler: %s@\n"
    ( match Config.scheduler with
    | File ->
        "file"
    | Restart ->
        "restart"
    | SyntacticCallGraph ->
        "callgraph" )


let print_cores_used () = L.environment_info "Cores used: %d@\n" Config.jobs

let log_environment_info () =
  L.environment_info "CWD = %s@\n" (Sys.getcwd ()) ;
  ( match Config.inferconfig_file with
  | Some file ->
      L.environment_info "Read configuration in %s@\n" file
  | None ->
      L.environment_info "No .inferconfig file found@\n" ) ;
  L.environment_info "Project root = %s@\n" Config.project_root ;
  let infer_args =
    Sys.getenv CLOpt.args_env_var
    |> Option.map ~f:(String.split ~on:CLOpt.env_var_sep)
    |> Option.value ~default:["<not set>"]
  in
  L.environment_info "INFER_ARGS = %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    infer_args ;
  L.environment_info "command line arguments: %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    (Array.to_list Sys.(get_argv ())) ;
  ( match Utils.get_available_memory_MB () with
  | None ->
      L.environment_info "Could not retrieve available memory (possibly not on Linux)@\n"
  | Some available_memory ->
      L.environment_info "Available memory at startup: %d MB@\n" available_memory ;
      ScubaLogging.log_count ~label:"startup_mem_avail_MB" ~value:available_memory ) ;
  print_active_checkers () ;
  print_scheduler () ;
  print_cores_used ()


let () =
  (* We specifically want to collect samples only from the main process until
     we figure out what other entries and how we want to collect *)
  if CommandLineOption.is_originator then ScubaLogging.register_global_log_flushing_at_exit () ;
  ( if Config.linters_validate_syntax_only then
    match CTLParserHelper.validate_al_files () with
    | Ok () ->
        L.exit 0
    | Error e ->
        print_endline e ;
        L.exit 3 ) ;
  ( match Config.check_version with
  | Some check_version ->
      if not (String.equal check_version Version.versionString) then
        L.(die UserError)
          "Provided version '%s' does not match actual version '%s'" check_version
          Version.versionString
  | None ->
      () ) ;
  if Config.print_builtins then Builtin.print_and_exit () ;
  let has_results_dir = setup () in
  if has_results_dir then log_environment_info () ;
  if has_results_dir && Config.debug_mode && CLOpt.is_originator then (
    L.progress "Logs in %s@." (ResultsDir.get_path Logs) ;
    Option.iter Config.scuba_execution_id ~f:(fun id -> L.progress "Execution ID %Ld@." id) ) ;
  ( match Config.command with
  | _ when Config.test_determinator && not Config.process_clang_ast ->
      TestDeterminator.compute_and_emit_test_to_run ()
  | _ when Option.is_some Config.java_debug_source_file_info ->
      JSourceFileInfo.debug_on_file (Option.value_exn Config.java_debug_source_file_info)
  | Analyze ->
      run Driver.Analyze
  | Capture | Compile | Run ->
      run (Lazy.force Driver.mode_from_command_line)
  | Help ->
      if
        Config.(
          list_checkers || list_issue_types || Option.is_some write_website
          || (not (List.is_empty help_checker))
          || not (List.is_empty help_issue_type))
      then (
        if Config.list_checkers then Help.list_checkers () ;
        if Config.list_issue_types then Help.list_issue_types () ;
        if not (List.is_empty Config.help_checker) then Help.show_checkers Config.help_checker ;
        if not (List.is_empty Config.help_issue_type) then
          Help.show_issue_types Config.help_issue_type ;
        Option.iter Config.write_website ~f:(fun website_root -> Help.write_website ~website_root) ;
        () )
      else
        L.result
          "To see Infer's manual, run `infer --help`.@\n\
           To see help about the \"help\" command itself, run `infer help --help`.@\n"
  | Report -> (
      let write_from_json out_path =
        IssuesTest.write_from_json ~json_path:Config.from_json_report ~out_path
          Config.issues_tests_fields
      in
      let write_from_cost_json out_path =
        CostIssuesTest.write_from_json ~json_path:Config.from_json_costs_report ~out_path
          CostIssuesTestField.all_fields
      in
      match (Config.issues_tests, Config.cost_issues_tests) with
      | None, None ->
          if not Config.quiet then L.result "%t" Summary.OnDisk.pp_specs_from_config
      | Some out_path, Some cost_out_path ->
          write_from_json out_path ;
          write_from_cost_json cost_out_path
      | None, Some cost_out_path ->
          write_from_cost_json cost_out_path
      | Some out_path, None ->
          write_from_json out_path )
  | ReportDiff ->
      (* at least one report must be passed in input to compute differential *)
      ( match Config.(report_current, report_previous, costs_current, costs_previous) with
      | None, None, None, None ->
          L.die UserError
            "Expected at least one argument among '--report-current', '--report-previous', \
             '--costs-current', and '--costs-previous'"
      | _ ->
          () ) ;
      ReportDiff.reportdiff ~current_report:Config.report_current
        ~previous_report:Config.report_previous ~current_costs:Config.costs_current
        ~previous_costs:Config.costs_previous
  | Debug when not Config.(global_tenv || procedures || source_files) ->
      L.die UserError
        "Expected at least one of '--procedures', '--source_files', or '--global-tenv'"
  | Debug ->
      ( if Config.global_tenv then
        match Tenv.load_global () with
        | None ->
            L.result "No global type environment was found.@."
        | Some tenv ->
            L.result "Global type environment:@\n@[<v>%a@]" Tenv.pp tenv ) ;
      ( if Config.procedures then
        let filter = Lazy.force Filtering.procedures_filter in
        if Config.procedures_summary then
          let pp_summary fmt proc_name =
            match Summary.OnDisk.get proc_name with
            | None ->
                Format.fprintf fmt "No summary found: %a@\n" Procname.pp proc_name
            | Some summary ->
                Summary.pp_text fmt summary
          in
          Option.iter (Procedures.select_proc_names_interactive ~filter) ~f:(fun proc_names ->
              L.result "%a" (fun fmt () -> List.iter proc_names ~f:(pp_summary fmt)) ())
        else
          L.result "%a"
            Config.(
              Procedures.pp_all ~filter ~proc_name:procedures_name ~attr_kind:procedures_definedness
                ~source_file:procedures_source_file ~proc_attributes:procedures_attributes
                ~proc_cfg:procedures_cfg)
            () ) ;
      if Config.source_files then (
        let filter = Lazy.force Filtering.source_files_filter in
        L.result "%a"
          (SourceFiles.pp_all ~filter ~type_environment:Config.source_files_type_environment
             ~procedure_names:Config.source_files_procedure_names
             ~freshly_captured:Config.source_files_freshly_captured)
          () ;
        if Config.source_files_cfg then (
          let source_files = SourceFiles.get_all ~filter () in
          List.iter source_files ~f:(fun source_file ->
              (* create directory in captured/ *)
              DB.Results_dir.init ~debug:true source_file ;
              (* collect the CFGs for all the procedures in [source_file] *)
              let proc_names = SourceFiles.proc_names_of_source source_file in
              let cfgs = Procname.Hash.create (List.length proc_names) in
              List.iter proc_names ~f:(fun proc_name ->
                  Procdesc.load proc_name
                  |> Option.iter ~f:(fun cfg -> Procname.Hash.add cfgs proc_name cfg)) ;
              (* emit the dot file in captured/... *)
              DotCfg.emit_frontend_cfg source_file cfgs) ;
          L.result "CFGs written in %s/*/%s@." (ResultsDir.get_path Debug)
            Config.dotty_frontend_output ) )
  | Explore ->
      if (* explore bug traces *)
         Config.html then
        TraceBugs.gen_html_report ~report_json:(ResultsDir.get_path ReportJson)
          ~show_source_context:Config.source_preview ~max_nested_level:Config.max_nesting
          ~report_html_dir:(ResultsDir.get_path ReportHtml)
      else
        TraceBugs.explore ~selector_limit:None ~report_json:(ResultsDir.get_path ReportJson)
          ~report_txt:(ResultsDir.get_path ReportText) ~selected:Config.select
          ~show_source_context:Config.source_preview ~max_nested_level:Config.max_nesting
  | NPEX ->
      if Config.npex_launch_spec_verifier || Config.npex_launch_spec_inference then
        Program.prepare_incremental_db () ;
      let program = Program.from_marshal () in
      let is_capture_failed program =
        NullPoint.get_nullpoint_list program |> List.map ~f:NullPoint.get_procname |> List.is_empty
      in
      if Config.npex_launch_spec_verifier then
        ignore (Patch.create program ~patch_json_path:Config.npex_patch_json_name)
      else if (not Config.npex_launch_spec_verifier) && is_capture_failed program then (
        L.progress "FAILED TO COMPILE: @." ;
        L.exit 1 ) ;
      let get_summary proc_name =
        match Summary.OnDisk.get proc_name with
        | Some {payloads= {spec_checker= Some spec_checker_summary}} ->
            spec_checker_summary
        | _ ->
            L.(die ExternalError)
              "%a has not been analyzed during verification" Procname.pp proc_name
      in
      let serializer = Serialization.create_serializer Serialization.Key.summary in
      let get_original_summary proc_name =
        let original_summary_path =
          Procname.to_filename proc_name ^ ".specs"
          |> Filename.concat Config.npex_summary_dir
          |> DB.filename_from_string
        in
        match Serialization.read_from_file serializer original_summary_path with
        | Some Summary.{payloads= {spec_checker= Some spec_checker_summary}} ->
            spec_checker_summary
        | _ ->
            L.(die ExternalError) "%a has not been analyzed during inference" Procname.pp proc_name
      in
      ResultsDir.assert_results_dir "have you run capture before?" ;
      if Config.npex_launch_localize then (
        assert (Int.equal (List.length Config.error_report_json) 1) ;
        L.progress "launch fault localization@." ;
        let program = Program.from_marshal () in
        let target_procs = Localizer.parse_trace program in
        Program.to_marshal Program.marshalled_path program ;
        let nullpoints = NullPoint.get_nullpoint_list ~debug:true program in
        L.progress "NullPoint : %a@." (Pp.seq NullPoint.pp) nullpoints ;
        let get_summary proc_name =
          match Summary.OnDisk.get proc_name with
          | Some {payloads= {spec_checker_localizer= Some summary}} ->
              summary
          | _ ->
              L.(die ExternalError)
                "%a has not been analyzed during verification" Procname.pp proc_name
        in
        let _, time = Utils.timeit ~f:(fun () -> InferAnalyze.main ~changed_files:None) in
        Localizer.localize ~get_summary ~time program target_procs )
      else if Config.npex_launch_spec_inference then (
        L.progress "launch spec inference@." ;
        let program = Program.from_marshal () in
        (* OPTIMIZATION *)
        if not Config.npex_manual_model then ignore (NullModel.LocFieldMValueMap.from_marshal ()) ;
        let nullpoints = NullPoint.get_nullpoint_list program in
        L.progress "NullPoint : %a@." (Pp.seq NullPoint.pp) nullpoints ;
        InferAnalyze.main ~changed_files:None ;
        let target_procs =
          List.fold nullpoints ~init:Procname.Set.empty ~f:(fun acc NullPoint.{node} ->
              Procname.Set.add (InterNode.get_proc_name node) acc)
          |> Procname.Set.elements
        in
        let is_analyzed =
          List.fold ~init:false target_procs ~f:(fun acc proc ->
              let disjuncts = SpecCheckerSummary.get_local_disjuncts (get_summary proc) in
              Vocab.print_to_file
                ~msg:(Format.asprintf "%a" SpecVeri.pp_states disjuncts)
                ~filename:
                  (Format.asprintf "%s/inferenced_all_states_%a" Config.npex_result_dir Procname.pp
                     proc) ;
              match SpecVeri.get_feasible_disjuncts_opt disjuncts with
              | Some normal_and_infered ->
                  Vocab.print_to_file
                    ~msg:(Format.asprintf "%a" SpecVeri.pp_normal_and_infered normal_and_infered)
                    ~filename:
                      (Format.asprintf "%s/inferenced_max_states_%a" Config.npex_result_dir
                         Procname.pp proc) ;
                  true
              | None ->
                  acc)
        in
        if is_analyzed then L.exit 0
        else (
          L.progress "[FAIL]: to analyze find meaninigful specification with the given model@." ;
          L.exit 1 ) )
      else if Config.npex_launch_spec_verifier then (
        InferAnalyze.main ~changed_files:None ;
        let _, time =
          Utils.timeit ~f:(fun () -> SpecVeri.launch ~get_summary ~get_original_summary)
        in
        L.progress "%d ms elapsed to verify specification@." time ) ) ;
  (* to make sure the exitcode=0 case is logged, explicitly invoke exit *)
  L.exit 0
