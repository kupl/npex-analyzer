(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd

(** Entries in the results directory (infer-out/). Unless you want to specify a custom results
    directory you probably want to use {!ResultsDir.Entry} instead of this module. *)

type id =
  | CaptureDB  (** the capture database *)
  | CaptureDependencies  (** list of infer-out/ directories that contain capture artefacts *)
  | ChangedFunctions  (** results of the clang test determinator *)
  | Debug  (** directory containing debug data *)
  | Differential  (** contains the results of [infer reportdiff] *)
  | DuplicateFunctions  (** list of duplicated functions *)
  | JavaClassnamesCache  (** used when capturing Java jar dependencies *)
  | JavaGlobalTypeEnvironment  (** internal {!Tenv.t} object corresponding to the whole project *)
  | LintDotty  (** directory of linters' dotty debug output for CTL evaluation *)
  | LintIssues  (** directory of linters' issues *)
  | Logs  (** log file *)
  | NullsafeFileIssues  (** file-wide issues of the nullsafe analysis *)
  | PerfEvents  (** file containing events for performance profiling *)
  | ProcnamesLocks
      (** directory of per-{!Procname.t} file locks, used by the analysis scheduler in certain modes *)
  | RacerDIssues  (** directory of issues reported by the RacerD analysis *)
  | ReportCostsJson  (** reports of the costs analysis *)
  | ReportHtml  (** directory of the HTML report *)
  | ReportJson  (** the main product of the analysis: [report.json] *)
  | ReportText  (** a human-readable textual version of [report.json] *)
  | ReportXML  (** a PMD-style XML version of [report.json] *)
  | RetainCycles  (** directory of retain cycles dotty files *)
  | RunState  (** internal data about the last infer run *)
  | StarvationIssues  (** directory of issues reported by the starvation analysis *)
  | Temporary  (** directory containing temp files *)
  | TestDeterminatorReport  (** the report produced by the test determinator capture mode *)
  | TestDeterminatorTempResults  (** a directory *)

val get_path : results_dir:string -> id -> string
(** the absolute path for the given entry *)

val get_issues_directories : unit -> id list
(** all the entries that correspond to directories containing temporary issue logs for certain
    analyses *)

val to_delete_before_incremental_capture_and_analysis : results_dir:string -> string list
(** utility for {!ResultsDir.scrub_for_incremental}, you probably want to use that instead *)

val to_delete_before_caching_capture : results_dir:string -> string list
(** utility for {!ResultsDir.scrub_for_caching}, you probably want to use that instead *)

val buck_infer_deps_file_name : string
(** sad that we have to have this here but some code path is looking for all files with that name in
    buck-out/ *)
