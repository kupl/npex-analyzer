(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open PolyVariantEqual
module L = Logging

type t =
  | Invalid of {ml_source_file: string}
  | Absolute of string
  | RelativeProjectRoot of string  (** relative to project root *)
[@@deriving compare, equal]

module OrderedSourceFile = struct
  type nonrec t = t [@@deriving compare]
end

module Map = Caml.Map.Make (OrderedSourceFile)
module Set = Caml.Set.Make (OrderedSourceFile)

module Hash = Caml.Hashtbl.Make (struct
  type nonrec t = t

  let equal = equal

  let hash = Caml.Hashtbl.hash
end)

let from_abs_path ?(warn_on_error = true) fname =
  if Filename.is_relative fname then
    L.(die InternalError) "Path '%s' is relative, when absolute path was expected." fname ;
  (* try to get realpath of source file. Use original if it fails *)
  let fname_real = try Utils.realpath ~warn_on_error fname with Unix.Unix_error _ -> fname in
  let project_root_real = Utils.realpath ~warn_on_error Config.project_root in
  match
    Utils.filename_to_relative ~backtrack:Config.relative_path_backtrack ~root:project_root_real
      fname_real
  with
  | Some path ->
      RelativeProjectRoot path
  | None when Config.buck_cache_mode && Filename.check_suffix fname_real "java" ->
      L.(die InternalError) "%s is not relative to %s" fname_real project_root_real
  | None ->
      (* fname_real is absolute already *)
      Absolute fname_real


let to_string =
  let root = Utils.realpath Config.project_root in
  fun ?(force_relative = false) fname ->
    match fname with
    | Invalid {ml_source_file} ->
        "DUMMY from " ^ ml_source_file
    | RelativeProjectRoot path ->
        path
    | Absolute path ->
        if force_relative then
          let open IOption.Let_syntax in
          (let* isysroot_suffix = Config.xcode_isysroot_suffix in
           let+ pos = String.substr_index path ~pattern:isysroot_suffix in
           "${XCODE_ISYSROOT}" ^ String.subo ~pos:(pos + String.length isysroot_suffix) path)
          |> IOption.if_none_eval ~f:(fun () ->
                 Option.value_exn (Utils.filename_to_relative ~force_full_backtrack:true ~root path))
        else path


let has_extension t ~ext = String.is_suffix (to_string t) ~suffix:ext

let pp fmt fname = Format.pp_print_string fmt (to_string fname)

let to_abs_path fname =
  match fname with
  | Invalid {ml_source_file} ->
      L.(die InternalError)
        "cannot be called with Invalid source file originating in %s" ml_source_file
  | RelativeProjectRoot path ->
      Filename.concat Config.project_root path
  | Absolute path ->
      path


let to_rel_path fname = match fname with RelativeProjectRoot path -> path | _ -> to_abs_path fname

let invalid ml_source_file = Invalid {ml_source_file}

let is_invalid = function Invalid _ -> true | _ -> false

let is_under_project_root = function
  | Invalid {ml_source_file} ->
      L.(die InternalError) "cannot be called with Invalid source file from %s" ml_source_file
  | RelativeProjectRoot _ ->
      true
  | Absolute _ ->
      false


let exists_cache = String.Table.create ~size:256 ()

let path_exists abs_path =
  try String.Table.find_exn exists_cache abs_path
  with Not_found_s _ | Caml.Not_found ->
    let result = Sys.file_exists abs_path = `Yes in
    String.Table.set exists_cache ~key:abs_path ~data:result ;
    result


let of_header ?(warn_on_error = true) header_file =
  let abs_path = to_abs_path header_file in
  let source_exts = ["c"; "cc"; "cpp"; "cxx"; "m"; "mm"] in
  let header_exts = ["h"; "hh"; "hpp"; "hxx"] in
  match Filename.split_extension abs_path with
  | file_no_ext, Some ext when List.mem ~equal:String.equal header_exts ext ->
      List.find_map source_exts ~f:(fun ext ->
          let possible_file = file_no_ext ^ "." ^ ext in
          if path_exists possible_file then Some (from_abs_path ~warn_on_error possible_file)
          else None)
  | _ ->
      None


let create ?(warn_on_error = true) path =
  if Filename.is_relative path then
    (* sources in changed-files-index may be specified relative to project root *)
    RelativeProjectRoot path
  else from_abs_path ~warn_on_error path


let changed_sources_from_changed_files changed_files =
  List.fold changed_files ~init:Set.empty ~f:(fun changed_files_set line ->
      try
        let source_file = create line in
        let changed_files' = Set.add source_file changed_files_set in
        (* Add source corresponding to changed header if it exists *)
        match of_header source_file with
        | Some src ->
            Set.add src changed_files'
        | None ->
            changed_files'
      with _exn -> changed_files_set)


module SQLite = struct
  type nonrec t = t

  let invalid_tag = 'I'

  let absolute_tag = 'A'

  let relative_tag = 'R'

  let serialize sourcefile =
    let tag_text tag str = Sqlite3.Data.TEXT (Printf.sprintf "%c%s" tag str) in
    match sourcefile with
    | Invalid {ml_source_file} ->
        tag_text invalid_tag ml_source_file
    | Absolute abs_path ->
        tag_text absolute_tag abs_path
    | RelativeProjectRoot rel_path ->
        tag_text relative_tag rel_path


  let deserialize serialized_sourcefile =
    let[@warning "-8"] (Sqlite3.Data.TEXT text) = serialized_sourcefile in
    if String.is_empty text then
      L.die InternalError "Could not deserialize sourcefile with empty representation@." ;
    let tag = text.[0] in
    let str = String.sub ~pos:1 ~len:(String.length text - 1) text in
    if Char.equal tag invalid_tag then Invalid {ml_source_file= str}
    else if Char.equal tag absolute_tag then Absolute str
    else if Char.equal tag relative_tag then RelativeProjectRoot str
    else L.die InternalError "Could not deserialize sourcefile with tag=%c, str= %s@." tag str
end
