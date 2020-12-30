open! IStd
open! Vocab

type info = Call of string | Entry | Sink | Normal

type t = (Location.t * info) list

let is_entry_info = function Entry -> true | _ -> false

let info_of_string tag description =
  match tag with "CALLSITE" -> Call description | "ENTRY" -> Entry | _ -> Normal


let to_string_info = function
  | Call callee ->
      F.asprintf "Call %s" callee
  | Entry ->
      "Entry"
  | Sink ->
      "Sink"
  | Normal ->
      "Normal"


let pp_loc_info fmt (loc, info) = F.fprintf fmt "(%a, %s)" Location.pp_file_pos loc (to_string_info info)

let pp fmt trace = if Config.debug_mode then F.fprintf fmt "%a" (Pp.seq ~sep:"\n" pp_loc_info) trace

let loc_from_json_opt files json =
  try
    let open Yojson.Basic.Util in
    let line = json |> member "line_number" |> to_int in
    let file =
      ( match json |> member "filename" |> to_string_option with
      | None ->
          json |> member "filepath" |> to_string
      | Some filepath ->
          filepath )
      |> source_file_from_string files
    in
    Some Location.{line; file; col= -1}
  with _ -> None


let from_alarm_report filepath : t =
  let open Yojson.Basic.Util in
  (* Use only first report *)
  let json = read_json_file_exn filepath |> to_list |> List.hd_exn in
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let trace =
    let bug_trace = json |> member "bug_trace" |> to_list in
    List.filter_mapi bug_trace ~f:(fun i json' ->
        match loc_from_json_opt source_files json' with
        | Some location ->
            let info : info =
              let description = json' |> member "description" |> to_string in
              if String.is_prefix description ~prefix:"start of procedure" then Entry
              else
                match List.nth bug_trace (i + 1) with
                | Some json_next ->
                    let description_next = json_next |> member "description" |> to_string in
                    if String.is_prefix description_next ~prefix:"start of procedure" then
                      let method_expression =
                        String.chop_prefix_exn description_next ~prefix:"start of procedure "
                      in
                      Call (String.split method_expression ~on:'(' |> List.hd_exn)
                    else Normal
                | None ->
                    Sink
            in
            Some (location, info)
        | None ->
            None)
  in
  trace


let from_report filepath : t =
  let json = read_json_file_exn filepath in
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let open Yojson.Basic.Util in
  let trace =
    json
    |> to_list
    |> List.filter_map ~f:(fun json' ->
           match loc_from_json_opt source_files json' with
           | Some location ->
               let tag_str = json' |> member "tag" |> to_string in
               let desc_str = json' |> member "description" |> to_string in
               let info = info_of_string tag_str desc_str in
               Some (location, info)
           | None ->
               None)
  in
  trace
