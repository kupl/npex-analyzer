open! IStd
module L = Logging
module F = Format

exception TODO of string

exception Unexpected of string

let ( <<< ) f g x = f (g x)

let is_ill_temp_var pv =
  let pv_string = Pvar.to_string pv in
  String.contains pv_string ~pos:0 '$'
  && (not (String.is_prefix pv_string ~prefix:"$bcvar"))
  && (not (String.is_prefix pv_string ~prefix:"$irvar"))
  && not (String.contains pv_string '_')


let is_catch_var pv = String.is_prefix (Pvar.to_string pv) ~prefix:"CatchVar"

let pp_instr = Sil.pp_instr ~print_types:true Pp.text

let[@warning "-33"] get_line node = Location.(Procdesc.Node.get_loc node).line

let id_func x = x

let is_main_func pname = String.equal "main" (Procname.get_method pname)

let is_call_instr = function Sil.Call _ -> true | _ -> false

let is_load_instr = function Sil.Load _ -> true | _ -> false

let is_store_instr = function Sil.Store _ -> true | _ -> false

let is_return_instr = function Sil.Store {e1= Lvar pv} when Pvar.is_return pv -> true | _ -> false

let is_prune_instr = function Sil.Prune _ -> true | _ -> false

let is_exn_instr = function Sil.Store {e2= Exp.Exn _} -> true | _ -> false

let is_equal_bo = function Binop.Eq | Binop.Ne -> true | _ -> false

let rec is_nullcheck_exp ~is_true prune_exp =
  match prune_exp with
  | Exp.UnOp (Unop.LNot, e, _) ->
      is_nullcheck_exp e ~is_true:(not is_true)
  | Exp.BinOp (Binop.Eq, e1, e2) when is_true ->
      Exp.is_null_literal e1 || Exp.is_null_literal e2
  | Exp.BinOp (Binop.Ne, e1, e2) when not is_true ->
      Exp.is_null_literal e1 || Exp.is_null_literal e2
  | Exp.Var _ ->
      (* v != null *)
      if is_true then false else true
  | _ ->
      false


let is_nullcheck_instr = function
  | Sil.Prune (bexp, _, _, _) ->
      is_nullcheck_exp ~is_true:true bexp || is_nullcheck_exp ~is_true:false bexp
  | _ ->
      false


let extract_load_exp_exn = function
  | Sil.Load {e} ->
      e
  | _ as instr ->
      L.(die InternalError)
        "extract_load_exp_exn is called from non-load instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        instr


let args_of_call_instr_exn = function
  | Sil.Call (_, _, args, _, _) ->
      args
  | _ ->
      L.(die InternalError) "non-call instr is given"


let node_has_same_loc_instr loc node =
  Instrs.exists ~f:(fun instr -> Location.equal loc (Sil.location_of_instr instr)) (Procdesc.Node.get_instrs node)


let get_node_loc_line node = (Procdesc.Node.get_loc node).Location.line

let get_first_instr_of_node node = Instrs.nth_exn (Procdesc.Node.get_instrs node) 0

let equal_node_inter n1 n2 =
  Procdesc.Node.equal n1 n2 && Procname.equal (Procdesc.Node.get_proc_name n1) (Procdesc.Node.get_proc_name n2)


let instr_get_exps instr =
  Sil.exps_of_instr instr @ match instr with Sil.Call (_, _, args, _, _) -> List.map args ~f:fst | _ -> []


let rec combinations ~k ~lst =
  if k <= 0 then [[]]
  else
    match lst with
    | [] ->
        []
    | h :: tl ->
        let with_h = List.map (combinations ~k:(k - 1) ~lst:tl) ~f:(fun l -> h :: l) in
        let without_h = combinations ~k ~lst:tl in
        with_h @ without_h


let equal_typ x y =
  let desc_x, desc_y = (x.Typ.desc, y.Typ.desc) in
  Typ.equal_desc desc_x desc_y


let bigand lst = List.for_all lst ~f:(fun x -> x)

let bigor lst = List.exists lst ~f:(fun x -> x)

let get_instrs = Procdesc.Node.get_instrs

let get_instrs_list n = Procdesc.Node.get_instrs n |> Instrs.get_underlying_not_reversed |> Array.to_list

let is_callnode node = Instrs.exists (Procdesc.Node.get_instrs node) ~f:is_call_instr

let is_retnode node =
  let has_retvar = function Exp.Lvar pv when Pvar.is_return pv -> true | _ -> false in
  Instrs.exists (Procdesc.Node.get_instrs node) ~f:(fun instr -> List.exists ~f:has_retvar (instr_get_exps instr))


(** Helpers for manipulating SIL instructions **)
let replace_call_exp_of fexp = function
  | Sil.Call (r, _, args, loc, cflags) ->
      Sil.Call (r, fexp, args, loc, cflags)
  | _ as inst ->
      L.(die InternalError)
        "replace_call_exp_of is applied to non-call-instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        inst


let fexp_from_string_c_fun fname = Exp.Const (Cfun (Procname.from_string_c_fun fname))

let call_instr_info_exn = function
  | Sil.Call ((id, typ), fexp, args, loc, cflags) ->
      ((id, typ), fexp, args, loc, cflags)
  | _ as inst ->
      L.(die InternalError)
        "call_instr_info_exn is applied to non-call-instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        inst


(** printers **)
open ANSITerminal

let step_style = [Bold; white]

let result_style = []

let progress_style = [Bold; white; on_green]

let prerr_step_begin str = prerr_string step_style (F.sprintf "== %s ...@." str)

let prerr_step_done str = prerr_string step_style (F.sprintf "== %s ... done!@.@." str)

let prerr_results str (pp : F.formatter -> 'a -> unit) (value : 'a) : unit =
  prerr_string result_style (F.asprintf "- %s: %a@." str pp value)


let prerr_step_evaluating (str : string) (v : 'a Lazy.t) : 'a =
  prerr_string step_style (F.sprintf "== %s ... @." str) ;
  let value = Lazy.force v in
  prerr_string step_style (F.sprintf "== %s ... done!@.@." str) ;
  value


let print_to_file ~msg ~filename =
  Utils.with_file_out filename ~f:(fun oc -> F.fprintf (F.formatter_of_out_channel oc) "%s" msg)


let prerr_progress () = prerr_string progress_style "@"

let find_node_with_location ~file ~line =
  List.concat_map (SourceFiles.proc_names_of_source file) ~f:(fun procname ->
      match Procdesc.load procname with
      | Some pdesc ->
          List.filter (Procdesc.get_nodes pdesc) ~f:(fun n -> Int.( = ) (get_node_loc_line n) line)
      | None ->
          [])


let read_json_file_exn filepath =
  match Utils.read_json_file filepath with
  | Ok json ->
      json
  | Error msg ->
      L.(die InternalError "Could not read or parse error report in %s:@\n%s@." filepath msg)


let source_file_from_string files filename =
  let find_or_raise files ~f =
    match List.find files ~f with
    | Some source_file ->
        source_file
    | None ->
        raise
          (Unexpected
             (F.asprintf "Could not find %s from captured files@. - %a@." filename (Pp.seq SourceFile.pp) files))
  in
  if Char.equal filename.[0] '/' then
    find_or_raise files ~f:(fun source_file -> String.(filename = SourceFile.to_abs_path source_file))
  else find_or_raise files ~f:(fun source_file -> String.(filename = SourceFile.to_rel_path source_file))


let join_list list ~joinable ~join =
  let rec _join acc = function
    | [] ->
        acc
    | work :: rest ->
        let list_joinable, list_unjoinable = List.partition_tf rest ~f:(joinable work) in
        if List.is_empty list_joinable then _join (work :: acc) list_unjoinable
        else
          let joined = List.fold list_joinable ~init:work ~f:join in
          _join acc (joined :: list_unjoinable)
  in
  _join [] list
