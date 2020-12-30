open! IStd
open! Vocab
module L = Logging
module F = Format
module Hashtbl = Caml.Hashtbl
module Node = InstrNode
module NSet = PrettyPrintable.MakePPSet (Node)
module NodeMap = PrettyPrintable.MakePPMap (Node)

type t = AccessExpr.t NodeMap.t

let pp = NodeMap.pp ~pp_value:AccessExpr.pp

let join (x : t) (y : t) : t = NodeMap.union (fun _ ae1 _ -> Some ae1) x y

module Semantics = struct
  type node = InstrNode.t * Interpreter.state

  type t = node list

  let pp_node fmt (instr_node, state) =
    F.fprintf fmt "State: %aNode:%a@." Interpreter.pp state InstrNode.pp instr_node


  let pp fmt trace = F.fprintf fmt "@.==== Semantic Trace ====@.%a" (Pp.seq ~sep:"\n" pp_node) trace
end

let analyze_path program (trace : ErrTrace.t) : Semantics.t =
  let open ErrTrace in
  let[@warning "-8"] (head :: rest) = trace in
  let init : Semantics.t = [(head |> fst, Interpreter.empty)] in
  List.foldi ~init rest ~f:(fun i (acc : Semantics.t) (node : node) ->
      let _, state = List.rev acc |> List.hd_exn in
      let new_state =
        match node with
        | instr_node, Intra | instr_node, Sink ->
            Interpreter.exec_instr state instr_node
        | instr_node, Call ->
            let callee = List.nth_exn rest (i + 1) |> fst |> InstrNode.get_proc_name in
            let callee_pdesc = Program.pdesc_of program callee in
            let formals = Procdesc.get_pvar_formals callee_pdesc in
            Interpreter.bind_argument state callee instr_node ~formals
        | instr_node, CallRet ->
            let callee = List.nth_exn rest (i - 1) |> fst |> InstrNode.get_proc_name in
            let callee_pdesc = Program.pdesc_of program callee in
            let retvar = Procdesc.get_ret_var callee_pdesc in
            Interpreter.bind_retvar state (InstrNode.get_instr instr_node) ~retvar
        | _, Entry ->
            state
      in
      acc @ [(fst node, new_state)])


(* Localize null point from semantics 
   1. point where null pointer is first defined (p = null, foo(null))
   2. point where null pointer is copied (p = nullpointer, p = getNull())
   3. point where null pointer is parameter (foo (nullpointer))
*)
let localize_from_semantics program nullpoint semantics nullflow : t =
  let open Interpreter in
  let NullPoint.{null_exp; node; instr} = nullpoint in
  let null_node = InstrNode.make node instr in
  let null_loc =
    let _, last_state = List.rev semantics |> List.hd_exn in
    Interpreter.eval last_state ~node:null_node ~pos:0 null_exp
  in
  L.progress " - found null location: %a@." AbsLoc.pp null_loc ;
  (* L.progress "%a@." Semantics.pp semantics ; *)
  if AbsLoc.is_null null_loc || AbsLoc.is_extern null_loc then
    List.foldi ~init:nullflow semantics ~f:(fun i acc (node, state) ->
        let prev_state = if Int.equal i 0 then state else List.nth_exn semantics (i - 1) |> snd in
        let pdesc = Program.pdesc_of program (InstrNode.get_proc_name node) in
        match InstrNode.get_instr node with
        | Sil.Store {e2} when AbsLoc.equal null_loc (eval prev_state ~node ~pos:0 e2) -> (
          try NodeMap.add node (AccessExpr.from_IR_exp pdesc e2) acc
          with _ ->
            L.progress "[WARNING] cannot convert null-exp %a in %a to AccessExpr@." Exp.pp e2 Procname.pp
              (InstrNode.get_proc_name node) ;
            acc )
        | Sil.Call (_, _, arg_typs, _, _) ->
            List.foldi arg_typs ~init:acc ~f:(fun i acc (e, _) ->
                if AbsLoc.equal null_loc (eval prev_state ~node ~pos:i e) then
                  NodeMap.add node (AccessExpr.from_IR_exp pdesc e) acc
                else acc)
        | _ when InstrNode.is_entry node ->
            let formal_pvars = Procdesc.get_pvar_formals pdesc in
            List.fold formal_pvars ~init:acc ~f:(fun acc (pv, _) ->
                let loc_of_pv = eval state ~node ~pos:0 (Exp.Lvar pv) in
                let pointsto_of_pv = points_to_of state loc_of_pv in
                if AbsLoc.equal null_loc pointsto_of_pv then
                  NodeMap.add node (AccessExpr.from_IR_exp pdesc (Exp.Lvar pv)) acc
                else acc)
        | _ ->
            acc)
  else nullflow


let from_traces program nullpoint traces : t =
  List.fold traces ~init:NodeMap.empty ~f:(fun acc trace ->
      let semantics = analyze_path program trace in
      localize_from_semantics program nullpoint semantics acc)


let generate_npe_list nullflow =
  NodeMap.iter
    (fun node aexpr ->
      let Location.{file; line} = Node.get_loc node in
      let class_name =
        match Node.get_proc_name node with
        | Procname.Java java ->
            Procname.Java.get_simple_class_name java
        | _ as proc ->
            L.(die ExternalError) "%a is not java method" Procname.pp proc
      in
      (* TODO: multiple access expressions? *)
      let deref_field = AccessExpr.get_deref_field aexpr in
      let json =
        let filepath_json = `String (SourceFile.to_string file) in
        let line_json = `Int line in
        let deref_field_json = `String deref_field in
        let npe_class_json = `String class_name in
        let npe_method_json = `String (Node.get_proc_name node |> Procname.get_method) in
        `Assoc
          [ ("filepath", filepath_json)
          ; ("line", line_json)
          ; ("deref_field", deref_field_json)
          ; ("npe_class", npe_class_json)
          ; ("npe_method", npe_method_json) ]
      in
      let filename = String.split (SourceFile.to_string file) ~on:'/' |> List.rev |> List.hd_exn in
      Utils.write_json_to_file (F.asprintf "npe_%s_%d.json" filename line) json)
    nullflow
