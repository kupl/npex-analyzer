open! IStd
open! Vocab
module L = Logging
module Node = InterNode
module NSet = PrettyPrintable.MakePPSet (Node)

module type IntraCfg = sig
  module G : module type of Graph.Imperative.Digraph.ConcreteBidirectional (Node)

  type t
end

module IntraCfg = struct
  module G = Graph.Imperative.Digraph.ConcreteBidirectional (Node)
  module InstrG = Graph.Imperative.Digraph.ConcreteBidirectional (InstrNode)
  module GDom = Graph.Dominator.Make_graph (G)
  module Oper = Graph.Oper.I (G)
  module Path = Graph.Path.Check (G)

  type t =
    { pdesc: Procdesc.t
    ; file: SourceFile.t
    ; graph: G.t
    ; mutable instr_graph: InstrG.t option
    ; mutable cfg_path_checker: Path.path_checker option
    ; mutable cfg_dom_tree: (G.t * Path.path_checker) option
    ; mutable cfg_pdom_tree: (G.t * Path.path_checker) option }

  let compute_dom_tree ~is_post pdesc cfg =
    let entry = pdesc |> (if is_post then Procdesc.get_exit_node else Procdesc.get_start_node) |> Node.of_pnode in
    let cfg = if is_post then Oper.mirror cfg else cfg in
    let GDom.{dom_tree} = GDom.compute_all cfg entry in
    let graph = G.create () in
    G.iter_vertex
      (fun v ->
        G.add_vertex graph v ;
        List.iter (dom_tree v) ~f:(G.add_edge graph v))
      cfg ;
    (graph, Path.create graph)


  let instr_graph_from_pdesc pdesc =
    let graph = InstrG.create () in
    let nodes =
      let pnodes = Procdesc.get_nodes pdesc in
      List.concat_map pnodes ~f:InstrNode.list_of_pnode
    in
    (* ignore procedures without body nodes *)
    if List.length nodes < 3 then graph
    else
      let add_succs node = List.iter (InstrNode.get_succs node) ~f:(InstrG.add_edge graph node) in
      List.iter nodes ~f:add_succs ; graph


  let from_pdesc pdesc =
    let g = G.create () in
    let insert_skip_instr_to_empty_node n =
      if Instrs.is_empty (Procdesc.Node.get_instrs n) then
        let location = Procdesc.Node.get_loc n in
        let instr_to_add = Sil.Metadata (Abstract location) in
        Procdesc.Node.replace_instrs_with_given n (Instrs.singleton instr_to_add)
    in
    Procdesc.iter_nodes
      (fun node ->
        insert_skip_instr_to_empty_node node ;
        (* print_node node ; *)
        List.iter (Procdesc.Node.get_succs node) ~f:(fun succ ->
            G.add_edge_e g (Node.of_pnode node, Node.of_pnode succ)))
      pdesc ;
    let Location.{file} = Procdesc.get_loc pdesc in
    {pdesc; file; graph= g; instr_graph= None; cfg_path_checker= None; cfg_dom_tree= None; cfg_pdom_tree= None}


  let pred {graph} x = G.pred graph x

  let succ {graph} x = G.succ graph x

  let get_instr_graph t =
    match t.instr_graph with
    | Some instr_graph ->
        instr_graph
    | None ->
        t.instr_graph <- Some (Profiler.pick "draw instr_graph" instr_graph_from_pdesc t.pdesc) ;
        Option.value_exn t.instr_graph


  let get_cfg_path_checker t =
    match t.cfg_path_checker with
    | Some cfg_path_checker ->
        cfg_path_checker
    | None ->
        t.cfg_path_checker <- Some (Profiler.pick "create path" Path.create t.graph) ;
        Option.value_exn t.cfg_path_checker


  let get_cfg_dom_tree t =
    match t.cfg_dom_tree with
    | Some cfg_dom_tree ->
        cfg_dom_tree
    | None ->
        t.cfg_dom_tree <- Some (Profiler.pick "compute_dom_tree" (compute_dom_tree ~is_post:false t.pdesc) t.graph) ;
        Option.value_exn t.cfg_dom_tree


  let get_cfg_pdom_tree t =
    match t.cfg_pdom_tree with
    | Some cfg_pdom_tree ->
        cfg_pdom_tree
    | None ->
        t.cfg_pdom_tree <-
          Some (Profiler.pick "compute_pdom_tree" (compute_dom_tree ~is_post:true t.pdesc) t.graph) ;
        Option.value_exn t.cfg_pdom_tree


  let pred_instr_node t x = InstrG.pred (get_instr_graph t) x

  let succ_instr_node t x = InstrG.succ (get_instr_graph t) x

  (* let iter_nodes {pdesc} ~f = Procdesc.iter_nodes f pdesc *)

  (* let fold_nodes {pdesc} ~f = Procdesc.fold_nodes f pdesc *)

  let is_reachable t x y = Path.check_path (get_cfg_path_checker t) x y

  let dom t x y = Path.check_path (snd (get_cfg_dom_tree t)) x y

  let pdom t x y = Path.check_path (snd (get_cfg_pdom_tree t)) x y

  let[@warning "-32"] mem_vertex {graph} = G.mem_vertex graph

  let find_reachable_nodes_of ?(forward = true) ?(reflexive = true) (graph : G.t) (init : NSet.t) : NSet.t =
    let fold_next = if forward then G.fold_succ else G.fold_pred in
    let rec __reach reachables wset =
      if NSet.is_empty wset then reachables
      else
        let w = NSet.choose wset in
        let rest = NSet.remove w wset in
        if G.mem_vertex graph w then
          let new_reachables =
            fold_next
              (fun succ acc -> if NSet.mem succ reachables then acc else NSet.add succ acc)
              graph w NSet.empty
          in
          __reach (NSet.union reachables new_reachables) (NSet.union new_reachables rest)
        else (
          L.progress "%a is not in the graph!.@" Node.pp w ;
          __reach reachables rest )
    in
    if reflexive then __reach init init else __reach NSet.empty init
end

module CallGraph =
  Graph.Imperative.Digraph.ConcreteBidirectionalLabeled
    (struct
      include Procname

      let hash = Hashtbl.hash
    end)
    (InstrNode)

module Dot = Graph.Graphviz.Dot (struct
  include CallGraph

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = Procname.to_string v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes (_, instr_node, _) = [`Label (F.asprintf "%a" InstrNode.pp instr_node)]
end)

type t =
  { cfgs: IntraCfg.t Procname.Map.t
  ; tenv: Tenv.t
  ; callgraph: CallGraph.t
  ; mutable library_calls: InstrNode.Set.t (* libary와 non-trace를 구분하기 위함 *)
  ; mutable class_inits: Procname.t list (* executed first *)
  ; mutable entries: Procname.t list (* execute @Before, then @TEST *) }

let get_entries {entries} = entries

let add_call_edge {callgraph} instr_node callee =
  CallGraph.add_edge_e callgraph (InstrNode.get_proc_name instr_node, instr_node, callee)


let print_callgraph program dotname =
  Utils.with_file_out dotname ~f:(fun oc -> Dot.output_graph oc program.callgraph)


let callers_of_instr_node {callgraph} instr_node =
  let preds = try CallGraph.pred_e callgraph (InstrNode.get_proc_name instr_node) with _ -> [] in
  List.filter_map preds ~f:(fun (pred, instr_node', _) ->
      if InstrNode.equal instr_node instr_node' then Some pred else None)


let callees_of_instr_node {callgraph} instr_node =
  let succs = try CallGraph.succ_e callgraph (InstrNode.get_proc_name instr_node) with _ -> [] in
  List.filter_map succs ~f:(fun (_, instr_node', succ) ->
      if InstrNode.equal instr_node instr_node' then Some succ else None)


let is_library_call t instr_node = InstrNode.Set.mem instr_node t.library_calls

let add_library_call t instr_node = t.library_calls <- InstrNode.Set.add instr_node t.library_calls

let add_entry t proc = if not (List.mem t.entries ~equal:Procname.equal proc) then t.entries <- proc :: t.entries

(* let dummy_node = Node.of_pnode (Procdesc.Node.dummy Procname.empty_block) *)

let cfgof {cfgs} pid = Procname.Map.find pid cfgs

let pdesc_of {cfgs} pid = (Procname.Map.find pid cfgs).IntraCfg.pdesc

let all_procs {cfgs} = Procname.Map.fold (fun p _ -> Procname.Set.add p) cfgs Procname.Set.empty

let all_nodes {cfgs} =
  Procname.Map.fold
    (fun _ IntraCfg.{pdesc} acc -> acc @ (Procdesc.get_nodes pdesc |> List.map ~f:InterNode.of_pnode))
    cfgs []


let all_instr_nodes {cfgs} =
  Procname.Map.fold
    (fun _ IntraCfg.{pdesc} acc -> acc @ (Procdesc.get_nodes pdesc |> List.concat_map ~f:InstrNode.list_of_pnode))
    cfgs []


(* let mem_vertex cfgs x = IntraCfg.mem_vertex (cfgof cfgs (Node.get_proc_name x)) x *)

let cfg_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive cfg.graph init


let dom_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive (fst (IntraCfg.get_cfg_dom_tree cfg)) init


let pdom_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive (fst (IntraCfg.get_cfg_pdom_tree cfg)) init


let is_reachable program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.is_reachable (cfgof program pid1) x y else false


let dom program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.dom (cfgof program pid1) x y else false


let pdom program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.pdom (cfgof program pid1) x y else false


let is_undef_proc program pid =
  try
    let pdesc = pdesc_of program pid in
    (* NOTE: undefined procedures (e.g., extern) may have a procdesc in Infer IR. *)
    let ProcAttributes.{is_defined} = Procdesc.get_attributes pdesc in
    (not is_defined) || Models.is_model pid
  with Caml.Not_found -> true


let pred program x = IntraCfg.pred (cfgof program (Node.get_proc_name x)) x

let succ program x = IntraCfg.succ (cfgof program (Node.get_proc_name x)) x

let pred_instr_node program x = IntraCfg.pred_instr_node (cfgof program (InstrNode.get_proc_name x)) x

let succ_instr_node program x = IntraCfg.succ_instr_node (cfgof program (InstrNode.get_proc_name x)) x

(* let get_blocks cfgs init =
  if NSet.is_empty init then NSet.empty
  else
    let pid = Node.get_proc_name (NSet.choose init) in
    let init = NSet.filter (fun n -> Procname.equal (Node.get_proc_name n) pid) init in
    let is_single_pred n = Int.equal (List.length (pred cfgs n)) 1 in
    let is_single_succ n = Int.equal (List.length (succ cfgs n)) 1 in
    let rec do_worklist acc worklist =
      if NSet.is_empty worklist then acc
      else
        let work = NSet.choose worklist in
        let rest = NSet.remove work worklist in
        let nexts =
          let preds = List.filter (pred cfgs work) ~f:is_single_succ in
          let succs = List.filter (succ cfgs work) ~f:is_single_pred in
          NSet.diff (NSet.of_list (preds @ succs)) acc
        in
        do_worklist (NSet.add work acc) (NSet.union rest nexts)
    in
    do_worklist init init *)

let build () : t =
  let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let procnames = List.concat_map source_files ~f:(fun src -> SourceFiles.proc_names_of_source src) in
  let tenv =
    let tenv' =
      List.fold source_files
        ~init:(Tenv.FileLocal (Tenv.create ()))
        ~f:(fun acc file ->
          let tenv_local =
            try Tenv.FileLocal (Option.value_exn (Tenv.load file))
            with _ -> L.(die ExternalError "Failed to load tenv file: %a@." SourceFile.pp file)
          in
          Tenv.merge_per_file ~src:tenv_local ~dst:acc)
    in
    match tenv' with Global -> L.(die InternalError "Global Tenv Found") | FileLocal t -> t
  in
  let cfgs =
    List.fold procnames ~init:Procname.Map.empty ~f:(fun acc procname ->
        match Procdesc.load procname with
        | Some pdesc ->
            Procname.Map.add procname (IntraCfg.from_pdesc pdesc) acc
        | None ->
            acc)
  in
  {cfgs; tenv; callgraph= CallGraph.create (); entries= []; class_inits= []; library_calls= InstrNode.Set.empty}


let has_instr ~f node = Instrs.exists (Node.get_instrs node) ~f

let marshalled_path = Filename.concat Config.results_dir "program.data"

let to_marshal program = Utils.with_file_out marshalled_path ~f:(fun oc -> Marshal.to_channel oc program [])

let get_files {cfgs} : SourceFile.t list = Procname.Map.fold (fun _ IntraCfg.{file} acc -> file :: acc) cfgs []

let get_nodes program pid =
  let IntraCfg.{pdesc} = cfgof program pid in
  Procdesc.get_nodes pdesc |> List.map ~f:Node.of_pnode


let get_exit_node program pid =
  let pdesc = pdesc_of program pid in
  Node.of_pnode (Procdesc.get_exit_node pdesc)


let get_entry_node program pid =
  let pdesc = pdesc_of program pid in
  Node.of_pnode (Procdesc.get_start_node pdesc)


let get_exit_instr_node program pid =
  let pdesc = pdesc_of program pid in
  Procdesc.get_exit_node pdesc |> InstrNode.list_of_pnode |> List.hd_exn


let get_entry_instr_node program pid =
  let pdesc = pdesc_of program pid in
  Procdesc.get_start_node pdesc |> InstrNode.list_of_pnode |> List.hd_exn


let cache : t option ref = ref None

let from_marshal () : t =
  match !cache with
  | Some program ->
      program
  | None ->
      let program =
        try Utils.with_file_in marshalled_path ~f:Marshal.from_channel
        with _ ->
          let program = build () in
          to_marshal program ; program
      in
      cache := Some program ;
      program


let find_node_with_location {cfgs} (Location.{file; line} as loc) : Node.t list =
  let pdescs = Procname.Map.fold (fun _ IntraCfg.{pdesc} acc -> pdesc :: acc) cfgs [] in
  let pdescs_file_matched =
    List.filter pdescs ~f:(fun pdesc -> SourceFile.equal file (Procdesc.get_loc pdesc).Location.file)
  in
  let nodes = List.concat_map pdescs_file_matched ~f:Procdesc.get_nodes in
  let rec find_nodes_with_line ~i ~line =
    if Int.equal i 0 then L.(die InternalError) "[ERROR]: cannot find node at %a" Location.pp_file_pos loc
    else
      let results =
        List.filter nodes ~f:(fun n -> Int.equal line (Procdesc.Node.get_loc n).Location.line)
        |> List.map ~f:Node.of_pnode
      in
      if List.is_empty results then find_nodes_with_line ~i:(i - 1) ~line:(line - 1) else results
  in
  find_nodes_with_line ~i:10 ~line


module TypSet = Caml.Set.Make (Typ)

let fields_of_typ program Typ.{desc} =
  match desc with
  | Tstruct strname -> (
    match Tenv.lookup program.tenv strname with Some {fields} -> fields | None -> [] )
  | _ ->
      []


let rec subtyps_of program typ =
  let fields = fields_of_typ program typ in
  List.fold fields ~init:TypSet.empty ~f:(fun acc (_, typ', _) -> TypSet.union (subtyps_of program typ') acc)


let is_primitive_type Typ.{desc} = match desc with Tint _ | Tfloat _ | Tfun _ -> true | _ -> false

let is_consistent_type t1 t2 =
  if Typ.is_pointer_to_void t1 || Typ.is_pointer_to_void t2 then true
  else if is_primitive_type t1 && is_primitive_type t2 then true
  else
    match (t1.Typ.desc, t2.Typ.desc) with
    | Tfun _, Tfun _ ->
        true
    | Tvoid, Tvoid ->
        true
    | Tptr _, Tptr _ ->
        true
    | Tstruct _, Tstruct _ ->
        true
    | _ ->
        false


let rec type_hierachy program t1 t2 =
  match (t1.Typ.desc, t2.Typ.desc) with
  | Tint _, Tint _ | Tint _, Tfloat _ | Tfloat _, Tint _ | Tfloat _, Tfloat _ ->
      true
  | Tvoid, _ ->
      true (* dynamic type *)
  | Tfun, Tfun ->
      true
  | Tptr (t1', Typ.Pk_pointer), Tptr (t2', Typ.Pk_pointer) ->
      type_hierachy program t1' t2'
  | Tptr _, Tptr _ ->
      true (* TODO: C++ reference *)
  | Tstruct (CStruct _), Tstruct (CStruct _) ->
      (* TODO: Check whether they have compatible types *)
      not (TypSet.is_empty (TypSet.inter (subtyps_of program t1) (subtyps_of program t2)))
  | Tstruct (JavaClass _ as name1), Tstruct (JavaClass _ as name2) ->
      (* TODO check: does it work for Object type? should we add not? *)
      Subtype.is_known_subtype program.tenv name1 name2
  | Tstruct _, Tstruct _ ->
      true (* TODO: CUnion, C++ class *)
  | _ ->
      false


let has_annot program annot pid =
  let pdesc = pdesc_of program pid in
  let method_annotation = (Procdesc.get_attributes pdesc).ProcAttributes.method_annotation in
  let annot_return = method_annotation.return in
  Annotations.ia_ends_with annot_return annot