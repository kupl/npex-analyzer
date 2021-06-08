open! IStd
open! Vocab
module F = Format
module L = Logging

module type SpecTransfer = TransferFunctions.DisjReady with module Domain = SpecCheckerDomain

module type DisjSpecDom = sig
  type t = SpecCheckerDomain.t list

  val leq : lhs:t -> rhs:t -> bool

  val pp : Formatter.t -> t -> unit

  val join : t -> t -> t

  val widen : prev:t -> next:t -> num_iters:int -> t
end

module type DisjSpecTransfer = sig
  module CFG : ProcCfg.S

  module Domain : DisjSpecDom

  type analysis_data

  val exec_instr : Domain.t -> analysis_data -> CFG.Node.t -> Sil.instr -> Domain.t

  val pp_session_name : CFG.Node.t -> Format.formatter -> unit
end

type exec_node_schedule_result = ReachedFixPoint | DidNotReachFixPoint

module VisitCount : sig
  type t = private int

  val first_time : t

  val succ : t -> t
end = struct
  type t = int

  let first_time = 1

  let succ visit_count =
    let visit_count' = visit_count + 1 in
    if visit_count' > Config.max_widens then
      L.die InternalError
        "Exceeded max widening threshold %d. Please check your widening operator or increase the threshold"
        Config.max_widens ;
    visit_count'
end

module State = struct
  type 'a t = {pre: 'a; post: 'a; visit_count: VisitCount.t}

  let pre {pre} = pre

  let post {post} = post
end

(** use this as [pp_instr] everywhere a SIL CFG is expected *)
let pp_sil_instr _ instr =
  Some (fun f -> F.fprintf f "@[<h>%a;@]@;" (Sil.pp_instr ~print_types:false Pp.text) instr)


(** internal module that extends transfer functions *)
module type NodeTransferFunctions = sig
  include DisjSpecTransfer

  val exec_node_instrs :
    Domain.t State.t option -> exec_instr:(Domain.t -> Sil.instr -> Domain.t) -> Domain.t -> _ Instrs.t -> Domain.t
  (** specifies how to symbolically execute the instructions of a node, using [exec_instr] to go
      over a single instruction *)
end

(** most transfer functions will use this simple [Instrs.fold] approach *)
module AbstractInterpreterCommon (TransferFunctions : NodeTransferFunctions) = struct
  module CFG = TransferFunctions.CFG
  module Node = CFG.Node
  module TransferFunctions = TransferFunctions
  module InvariantMap = TransferFunctions.CFG.Node.IdMap
  module Domain = TransferFunctions.Domain

  type invariant_map = Domain.t State.t InvariantMap.t

  (** extract the state of node [n] from [inv_map] *)
  let extract_state node_id inv_map = InvariantMap.find_opt node_id inv_map

  (** extract the postcondition of node [n] from [inv_map] *)
  let extract_post node_id inv_map = extract_state node_id inv_map |> Option.map ~f:State.post

  (** extract the precondition of node [n] from [inv_map] *)
  let extract_pre node_id inv_map = extract_state node_id inv_map |> Option.map ~f:State.pre

  let debug_absint_operation op =
    let pp_op fmt op =
      match op with
      | `Join _ ->
          F.pp_print_string fmt "JOIN"
      | `Widen (num_iters, _) ->
          F.fprintf fmt "WIDEN(num_iters= %d)" num_iters
    in
    let left, right, result = match op with `Join lrr | `Widen (_, lrr) -> lrr in
    let pp_right f = if phys_equal right left then F.pp_print_string f "= LEFT" else Domain.pp f right in
    let pp_result f =
      if phys_equal result left then F.pp_print_string f "= LEFT"
      else if phys_equal result right then F.pp_print_string f "= RIGHT"
      else Domain.pp f result
    in
    L.d_printfln_escaped "%a@\n@\nLEFT:   %a@\nRIGHT:  %t@\nRESULT: %t@." pp_op op Domain.pp left pp_right
      pp_result


  (** reference to log errors only at the innermost recursive call *)
  let logged_error = ref false

  let dump_html ~pp_instr pre instr post_result =
    let pp_post_error f (exn, _, instr) =
      F.fprintf f "Analysis stopped in `%a` by error: %a."
        (Sil.pp_instr ~print_types:false Pp.text)
        instr Exn.pp exn
    in
    let pp_post f post =
      match post with
      | Ok astate_post ->
          if phys_equal astate_post pre then F.pp_print_string f "STATE UNCHANGED"
          else F.fprintf f "STATE:@\n@[%a@]" Domain.pp astate_post
      | Error err ->
          pp_post_error f err
    in
    let pp_all f =
      (* we pass [pre] to [pp_instr] because HIL needs it to interpret temporary variables *)
      match (pp_instr pre instr, post_result) with
      | None, Ok _ ->
          ()
      | None, Error err ->
          pp_post_error f err
      | Some pp_instr, _ ->
          Format.fprintf f "@[<h>INSTR=  %t@]@\n@\n%a@\n" pp_instr pp_post post_result
    in
    L.d_printfln_escaped "%t" pp_all


  let exec_node_instrs old_state_opt ~pp_instr proc_data node pre =
    let instrs = CFG.instrs node in
    if Config.write_html then L.d_printfln_escaped "PRE STATE:@\n@[%a@]@\n" Domain.pp pre ;
    let exec_instr pre instr =
      AnalysisState.set_instr instr ;
      let result =
        try
          let post = TransferFunctions.exec_instr pre proc_data node instr in
          (* don't forget to reset this so we output messages for future errors too *)
          logged_error := false ;
          Ok post
        with exn ->
          (* delay reraising to get a chance to write the debug HTML *)
          let backtrace = Caml.Printexc.get_raw_backtrace () in
          Error (exn, backtrace, instr)
      in
      if Config.write_html then dump_html ~pp_instr pre instr result ;
      match result with
      | Ok post ->
          post
      | Error (exn, backtrace, instr) ->
          ( match exn with
          | TaskSchedulerTypes.ProcnameAlreadyLocked _ ->
              (* this isn't an error; don't log it *)
              ()
          | _ ->
              if not !logged_error then (
                L.internal_error "In instruction %a@\n" (Sil.pp_instr ~print_types:true Pp.text) instr ;
                logged_error := true ) ) ;
          Caml.Printexc.raise_with_backtrace exn backtrace
    in
    (* hack to ensure that we call `exec_instr` on a node even if it has no instructions *)
    let instrs = if Instrs.is_empty instrs then Instrs.singleton Sil.skip_instr else instrs in
    TransferFunctions.exec_node_instrs old_state_opt ~exec_instr pre instrs


  (* Note on narrowing operations: we defines the narrowing operations simply to take a smaller one.
     So, as of now, the termination of narrowing is not guaranteed in general. *)
  let exec_node ~pp_instr analysis_data node ~is_loop_head ~is_narrowing astate_pre inv_map =
    let node_id = Node.id node in
    let update_inv_map inv_map new_pre old_state_opt =
      let new_post = exec_node_instrs old_state_opt ~pp_instr analysis_data node new_pre in
      let new_visit_count =
        match old_state_opt with
        | None ->
            VisitCount.first_time
        | Some {State.visit_count; _} ->
            VisitCount.succ visit_count
      in
      InvariantMap.add node_id {State.pre= new_pre; post= new_post; visit_count= new_visit_count} inv_map
    in
    let inv_map, converged =
      if InvariantMap.mem node_id inv_map then
        let old_state = InvariantMap.find node_id inv_map in
        let new_pre =
          if is_loop_head && not is_narrowing then (
            let num_iters = (old_state.State.visit_count :> int) in
            let prev = old_state.State.pre in
            let next = astate_pre in
            let res = Domain.widen ~prev ~next ~num_iters in
            if Config.write_html then debug_absint_operation (`Widen (num_iters, (prev, next, res))) ;
            res )
          else astate_pre
        in
        if
          if is_narrowing then
            (old_state.State.visit_count :> int) > Config.max_narrows
            || Domain.leq ~lhs:old_state.State.pre ~rhs:new_pre
          else Domain.leq ~lhs:new_pre ~rhs:old_state.State.pre
        then (inv_map, ReachedFixPoint)
        else if is_narrowing && not (Domain.leq ~lhs:new_pre ~rhs:old_state.State.pre) then (
          L.d_printfln "Terminate narrowing because old and new states are not comparable: %a@." Node.pp_id node_id ;
          (inv_map, ReachedFixPoint) )
        else (update_inv_map inv_map new_pre (Some old_state), DidNotReachFixPoint)
      else (* first time visiting this node *)
        (update_inv_map inv_map astate_pre None, DidNotReachFixPoint)
    in
    (match converged with ReachedFixPoint -> L.d_printfln "Fixpoint reached.@." | DidNotReachFixPoint -> ()) ;
    (inv_map, converged)


  (* shadowed for HTML debug *)
  let exec_node ~pp_instr proc_data node ~is_loop_head ~is_narrowing astate_pre inv_map =
    AnalysisCallbacks.html_debug_new_node_session (Node.underlying_node node)
      ~kind:(if is_narrowing then `ExecNodeNarrowing else `ExecNode)
      ~pp_name:(TransferFunctions.pp_session_name node)
      ~f:(fun () -> exec_node ~pp_instr proc_data node ~is_loop_head ~is_narrowing astate_pre inv_map)


  let compute_pre cfg node inv_map =
    let open IOption.Let_syntax in
    let extract_post_ pred =
      match
        ( Procdesc.Node.get_kind (CFG.Node.underlying_node pred)
        , Procdesc.Node.get_kind (CFG.Node.underlying_node node) )
      with
      | Start_node, Exit_node ->
          (* NPEX: invalidate Unexpected transfer (e.g., start to exit) *)
          None
      | _, Stmt_node ExceptionHandler | _, Stmt_node ExceptionsSink ->
          (* NPEX: filter before join so that useless states are not pruned *)
          let+ post = extract_post (Node.id pred) inv_map in
          List.filter post ~f:SpecCheckerDomain.is_exceptional
      | _, Exit_node ->
          extract_post (Node.id pred) inv_map
      | _ ->
          (* NPEX: filter before join so that useless states are not pruned *)
          let+ post = extract_post (Node.id pred) inv_map in
          List.filter post ~f:(not <<< SpecCheckerDomain.is_exceptional)
    in
    CFG.fold_preds cfg node ~init:None ~f:(fun joined_post_opt pred ->
        match extract_post_ pred with
        | None ->
            joined_post_opt
        | Some post as some_post -> (
          match joined_post_opt with
          | None ->
              some_post
          | Some joined_post ->
              (* NPEX HEURISTICS: disable join here *)
              let res = post @ joined_post in
              if Config.write_html then debug_absint_operation (`Join (joined_post, post, res)) ;
              Some res ))


  let compute_pre cfg node inv_map =
    (* NPEX: to handle exceptional flow *)
    match Procdesc.Node.get_kind (CFG.Node.underlying_node node) with
    | Exit_node -> (
        let result_opt = compute_pre cfg node inv_map in
        match result_opt with
        | Some result ->
            Some result
        | None ->
            L.progress "%a is not valid procedure@." Procname.pp (CFG.proc_desc cfg |> Procdesc.get_proc_name) ;
            CFG.fold_preds cfg node ~init:(Some []) ~f:(fun acc pred ->
                L.progress "pred node: %a@." InterNode.pp_pnode (CFG.Node.underlying_node pred) ;
                acc) )
    | Stmt_node ExceptionHandler | Stmt_node ExceptionsSink ->
        L.d_printfln "ExceptionHandler Node: invalidate non-exceptional states" ;
        compute_pre cfg node inv_map
    | _ ->
        L.d_printfln "Normal Node: invalidate exceptional states" ;
        compute_pre cfg node inv_map


  (* shadowed for HTML debug *)
  let compute_pre cfg node inv_map =
    AnalysisCallbacks.html_debug_new_node_session (Node.underlying_node node) ~kind:`ComputePre
      ~pp_name:(TransferFunctions.pp_session_name node) ~f:(fun () -> compute_pre cfg node inv_map)


  (** compute and return an invariant map for [pdesc] *)
  let make_exec_pdesc ~exec_cfg_internal analysis_data ~do_narrowing ~initial proc_desc =
    exec_cfg_internal ~pp_instr:pp_sil_instr (CFG.from_pdesc proc_desc) analysis_data ~do_narrowing ~initial


  (** compute and return the postcondition of [pdesc] *)
  let make_compute_post ~exec_cfg_internal ?(pp_instr = pp_sil_instr) analysis_data ~do_narrowing ~initial
      proc_desc =
    let cfg = CFG.from_pdesc proc_desc in
    let inv_map = exec_cfg_internal ~pp_instr cfg analysis_data ~do_narrowing ~initial in
    extract_post (Node.id (CFG.exit_node cfg)) inv_map
end

module MakeWTONode (TransferFunctions : NodeTransferFunctions) = struct
  include AbstractInterpreterCommon (TransferFunctions)

  let debug_wto wto node =
    let underlying_node = Node.underlying_node node in
    AnalysisCallbacks.html_debug_new_node_session underlying_node ~kind:`WTO
      ~pp_name:(TransferFunctions.pp_session_name node) ~f:(fun () ->
        let pp_node fmt node = node |> Node.id |> Node.pp_id fmt in
        L.d_printfln "%a" (WeakTopologicalOrder.Partition.pp ~pp_node) wto ;
        let loop_heads =
          wto |> IContainer.to_rev_list ~fold:WeakTopologicalOrder.Partition.fold_heads |> List.rev
        in
        L.d_printfln "Loop heads: %a" (Pp.seq pp_node) loop_heads)


  let exec_wto_node ~pp_instr cfg proc_data inv_map node ~is_loop_head ~is_narrowing =
    match compute_pre cfg node inv_map with
    | Some astate_pre ->
        exec_node ~pp_instr proc_data node ~is_loop_head ~is_narrowing astate_pre inv_map
    | None ->
        L.(die InternalError) "Could not compute the pre of a node"


  (* [WidenThenNarrow] mode is to narrow the outermost loops eagerly, so that over-approximated
     widened values do not flow to the following code.

     Problem: There are two phases for finding a fixpoint, widening and narrowing.  First, it finds
     a fixpoint with widening, in function level.  After that, it finds a fixpoint with narrowing.
     A problem is that sometimes an overly-approximated, imprecise, values by widening are flowed to
     the following loops.  They are hard to narrow in the narrowing phase because there is a cycle
     preventing it.

     To mitigate the problem, it tries to do narrowing, in loop level, right after it found a
     fixpoint of a loop.  Thus, it narrows before the widened values are flowed to the following
     loops.  In order to guarantee the termination of the analysis, this eager narrowing is applied
     only to the outermost loops or when the first visits of each loops. *)
  type mode = Widen | WidenThenNarrow | Narrow

  let is_narrowing_of = function Widen | WidenThenNarrow -> false | Narrow -> true

  let rec exec_wto_component ~pp_instr cfg proc_data inv_map head ~is_loop_head ~mode ~is_first_visit rest =
    let is_narrowing = is_narrowing_of mode in
    match exec_wto_node ~pp_instr cfg proc_data inv_map head ~is_loop_head ~is_narrowing with
    | inv_map, ReachedFixPoint ->
        if is_narrowing && is_first_visit then
          exec_wto_rest ~pp_instr cfg proc_data inv_map head ~mode ~is_first_visit rest
        else inv_map
    | inv_map, DidNotReachFixPoint ->
        exec_wto_rest ~pp_instr cfg proc_data inv_map head ~mode ~is_first_visit rest


  and exec_wto_rest ~pp_instr cfg proc_data inv_map head ~mode ~is_first_visit rest =
    let inv_map = exec_wto_partition ~pp_instr cfg proc_data ~mode ~is_first_visit inv_map rest in
    exec_wto_component ~pp_instr cfg proc_data inv_map head ~is_loop_head:true ~mode ~is_first_visit:false rest


  and exec_wto_partition ~pp_instr cfg proc_data ~mode ~is_first_visit inv_map
      (partition : CFG.Node.t WeakTopologicalOrder.Partition.t) =
    match partition with
    | Empty ->
        inv_map
    | Node {node; next} ->
        let inv_map =
          exec_wto_node ~pp_instr cfg proc_data ~is_narrowing:(is_narrowing_of mode) inv_map node
            ~is_loop_head:false
          |> fst
        in
        exec_wto_partition ~pp_instr cfg proc_data ~mode ~is_first_visit inv_map next
    | Component {head; rest; next} ->
        let inv_map =
          match mode with
          | Widen when is_first_visit ->
              do_widen_then_narrow ~pp_instr cfg proc_data inv_map head ~is_first_visit rest
          | Widen | Narrow ->
              exec_wto_component ~pp_instr cfg proc_data inv_map head ~is_loop_head:false ~mode ~is_first_visit
                rest
          | WidenThenNarrow ->
              do_widen_then_narrow ~pp_instr cfg proc_data inv_map head ~is_first_visit rest
        in
        exec_wto_partition ~pp_instr cfg proc_data ~mode ~is_first_visit inv_map next


  and do_widen_then_narrow ~pp_instr cfg proc_data inv_map head ~is_first_visit rest =
    let inv_map =
      exec_wto_component ~pp_instr cfg proc_data inv_map head ~is_loop_head:false ~mode:Widen ~is_first_visit rest
    in
    exec_wto_component ~pp_instr cfg proc_data inv_map head ~is_loop_head:false ~mode:Narrow ~is_first_visit rest


  let exec_cfg_internal ~pp_instr cfg proc_data ~do_narrowing ~initial =
    let wto = CFG.wto cfg in
    let exec_cfg ~mode inv_map =
      match wto with
      | Empty ->
          inv_map (* empty cfg *)
      | Node {node= start_node; next} as wto ->
          if Config.write_html then debug_wto wto start_node ;
          let inv_map, _did_not_reach_fix_point =
            exec_node ~pp_instr proc_data start_node ~is_loop_head:false ~is_narrowing:(is_narrowing_of mode)
              initial inv_map
          in
          exec_wto_partition ~pp_instr cfg proc_data ~mode ~is_first_visit:true inv_map next
      | Component _ ->
          L.(die InternalError) "Did not expect the start node to be part of a loop"
    in
    if do_narrowing then exec_cfg ~mode:WidenThenNarrow InvariantMap.empty |> exec_cfg ~mode:Narrow
    else exec_cfg ~mode:Widen InvariantMap.empty


  let exec_cfg ?(do_narrowing = false) = exec_cfg_internal ~pp_instr:pp_sil_instr ~do_narrowing

  let exec_pdesc ?(do_narrowing = false) = make_exec_pdesc ~exec_cfg_internal ~do_narrowing

  let compute_post ?(do_narrowing = false) = make_compute_post ~exec_cfg_internal ~do_narrowing
end

module MakeSpecTransferFunctions (T : SpecTransfer) (DConfig : TransferFunctions.DisjunctiveConfig) = struct
  module CFG = T.CFG

  type analysis_data = T.analysis_data

  module Domain = struct
    (** a list [\[x1; x2; ...; xN\]] represents a disjunction [x1 ∨ x2 ∨ ... ∨ xN] *)
    type t = T.Domain.t list

    let rev_filter_not_over_approximated disjuncts ~not_in =
      List.rev_filter disjuncts ~f:(fun disjunct ->
          List.exists not_in ~f:(fun disj_not_in -> T.Domain.leq ~lhs:disjunct ~rhs:disj_not_in) |> not)


    let join : t -> t -> t = fun lhs rhs -> if phys_equal lhs rhs then lhs else T.Domain.merge (lhs @ rhs)

    (** check if elements of [disj] appear in [of_] in the same order, using pointer equality on
        abstract states to compare elements quickly *)
    let rec is_trivial_subset disj ~of_ =
      match (disj, of_) with
      | [], _ ->
          true
      | x :: disj', y :: of' when phys_equal x y ->
          is_trivial_subset disj' ~of_:of'
      | _, _ :: of' ->
          is_trivial_subset disj ~of_:of'
      | _, [] ->
          false


    let leq ~lhs ~rhs = phys_equal lhs rhs || is_trivial_subset lhs ~of_:rhs

    (** Ignore states in [lhs] that are over-approximated in [rhs] and vice-versa. Favors keeping
        states in [lhs]. *)
    let join lhs rhs =
      let rev_rhs_not_in_lhs = rev_filter_not_over_approximated rhs ~not_in:lhs in
      (* cheeky: this is only used in pulse, whose (<=) is actually a symmetric relation so there's
         no need to filter out elements of [lhs] *)
      join lhs rev_rhs_not_in_lhs


    let widen ~prev ~next ~num_iters =
      let (`UnderApproximateAfterNumIterations max_iter) = DConfig.widen_policy in
      if phys_equal prev next then prev
      else if num_iters > max_iter then (
        L.d_printfln "Iteration %d is greater than max iter %d, stopping." num_iters max_iter ;
        prev )
      else prev @ next


    let pp f disjuncts =
      let pp_disjuncts f disjuncts =
        List.iteri disjuncts ~f:(fun i disjunct -> F.fprintf f "#%d: @[%a@]@;" i T.Domain.pp disjunct)
      in
      F.fprintf f "@[<v>%d disjuncts:@;%a@]" (List.length disjuncts) pp_disjuncts disjuncts
  end

  let exec_instr pre_disjuncts analysis_data node instr =
    let post_disjuncts =
      List.foldi pre_disjuncts ~init:[] ~f:(fun i post_disjuncts pre_disjunct ->
          L.d_printfln "@[<v2>Executing instruction from disjunct #%d@;" i ;
          let disjuncts' = T.exec_instr pre_disjunct analysis_data node instr in
          ( if Config.write_html then
            let n = List.length disjuncts' in
            L.d_printfln "@]@\n@[Got %d disjunct%s back@]" n (if Int.equal n 1 then "" else "s") ) ;
          (* NPEX HEURISTICS: disable join here*)
          post_disjuncts @ disjuncts')
    in
    post_disjuncts


  let exec_node_instrs old_state_opt ~exec_instr pre instrs =
    let is_new_pre disjunct =
      match old_state_opt with
      | None ->
          true
      | Some {State.pre= previous_pre; _} ->
          not (List.mem ~equal:phys_equal previous_pre disjunct)
    in
    let old_post = match old_state_opt with None -> [] | Some {State.post; _} -> post in
    let new_post =
      List.foldi pre ~init:[] ~f:(fun i post_disjuncts pre_disjunct ->
          if is_new_pre pre_disjunct then (
            L.d_printfln "@[<v2>Executing node from disjunct #%d@;" i ;
            let disjuncts' = Instrs.fold ~init:[pre_disjunct] instrs ~f:exec_instr in
            L.d_printfln "@]@\n" ;
            (* NPEX HEURISTICS: disable join here*)
            post_disjuncts @ disjuncts' )
          else (
            L.d_printfln "@[Skipping already-visited disjunct #%d@]@;" i ;
            post_disjuncts ))
    in
    (* NPEX HEURISTICS: merge states if more than one states are generated *)
    if List.length new_post > 1 then old_post @ Domain.join new_post [] else old_post @ new_post


  let pp_session_name node f = T.pp_session_name node f
end

module Make (T : SpecTransfer) (DConfig : TransferFunctions.DisjunctiveConfig) =
  MakeWTONode (MakeSpecTransferFunctions (T) (DConfig))
