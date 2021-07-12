open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode
module Loc = SymDom.Loc
module Val = SymDom.Val
module PathCond = SymDom.PathCond
module PC = SymDom.PC
module Symbol = SymDom.Symbol
module SymExp = SymDom.SymExp
module SymHeap = SymDom.SymHeap
module Reg = SymDom.Reg
module Mem = SymDom.Mem
module Vars = PrettyPrintable.MakePPSet (Var)

(* TODO: add counter for each state *)
type t =
  { reg: Reg.t
  ; mem: Mem.t
  ; pc: PC.t
  ; is_npe_alternative: bool
  ; is_exceptional: bool
  ; applied_models: NullModel.t
  ; probability: float
  ; fault: NullPoint.t option
  ; nullptrs: Val.Set.t
  ; executed_procs: Procname.Set.t (* For optimization of inference and verification *)
  ; uncaught_npes: Val.t list
  ; temps_to_remove: Vars.t
  ; current_proc: Procname.t }

let pp fmt
    {reg; mem; pc; is_npe_alternative; is_exceptional; probability; applied_models; nullptrs; fault; uncaught_npes}
    =
  F.fprintf fmt
    "@[<v 2>  - Register:@,\
    \   %a@,\
    \ - Memory:@,\
    \   %a@,\
    \ - Path Conditions:@,\
    \   %a@,\
    \ - Is NPE Alternative? Is Exceptional?@,\
    \   %b,%b@,\
    \ - Applied Null Models:@,\
    \   (%f) %a@,\
    \ - Fault and Null Values:@,\
    \   %a, %a@,\
    \ - Uncaughted NPEs:@,\
    \   %a@]" Reg.pp reg Mem.pp mem PC.pp pc is_npe_alternative is_exceptional probability NullModel.pp
    applied_models (Pp.option NullPoint.pp) fault Val.Set.pp nullptrs (Pp.seq Val.pp) uncaught_npes


let cardinal x =
  (* To minimize randomness in fixed-point iteration *)
  let is_npe_alternative = if x.is_npe_alternative then 1 else 0 in
  let is_exceptional = if x.is_exceptional then 1 else 0 in
  let reg = Reg.cardinal x.reg in
  let mem = Mem.cardinal x.mem in
  let pc = PC.cardinal x.pc in
  is_npe_alternative + is_exceptional + reg + mem + pc


let leq ~lhs ~rhs =
  (* Optimization in disjunctive analysis: prune redundant states *)
  phys_equal lhs rhs


let bottom =
  { reg= Reg.bottom
  ; mem= Mem.bottom
  ; pc= PC.empty
  ; is_npe_alternative= false
  ; is_exceptional= false
  ; applied_models= NullModel.empty
  ; probability= 0.5
  ; nullptrs= Val.Set.empty
  ; fault= None
  ; executed_procs= Procname.Set.empty
  ; uncaught_npes= []
  ; temps_to_remove= Vars.empty
  ; current_proc= Procname.empty_block }


let is_bottom {reg; mem; pc} = Reg.is_bottom reg && Mem.is_bottom mem && PC.is_bottom pc

(** Basic Queries *)
let is_unknown_loc {mem} l = Loc.is_unknown l || not (Mem.mem l mem)

let is_unknown_id {reg} id = Val.is_bottom (Reg.find id reg)

let is_exceptional {is_exceptional} = is_exceptional

let has_uncaught_npes {uncaught_npes} = not (List.is_empty uncaught_npes)

let has_uncaught_model_npes {uncaught_npes} =
  (* This indicate that NPEs are not fixed in inferenced or patched state *)
  List.exists ~f:Val.is_model_null uncaught_npes


let is_inferred {applied_models; fault} = (not (NullModel.is_empty applied_models)) || Option.is_some fault

let is_npe_alternative {is_npe_alternative} = is_npe_alternative

let is_valid_pc astate pathcond = PC.is_valid pathcond astate.pc

let is_fault_null astate v = Val.Set.mem v astate.nullptrs

(** Read & Write *)
let read_loc {mem; pc} l =
  let v = Mem.find l mem in
  match PC.equal_constant_opt pc v with Some const -> const | None -> v


let read_id {reg} id = Reg.find id reg

let equal_values astate v = PC.equal_values astate.pc v

let inequal_values astate v = PC.inequal_values astate.pc v

let all_values {reg; pc; mem; nullptrs; uncaught_npes} =
  let reg_values = Reg.fold (fun _ v -> Val.Set.add v) reg Val.Set.empty in
  let pc_values = PC.all_values pc |> Val.Set.of_list in
  let mem_values =
    Mem.fold
      (fun l v ->
        match l with
        | Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _) ->
            Val.Set.add v <<< Val.Set.add (Val.Vheap sh)
        | _ ->
            Val.Set.add v)
      mem Val.Set.empty
  in
  reg_values
  |> Val.Set.union pc_values
  |> Val.Set.union mem_values
  |> Val.Set.union nullptrs
  |> Val.Set.union (Val.Set.of_list uncaught_npes)


let all_symbols astate =
  let rec add_if_symbol v acc_symvals =
    match v with
    | Val.Vint (SymExp.Symbol _) ->
        Val.Set.add v acc_symvals
    | Val.Vheap (SymHeap.Symbol _) ->
        Val.Set.add v acc_symvals
    | Val.Vextern (_, args) ->
        List.fold args ~init:acc_symvals ~f:(fun acc_symvals' v -> add_if_symbol v acc_symvals')
    | _ ->
        acc_symvals
  in
  let symvals_appered = Val.Set.fold add_if_symbol (all_values astate) Val.Set.empty in
  Val.Set.fold
    (fun v ->
      let s =
        match v with
        | Val.Vint (Symbol s) | Val.Vheap (Symbol s) ->
            s
        | _ ->
            L.(die InternalError) "%a is non-symbolic values" Val.pp v
      in
      List.map (Symbol.sub_symbols s) ~f:(fun s -> Val.Vheap (Symbol s)) |> Val.Set.of_list |> Val.Set.union)
    symvals_appered symvals_appered


let store_loc astate l v : t =
  if Val.is_constant v then
    let extern_symbol = Val.make_const_extern v in
    let mem' = Mem.strong_update l extern_symbol astate.mem in
    let pc' = PC.add (PathCond.make_physical_equals Binop.Eq extern_symbol v) astate.pc in
    {astate with mem= mem'; pc= pc'}
  else {astate with mem= Mem.strong_update l v astate.mem}


let store_reg astate id v = {astate with reg= Reg.strong_update id v astate.reg}

let remove_id astate id =
  if Reg.mem id astate.reg then {astate with reg= Reg.remove id astate.reg}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_pvar astate ~line ~pv =
  let pvar_loc = Loc.of_pvar pv ~line in
  if Mem.mem pvar_loc astate.mem then {astate with mem= Mem.remove pvar_loc astate.mem}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_temps astate ~line vars =
  match vars with
  | [(Var.ProgramVar _ as var)] ->
      {astate with temps_to_remove= Vars.add var astate.temps_to_remove}
  | _ ->
      (* remove temps at next EXIT_SCORE to maintain register information at node level *)
      let astate_temps_removed =
        Vars.fold
          (fun var astate' ->
            match var with
            | Var.LogicalVar id ->
                remove_id astate' id
            | Var.ProgramVar pv ->
                remove_pvar astate' ~line ~pv)
          astate.temps_to_remove astate
      in
      {astate_temps_removed with temps_to_remove= Vars.of_list vars}


let remove_locals astate ~pdesc =
  let pname = Procdesc.get_proc_name pdesc in
  let ret_var = Procdesc.get_ret_var pdesc in
  let formal_pvars = Procdesc.get_pvar_formals pdesc |> List.map ~f:fst in
  let locals = Procdesc.get_locals pdesc |> List.map ~f:(fun ProcAttributes.{name} -> Pvar.mk name pname) in
  List.fold ((ret_var :: formal_pvars) @ locals) ~init:astate ~f:(fun acc pv -> remove_pvar acc ~line:0 ~pv)


let replace_value astate ~(src : Val.t) ~(dst : Val.t) =
  let pc_replace_value pc ~src ~dst = debug_time "pc_replace" ~f:(PC.replace_value ~src ~dst) ~arg:pc in
  let mem_replace_value mem =
    debug_time "mem_replace"
      ~f:(fun mem ->
        match (src, dst) with
        | Vheap a, Vheap b ->
            Mem.fold
              (fun l v -> Mem.strong_update (Loc.replace_heap l ~src:a ~dst:b) (Val.replace_sub v ~src ~dst))
              mem Mem.empty
        | _ ->
            Mem.map (Val.replace_sub ~src ~dst) mem)
      ~arg:mem
  in
  let pc' = pc_replace_value astate.pc ~src ~dst in
  let mem' = mem_replace_value astate.mem in
  let reg' = Reg.map (Val.replace_sub ~src ~dst) astate.reg in
  let nullptrs' = Val.Set.map (Val.replace_sub ~src ~dst) astate.nullptrs in
  let uncaught_npes' = List.map ~f:(Val.replace_sub ~src ~dst) astate.uncaught_npes in
  {astate with pc= pc'; mem= mem'; reg= reg'; nullptrs= nullptrs'; uncaught_npes= uncaught_npes'}


let add_pc_simple ?(is_branch = false) astate pathcond : t =
  let pathcond_to_add = PathCond.normalize pathcond in
  if PC.is_valid pathcond_to_add astate.pc then astate
  else
    let pc' = PC.add ~is_branch pathcond_to_add astate.pc in
    {astate with pc= pc'}


let add_pc ?(is_branch = false) astate pathcond : t list =
  let replace_extern astate pc_set =
    (* HEURISTICS: replace an extern variable ex by v if there exists ex1 = ex2 or exn(ex) = exn(ex2) *)
    PC.PCSet.fold
      (fun cond astate_acc ->
        match cond with
        | PathCond.PEquals (x, y) when Val.is_extern x && (not (Val.is_const_extern x)) && Val.is_constant y ->
            replace_value astate_acc ~src:x ~dst:(Val.make_const_extern y)
        | PathCond.PEquals (x, y) when Val.is_extern y && (not (Val.is_const_extern y)) && Val.is_constant x ->
            replace_value astate_acc ~src:y ~dst:(Val.make_const_extern x)
        | PathCond.PEquals ((Val.Vint (SymExp.Extern _) as x), (Val.Vint (SymExp.Extern _) as y)) ->
            if Val.is_const_extern x then replace_value astate_acc ~src:y ~dst:x
            else replace_value astate_acc ~src:x ~dst:y
        | PathCond.PEquals ((Val.Vheap (SymHeap.Extern _) as x), (Val.Vheap (SymHeap.Extern _) as y))
        | PathCond.PEquals
            (Val.Vexn (Val.Vheap (SymHeap.Extern _) as x), Val.Vexn (Val.Vheap (SymHeap.Extern _) as y)) ->
            if Val.is_const_extern x then replace_value astate_acc ~src:y ~dst:x
            else replace_value astate_acc ~src:x ~dst:y
        | _ ->
            astate_acc)
      pc_set astate
  in
  let pathcond_to_add = PathCond.normalize pathcond in
  if PC.is_valid pathcond_to_add astate.pc then (* Avoid overwritting modelNull by normalNull *)
    [astate]
  else
    let pc' = PC.add ~is_branch pathcond_to_add astate.pc in
    if PC.is_invalid pc' then [] else [replace_extern {astate with pc= pc'} (PC.to_pc_set pc')]


let mark_npe_alternative astate = {astate with is_npe_alternative= true}

let set_exception astate = {astate with is_exceptional= true}

let unwrap_exception astate = {astate with is_exceptional= false}

let set_fault astate ~nullpoint = {astate with fault= Some nullpoint}

let set_uncaught_npes astate nullptrs =
  { astate with
    uncaught_npes=
      List.fold nullptrs ~init:astate.uncaught_npes ~f:(fun acc v ->
          if List.mem astate.uncaught_npes v ~equal:phys_equal then acc else v :: acc) }


let get_nullptrs astate = astate.nullptrs

let set_nullptrs astate vals = {astate with nullptrs= Val.Set.union vals astate.nullptrs}

let add_executed_proc astate proc = {astate with executed_procs= Procname.Set.add proc astate.executed_procs}

(* Symbolic domain *)
let resolve_unknown_loc astate typ loc : t =
  if is_unknown_loc astate loc then
    match Val.symbol_from_loc_opt typ loc with
    | Some symval ->
        let mem' = Mem.strong_update loc symval astate.mem in
        {astate with mem= mem'}
    | None ->
        (* too complex symbol *)
        store_loc astate loc (Val.make_extern (Node.dummy_of_proc astate.current_proc) typ)
  else astate


let bind_exn_extern astate instr_node ret_var callee arg_values =
  (* return -> Exn extern
     Exn extern = callee(arg_values) *)
  let ret_loc = Loc.of_pvar ret_var in
  let value = Val.make_extern instr_node Typ.void_star |> Val.to_exn in
  let arg_values =
    List.map arg_values ~f:(fun v ->
        match List.find (equal_values astate v) ~f:Val.is_constant with Some v' -> v' | None -> v)
  in
  let call_value = Val.Vextern (callee, arg_values) in
  let call_cond = PathCond.make_physical_equals Binop.Eq value call_value in
  let astate_reg_stored = store_loc astate ret_loc value |> set_exception in
  add_pc astate_reg_stored call_cond


let bind_extern_value astate instr_node ret_typ_id callee arg_values =
  (* ret_id -> extern
     extern = callee(arg_values) *)
  let ret_id, ret_typ = ret_typ_id in
  let value = Val.make_extern instr_node ret_typ in
  let arg_values =
    List.map arg_values ~f:(fun v ->
        match List.find (equal_values astate v) ~f:Val.is_constant with Some v' -> v' | None -> v)
  in
  let call_value = Val.Vextern (callee, arg_values) in
  let call_cond = PathCond.make_physical_equals Binop.Eq value call_value in
  let astate_reg_stored = store_reg astate ret_id value in
  add_pc astate_reg_stored call_cond


let init proc_desc : t =
  let formals = Procdesc.get_pvar_formals proc_desc in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let init_with_formals =
    List.fold formals ~init:bottom ~f:(fun astate (pv, typ) -> resolve_unknown_loc astate typ (Loc.of_pvar pv))
  in
  let init_with_executed_procs =
    {init_with_formals with executed_procs= Procname.Set.singleton proc_name; current_proc= proc_name}
  in
  match List.find formals ~f:(fun (pv, _) -> Pvar.is_this pv) with
  | Some (this_pvar, _) ->
      let null = Val.make_null (Node.of_pnode (Procdesc.get_start_node proc_desc) Sil.skip_instr) in
      let this_value = read_loc init_with_executed_procs (Loc.of_pvar this_pvar) in
      {init_with_executed_procs with pc= PC.add (PathCond.make_physical_equals Binop.Ne null this_value) PC.empty}
  | None ->
      init_with_executed_procs


let append_ctx astate offset =
  let reg = Reg.map (Val.append_ctx ~offset) astate.reg in
  let mem =
    Mem.fold
      (fun l v -> Mem.strong_update (Loc.append_ctx ~offset l) (Val.append_ctx ~offset v))
      astate.mem Mem.empty
  in
  let pc = PC.replace_by_map ~f:(Val.append_ctx ~offset) astate.pc in
  let nullptrs = Val.Set.map (Val.append_ctx ~offset) astate.nullptrs in
  let uncaught_npes = List.map ~f:(Val.append_ctx ~offset) astate.uncaught_npes in
  {astate with reg; mem; pc; nullptrs; uncaught_npes}


let add_model astate pos mval =
  match NullModel.find_opt pos astate.applied_models with
  | Some mvals when NullModel.MValueSet.equal mvals (NullModel.MValueSet.singleton mval) ->
      [astate]
  | Some _ ->
      L.d_printfln " - model %a is not appliable" NullModel.MValue.pp mval ;
      []
  | None ->
      [ { astate with
          applied_models= NullModel.add_element pos mval astate.applied_models
        ; probability= NullModel.compute_probability astate.applied_models } ]


(** Summary resolve *)
module SymResolvedMap = struct
  include PrettyPrintable.MakePPMonoMap (SymDom.Symbol) (Val)

  let find k t =
    try find k t
    with _ ->
      raise (Unexpected (F.asprintf "%a is not resolved...@.current sym_resolved_map : %a@." Symbol.pp k pp t))


  let rec resolve_loc sym_resolved_map = function
    | Loc.SymHeap sheap -> (
      match resolve_symheap sym_resolved_map sheap with
      | Val.Vheap sh ->
          Loc.SymHeap sh
      | Val.Vint (Symbol s) ->
          Loc.SymHeap (SymHeap.Symbol s)
      | _ as v ->
          raise (Unexpected (F.asprintf "%a is cannot resolved as loc" Val.pp v)) )
    | Loc.Field (l, fn) ->
        Loc.Field (resolve_loc sym_resolved_map l, fn)
    | Loc.Index (l, s) ->
        Loc.Index (resolve_loc sym_resolved_map l, s)
    | (Loc.TempVar _ | Loc.IllTempVar _ | Loc.Var _) as l ->
        l


  and resolve_symheap sym_resolved_map = function
    | SymHeap.Symbol s when not (mem s sym_resolved_map) ->
        raise (Unexpected (F.asprintf "%a is not resolved" SymDom.Symbol.pp s))
    | SymHeap.Symbol s ->
        find s sym_resolved_map
    | (SymHeap.Allocsite _ | SymHeap.String _ | SymHeap.Null _) as sheap ->
        Val.Vheap sheap
    | SymHeap.Extern _ as sheap ->
        Val.Vheap sheap
    | SymHeap.Unknown as s ->
        (* TODO: some extern values are required at caller *)
        Val.Vheap s


  let rec resolve_val sym_resolved_map = function
    | Val.Vint symexp ->
        resolve_symexp sym_resolved_map symexp
    | Val.Vheap sheap ->
        resolve_symheap sym_resolved_map sheap
    | Val.Vexn v ->
        Val.Vexn (resolve_val sym_resolved_map v)
    | Val.Vextern _ ->
        Val.top
    | _ as v ->
        v


  and resolve_symexp sym_resolved_map = function
    | SymExp.Symbol s when not (mem s sym_resolved_map) ->
        raise (Unexpected (F.asprintf "%a is not resolved" SymDom.Symbol.pp s))
    | SymExp.Symbol s ->
        find s sym_resolved_map
    | SymExp.Extern _ as symexp ->
        Val.Vint symexp
    | _ as x ->
        (* TODO: s1 + s2 -> resolve(s1) + resolve(s2) *)
        Val.Vint x


  let construct astate callee_state init =
    let symvals_to_resolve = all_symbols callee_state in
    let compare v1 v2 =
      let _length = function
        | Val.Vint (SymExp.Symbol (_, accesses)) | Val.Vheap (SymHeap.Symbol (_, accesses)) ->
            List.length accesses
        | _ ->
            L.(die InternalError) "nonono"
      in
      _length v1 - _length v2
    in
    let symvals = List.sort (Val.Set.elements symvals_to_resolve) ~compare in
    let update_resolved_loc s typ resolved_loc acc =
      if is_unknown_loc astate resolved_loc then
        match Val.symbol_from_loc_opt typ resolved_loc with
        | Some symval ->
            add s symval acc
        | None ->
            (* Unknown may introduced here *)
            add s (Val.make_extern (Node.dummy_of_proc astate.current_proc) typ) acc
      else add s (Mem.find resolved_loc astate.mem) acc
    in
    List.fold symvals ~init ~f:(fun acc v ->
        let typ, (base, accesses) =
          match v with
          | Val.Vint (SymExp.Symbol s) ->
              (Typ.int, s)
          | Val.Vheap (SymHeap.Symbol s) ->
              (Typ.void_star, s)
          | _ ->
              L.(die InternalError) "nonono"
        in
        match (base, List.rev accesses) with
        | Symbol.Global (pv, Symbol.Field fn), [] ->
            update_resolved_loc (base, accesses) typ (Loc.of_pvar pv |> Loc.append_field ~fn) acc
        | Symbol.Param _, [] ->
            (* already resolved at init *)
            acc
        | base, Symbol.Field fn :: remain' ->
            let base_loc = find (base, List.rev remain') acc |> Val.to_loc in
            update_resolved_loc (base, accesses) typ (Loc.append_field base_loc ~fn) acc
        | base, Symbol.Index index :: remain' ->
            let base_loc = find (base, List.rev remain') acc |> Val.to_loc in
            let index = SymExp.of_intlit index in
            update_resolved_loc (base, accesses) typ (Loc.append_index base_loc ~index) acc
        | Symbol.Global (_, _), _ ->
            L.(die InternalError) "Invalid symbol: %a@." Symbol.pp (base, accesses))


  let replace_mem sym_resolved_map mem_to_resolve mem_to_update =
    (* replace memory l |-> v by resolved_map (s |-> v) *)
    Mem.fold
      (fun l v -> Mem.strong_update (resolve_loc sym_resolved_map l) (resolve_val sym_resolved_map v))
      mem_to_resolve mem_to_update


  let replace_pc sym_resolved_map pc_to_resolve pc_to_update =
    PC.replace_by_map pc_to_resolve ~f:(resolve_val sym_resolved_map) |> PC.join pc_to_update


  let resolve_nullptrs sym_resolved_map nullptrs_to_resolve nullptrs_to_update =
    Val.Set.fold
      (fun v acc -> Val.Set.add (resolve_val sym_resolved_map v) acc)
      nullptrs_to_resolve nullptrs_to_update


  let resolve_uncaught_npes sym_resolved_map nullptrs_to_resolve nullptrs_to_update =
    List.fold nullptrs_to_resolve ~init:nullptrs_to_update ~f:(fun acc v ->
        let resolved = resolve_val sym_resolved_map v in
        if List.mem acc resolved ~equal:phys_equal then acc else resolved :: acc)
end

let resolve_summary astate ~actual_values ~formals callee_summary =
  let init_sym_resolved_map =
    List.fold2_exn formals actual_values ~init:SymResolvedMap.empty ~f:(fun sym_resolved_map (fv, typ) v ->
        if Typ.is_pointer typ || Typ.is_int typ then SymResolvedMap.add (Symbol.of_pvar fv) v sym_resolved_map
        else sym_resolved_map)
  in
  (* L.progress "[DEBUG]: init sym_resolved_map: %a@." SymResolvedMap.pp init_sym_resolved_map ; *)
  let sym_resolved_map =
    try SymResolvedMap.construct astate callee_summary init_sym_resolved_map
    with Unexpected msg -> L.(die InternalError) "%s@.%a" msg Mem.pp callee_summary.mem
  in
  (* L.d_printfln "[DEBUG]: init sym_resolved_map@. - %a@.====================================@." SymResolvedMap.pp
       init_sym_resolved_map ;
     L.d_printfln "[DEBUG]: sym_resolved_map@. - %a@.====================================@." SymResolvedMap.pp
       sym_resolved_map ; *)
  let mem', pc' =
    try
      ( SymResolvedMap.replace_mem sym_resolved_map callee_summary.mem astate.mem
      , SymResolvedMap.replace_pc sym_resolved_map callee_summary.pc astate.pc )
    with Unexpected msg ->
      (* L.progress
         "[WARING]: Failed to resolve callee memory@. Callee mem : %a@. Init_resolved_map : %a@. Sym_resolved_map \
          : %a@. Caller mem: %a@. Msg: %s@."
         pp callee_summary SymResolvedMap.pp init_sym_resolved_map SymResolvedMap.pp sym_resolved_map pp astate msg ; *)
      (Mem.bottom, PC.invalid)
  in
  let nullptrs' = SymResolvedMap.resolve_nullptrs sym_resolved_map callee_summary.nullptrs astate.nullptrs in
  let uncaught_npes' =
    SymResolvedMap.resolve_uncaught_npes sym_resolved_map callee_summary.uncaught_npes astate.uncaught_npes
  in
  let fault' : NullPoint.t option =
    match (astate.fault, callee_summary.fault) with
    | None, fault_opt ->
        fault_opt
    | Some fault, None ->
        Some fault
    | Some fault, Some _ ->
        (* TODO: this will not be merged *)
        Some fault
  in
  let applied_models' =
    NullModel.union (fun _ l _ -> Some l) astate.applied_models callee_summary.applied_models
  in
  let probability' = NullModel.compute_probability applied_models' in
  let executed_procs' = Procname.Set.union astate.executed_procs callee_summary.executed_procs in
  let astate' =
    { reg= astate.reg
    ; mem= mem'
    ; pc= pc'
    ; is_npe_alternative= callee_summary.is_npe_alternative || astate.is_npe_alternative
    ; is_exceptional= callee_summary.is_exceptional (* since exceptional state cannot execute fuction *)
    ; nullptrs= nullptrs'
    ; fault= fault'
    ; applied_models= applied_models'
    ; probability= probability'
    ; executed_procs= executed_procs'
    ; uncaught_npes= uncaught_npes'
    ; temps_to_remove= astate.temps_to_remove
    ; current_proc= astate.current_proc }
  in
  if PC.is_invalid pc' then (
    L.d_printfln "@.===== Summary is invalidated by pathcond =====@." ;
    L.d_printfln " - resolved state: %a@." pp astate' ;
    L.d_printfln " - callee state: %a@. - symresolved_map: %a@." pp callee_summary SymResolvedMap.pp
      sym_resolved_map ;
    None )
  else if not (NullModel.joinable astate.applied_models callee_summary.applied_models) then (
    (* e.g., p = null; foo(null); foo(null); but apply unjoinable model in foo *)
    L.d_printfln "@.===== Summary is invalidated by applied models =====@." ;
    L.d_printfln " - resolved state: %a@." pp astate' ;
    L.d_printfln " - callee state: %a@. - symresolved_map: %a@." pp callee_summary SymResolvedMap.pp
      sym_resolved_map ;
    None (* None *) )
  else if List.exists uncaught_npes' ~f:(fun v -> List.exists (inequal_values astate' v) ~f:Val.is_null) then (
    (* e.g., v is one of uncaughted NPEs, but v != null in caller state *)
    L.d_printfln "@.===== Summary is invalidated by uncaughted npes =====@." ;
    L.d_printfln " - resolved state: %a@." pp astate' ;
    L.d_printfln " - callee state: %a@. - symresolved_map: %a@." pp callee_summary SymResolvedMap.pp
      sym_resolved_map ;
    None (* None *) )
  else Some astate'


(** Eval functions *)
let eval_uop unop v =
  match unop with
  | Unop.LNot when Val.is_true v ->
      Val.zero
  | Unop.LNot when Val.is_false v ->
      Val.one
  | _ ->
      Val.top


let eval_binop binop v1 v2 =
  match binop with
  | Binop.PlusA _ ->
      Val.add v1 v2
  | Binop.MinusA _ ->
      Val.sub v1 v2
  | Binop.Lt ->
      Val.lt v1 v2
  | Binop.Gt ->
      Val.lt v2 v1
  | Binop.Le ->
      Val.lte v1 v2
  | Binop.Ge ->
      Val.lte v2 v1
  | _ ->
      Val.top


let rec eval ?(pos = 0) astate node instr exp =
  match exp with
  | Exp.Var id when Reg.mem id astate.reg ->
      Reg.find id astate.reg
  | Exp.Var id ->
      L.(die InternalError) "%a is not assigned any value" Ident.pp id
  | Exp.UnOp (unop, e, _) ->
      eval_uop unop (eval astate node instr e ~pos)
  | Exp.BinOp (binop, e1, e2) ->
      let v1 = eval astate node instr e1 ~pos in
      let v2 = eval astate node instr e2 ~pos in
      eval_binop binop v1 v2
  | Exp.Exn e -> (
    try eval astate node instr e |> Val.to_exn with
    | _ when List.is_empty astate.uncaught_npes ->
        (* HEURISTICS: abstract all exn values to exn*)
        Val.exn
    | _ ->
        Val.npe )
  | Exp.Const (Cstr str) ->
      Val.make_string str
  | Exp.Const (Cint intlit) when IntLit.isnull intlit ->
      Val.make_null (Node.of_pnode node instr) ~pos
  | Exp.Const (Cint intlit) ->
      Val.of_intlit intlit
  | Exp.Const (Cfloat flit) ->
      Val.of_float flit
  | Exp.Const (Cclass name) ->
      Val.make_string (Ident.name_to_string name)
  | Exp.Cast (_, e) ->
      eval astate node instr e
  | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ ->
      L.(die InternalError) "%a is not allowed as rvalue in java" Exp.pp exp
  | Exp.Closure _ | Exp.Sizeof _ | Exp.Const (Cfun _) ->
      Val.top


let rec eval_lv astate node instr exp =
  match exp with
  | Exp.Var id when Reg.mem id astate.reg -> (
    match Reg.find id astate.reg with
    | Val.Vheap h ->
        Loc.SymHeap h
    | Val.Top ->
        L.progress "[WARNING]: lvalue expression %a is evaluated to top" Exp.pp exp ;
        Loc.unknown
    | _ as v ->
        L.progress "[WARNING]: lvalue expression %a is evaluated to %a" Exp.pp exp Val.pp v ;
        Loc.unknown
        (* L.(die InternalError) "lvalue expression %a cannot be evaluated to %a" Exp.pp exp Val.pp v ) *) )
  | Exp.Var id ->
      L.(die InternalError) "%a is not loaded to reg" Ident.pp id
  | Exp.Const (Cstr str) ->
      Loc.make_string str
  | Exp.Cast (_, e) ->
      eval_lv astate node instr e
  | Exp.Lindex (e1, e2) ->
      let index = eval astate node instr e2 |> Val.to_symexp in
      eval_lv astate node instr e1 |> Loc.append_index ~index
  | Exp.Lvar pv ->
      Loc.of_pvar pv ~line:(get_line node)
  | Exp.Lfield (e, fn, _) ->
      eval_lv astate node instr e |> Loc.append_field ~fn
  | Exp.Const (Cclass name) ->
      (* value of the class variable is unknown, so init by global *)
      Loc.make_string (Ident.name_to_string name)
      (* let cls_name = Ident.name_to_string cls in
         let cls_var = Pvar.mk_global (Mangled.from_string cls_name) in
         Loc.of_pvar cls_var *)
  | _ ->
      L.(die InternalError) "%a is not allowed as lvalue expression in java" Exp.pp exp


(** remove unreachable *)
let compute_reachables_from ({mem} as astate) =
  let pc_relevant v = equal_values astate v @ inequal_values astate v in
  let pointsto_val =
    Mem.fold
      (fun l v acc ->
        match l with
        | Loc.Var pv when Pvar.is_return pv ->
            Val.Set.add v acc
        | (Loc.Field (Loc.Var gv, _) | Loc.Index (Loc.Var gv, _)) when Pvar.is_global gv ->
            Val.Set.add v acc
        | (Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _)) when SymHeap.is_symbolic sh ->
            Val.Set.add (Val.Vheap sh) acc |> Val.Set.add v
        | _ when Val.is_symbolic v ->
            Val.Set.add v acc
        | _ ->
            acc)
      mem Val.Set.empty
  in
  Val.Set.elements pointsto_val
  |> List.concat_map ~f:pc_relevant
  |> List.concat_map ~f:Val.get_subvalues
  |> Val.Set.of_list


let remove_unreachables ({mem; pc} as astate) =
  let all_heaps =
    all_values astate |> Val.Set.elements |> List.concat_map ~f:Val.get_subvalues |> Val.Set.of_list
  in
  let reachable_heaps = compute_reachables_from astate in
  let unreachable_heaps = Val.Set.diff all_heaps reachable_heaps in
  let is_unreachable_value v =
    List.exists (Val.get_subvalues v) ~f:(fun subval -> Val.Set.mem subval unreachable_heaps)
  in
  let is_reachable_loc = function
    | (Loc.Field (Loc.SymHeap sh, _) | Loc.Index (Loc.SymHeap sh, _))
      when Val.Set.mem (Val.Vheap sh) unreachable_heaps ->
        false
    | _ ->
        true
  in
  let mem' =
    Mem.filter
      (fun l v ->
        if (not (is_reachable_loc l)) || is_unreachable_value v then false
        else
          match (Loc.to_symbol_opt l, Val.get_symbol_opt v) with
          | Some s, Some s' when SymDom.Symbol.equal s s' ->
              (* L.progress "is equal %a, %a? %b@." Symbol.pp s Symbol.pp s' (Symbol.equal s s') ; *)
              false
          | Some _, None ->
              true
          | None, _ when Val.is_top v ->
              false
          | _ ->
              true)
      mem
  in
  let pc' =
    PC.filter_by_value ~f:(fun v -> List.exists (Val.get_subvalues v) ~f:(not <<< is_unreachable_value)) pc
  in
  let nullptrs' = Val.Set.filter (not <<< is_unreachable_value) astate.nullptrs in
  let uncaught_npes' = List.filter ~f:(not <<< is_unreachable_value) astate.uncaught_npes in
  {astate with mem= mem'; pc= pc'; nullptrs= nullptrs'; uncaught_npes= uncaught_npes'}


(** For Join *)
let unify lhs rhs : t * t =
  let all_locs =
    (* TODO: unify non-memory symbols? or guarantee all symbols are in memory *)
    Mem.fold (fun l _ acc -> l :: acc) lhs.mem []
  in
  let extern_locs, concrete_locs =
    List.partition_tf all_locs ~f:(fun l -> Loc.is_extern l || Loc.is_allocsite l)
  in
  let add_pc_simple astate pathcond = debug_time "add_pc_simple" ~f:(add_pc_simple astate) ~arg:pathcond in
  let replace_value astate ~src ~dst = debug_time "replace_value" ~f:(replace_value ~src ~dst) ~arg:astate in
  let replace_astate astate l v new_value introduced =
    match v with
    | Val.Vexn v' ->
        if Val.Set.mem v' introduced then
          add_pc_simple
            (store_loc astate l (Val.to_exn new_value))
            (PathCond.make_physical_equals Binop.Eq v' new_value)
        else replace_value astate ~src:v' ~dst:new_value
    | _ ->
        if Val.Set.mem v introduced then
          add_pc_simple (store_loc astate l new_value) (PathCond.make_physical_equals Binop.Eq v new_value)
        else if Val.is_allocsite v then
          add_pc_simple
            (replace_value astate ~src:v ~dst:new_value)
            (PathCond.make_physical_equals Binop.Ne new_value Val.default_null)
        else replace_value astate ~src:v ~dst:new_value
  in
  let replace_astate astate l v new_value introduced =
    debug_time "replace_astate" ~f:(replace_astate astate l v new_value) ~arg:introduced
  in
  let make_extern = Val.make_extern (Node.dummy_of_proc lhs.current_proc) in
  let rec _unify worklist rest (lhs, rhs) =
    let add v vals = debug_time "Set" ~f:(Val.Set.add v) ~arg:vals in
    let mem v vals = debug_time "Set" ~f:(Val.Set.mem v) ~arg:vals in
    let mem_mem l mem = debug_time "Mem" ~f:(Mem.mem l) ~arg:mem in
    let equal v1 v2 = debug_time "Equal" ~f:(Val.equal v1) ~arg:v2 in
    let find l mem = debug_time "find" ~f:(Mem.find l) ~arg:mem in
    (* let add = Val.Set.add in
       let mem = Val.Set.mem in
       let mem_mem = Mem.mem in
       let equal = Val.equal in
       let find = Mem.find in *)
    let f (vals, lhs, rhs, introduced) l =
      if mem_mem l rhs.mem then
        let v_lhs, v_rhs = (find l lhs.mem, find l rhs.mem) in
        match (v_lhs, v_rhs) with
        | _, _ when equal v_lhs v_rhs ->
            (add v_lhs vals, lhs, rhs, add v_lhs introduced)
        (* | _, _ when Val.is_const_extern v_lhs && Val.is_const_extern v_rhs ->
           (vals, lhs, rhs, introduced) *)
        | Val.Vint x, Val.Vint y when SymExp.is_top x || SymExp.is_top y ->
            (vals, lhs, rhs, introduced)
        | Val.Vheap x, Val.Vheap y when SymHeap.is_unknown x || SymHeap.is_unknown y ->
            (vals, lhs, rhs, introduced)
        | Val.Vint _, Val.Vint _ ->
            let new_value = make_extern Typ.int in
            ( vals
            , replace_astate lhs l v_lhs new_value introduced
            , replace_astate rhs l v_rhs new_value introduced
            , add new_value introduced )
        | Val.Vheap _, Val.Vheap _ ->
            let new_value = make_extern Typ.void_star in
            ( add new_value vals
            , replace_astate lhs l v_lhs new_value introduced
            , replace_astate rhs l v_rhs new_value introduced
            , add new_value introduced )
        | Vexn _, Vexn _ ->
            let new_value = make_extern Typ.void_star in
            (* exception heap cannot points-to something *)
            ( vals
            , replace_astate lhs l v_lhs new_value introduced
            , replace_astate rhs l v_rhs new_value introduced
            , add new_value introduced )
        | Vextern _, _ ->
            (* uninterpretted function term is not in memory *)
            (vals, lhs, rhs, introduced)
        | _, _ ->
            (vals, lhs, rhs, introduced)
      else (vals, lhs, rhs, introduced)
    in
    (* TODO: fix scalability issues *)
    let next_vals, next_lhs, next_rhs, _ =
      List.fold worklist ~init:(Val.Set.empty, lhs, rhs, Val.Set.empty) ~f:(fun acc l ->
          debug_time "loop_f" ~f:(f acc) ~arg:l)
      (* let v_lhs = Mem.find l lhs.mem in
         if is_node_value (Mem.find l lhs.mem) then
           let v_rhs = Mem.find l rhs.mem in
           if Val.equal v_lhs v_rhs then (Val.Set.add v_lhs nexts, rhs)
           else if is_node_value v_rhs then (Val.Set.add v_lhs nexts, replace_value rhs ~src:v_rhs ~dst:v_lhs)
           else (nexts, rhs)
         else (nexts, rhs)) *)
    in
    let partition_tf lst ~f = debug_time "partition" ~f:(List.partition_tf ~f) ~arg:lst in
    let next_worklist, next_rest =
      partition_tf rest ~f:(Loc.is_rec ~f:(function Loc.SymHeap sh -> mem (Val.Vheap sh) next_vals | _ -> false))
    in
    if List.is_empty next_worklist then (next_lhs, next_rhs)
    else _unify next_worklist next_rest (next_lhs, next_rhs)
  in
  let _unify concrete_locs extern_locs (lhs, rhs) =
    debug_time "_unify" ~f:(_unify concrete_locs extern_locs) ~arg:(lhs, rhs)
  in
  (* TODO: replace variable first *)
  _unify concrete_locs extern_locs (lhs, rhs)


let unify lhs rhs = debug_time "Unify" ~f:(unify lhs) ~arg:rhs

let get_null_locs astate =
  Mem.fold
    (fun l v acc ->
      if (Loc.is_var l || Val.is_symbolic v) && List.exists (equal_values astate v) ~f:Val.is_null then
        Loc.Set.add l acc
      else acc)
    astate.mem Loc.Set.empty


let collect_summary_symbols astate =
  (* TODO: HEURISTICS *)
  Mem.fold
    (fun l v acc ->
      match (l, v) with
      | (Loc.Field _, Val.Vint (Symbol s) | Loc.Index _, Val.Vint (Symbol s)) when Symbol.is_pvar s ->
          Val.Set.add v acc
      | _ ->
          acc)
    astate.mem Val.Set.empty


let joinable lhs rhs =
  let has_const_diff_value lhs rhs =
    let is_important = Val.is_null in
    Mem.exists
      (fun l v ->
        (not (Loc.is_extern l))
        &&
        (* Loc.is_concrete l
           && *)
        (* let equal_values_lhs, inequal_values_lhs = equal_values lhs v, inequal_values lhs v in
           let equal_values_rhs, inequal_values_rhs = equal_values rhs v, inequal_values rhs v in *)
        match List.find (equal_values lhs v) ~f:is_important with
        | Some v -> (
          match List.find (equal_values rhs (Mem.find l rhs.mem)) ~f:is_important with
          | Some v' ->
              not (Val.equal v v')
          | None -> (
            match List.find (inequal_values rhs (Mem.find l rhs.mem)) ~f:is_important with
            | Some v' ->
                Val.equal v v'
            | None ->
                false ) )
        | None -> (
          match List.find (inequal_values lhs v) ~f:is_important with
          | Some v -> (
            match List.find (equal_values rhs (Mem.find l rhs.mem)) ~f:is_important with
            | Some v' ->
                Val.equal v v'
            | None ->
                false )
          | None ->
              false ))
      lhs.mem
  in
  let has_no_significant_diff lhs rhs =
    if Config.npex_launch_localize then true
    else
      (* Loc.Set.equal (get_null_locs lhs) (get_null_locs rhs) *)
      Val.Set.equal (collect_summary_symbols lhs) (collect_summary_symbols rhs)
      &&
      let lhs, rhs = unify lhs rhs in
      not (has_const_diff_value lhs rhs)
    (* && not (has_const_diff_value lhs (unify ~base:lhs rhs)) *)
    (* let rhs = unify ~base:lhs rhs in
       let satisfiable lhs rhs = PC.check_sat lhs.pc rhs.pc in
       satisfiable lhs rhs *)
  in
  Bool.equal lhs.is_npe_alternative rhs.is_npe_alternative
  && Bool.equal lhs.is_exceptional rhs.is_exceptional
  && Bool.equal (has_uncaught_npes lhs) (has_uncaught_npes rhs)
  && NullModel.joinable lhs.applied_models rhs.applied_models
  && Option.equal NullPoint.equal lhs.fault rhs.fault
  && has_no_significant_diff lhs rhs


let joinable lhs rhs = debug_time "Joinable" ~f:(joinable lhs) ~arg:rhs

let weak_join lhs rhs : t =
  (* Assumption: lhs and rhs are joinable *)
  if phys_equal lhs rhs then (
    L.d_printfln "Two state are pyhsical equal" ;
    lhs )
  else if is_bottom lhs then (L.d_printfln "Right state is bottom" ; rhs)
  else if is_bottom rhs then (L.d_printfln "Left state is bottom" ; lhs)
  else (
    L.d_printfln " - Before Join - " ;
    L.d_printfln "Left@.%a@.Right@.%a@." pp lhs pp rhs ;
    let lhs, rhs = unify lhs rhs in
    L.d_printfln " - Unified Left - @.%a@." pp lhs ;
    L.d_printfln " - Unified Right - @.%a@." pp rhs ;
    let reg = Reg.weak_join ~lhs:lhs.reg ~rhs:rhs.reg in
    let mem = Mem.weak_join ~lhs:lhs.mem ~rhs:rhs.mem in
    let pc = PC.weak_join ~lhs:lhs.pc ~rhs:rhs.pc in
    let applied_models = NullModel.weak_join ~lhs:lhs.applied_models ~rhs:rhs.applied_models in
    let probability = NullModel.compute_probability applied_models in
    let is_npe_alternative = lhs.is_npe_alternative || rhs.is_npe_alternative in
    let is_exceptional = lhs.is_exceptional || rhs.is_exceptional in
    let fault = lhs.fault (* since lhs.fault = rhs.fault *) in
    let nullptrs = Val.Set.union lhs.nullptrs rhs.nullptrs in
    let executed_procs = Procname.Set.union lhs.executed_procs rhs.executed_procs in
    let uncaught_npes =
      List.fold rhs.uncaught_npes ~init:lhs.uncaught_npes ~f:(fun acc null ->
          if List.mem acc ~equal:phys_equal null then acc else null :: acc)
    in
    let temps_to_remove = Vars.union lhs.temps_to_remove rhs.temps_to_remove in
    let joined =
      { reg
      ; mem
      ; pc
      ; applied_models
      ; probability
      ; is_npe_alternative
      ; is_exceptional
      ; fault
      ; nullptrs
      ; executed_procs
      ; uncaught_npes
      ; temps_to_remove
      ; current_proc= lhs.current_proc }
    in
    L.d_printfln " - Joined - @.%a@." pp joined ;
    joined )


module Feature = struct
  type t = {is_npe_alternative: bool; is_exceptional: bool; fault: NullPoint.t option; has_uncaught_exception: bool}
  [@@deriving compare]

  let pp fmt x =
    F.fprintf fmt "%b:%b:%a:%b" x.is_npe_alternative x.is_exceptional (Pp.option NullPoint.pp) x.fault
      x.has_uncaught_exception
end

module FeatureMap = PrettyPrintable.MakePPMap (Feature)

let merge disjuncts =
  let add_state (feature_map : t list FeatureMap.t) (state : t) =
    let feature =
      Feature.
        { is_npe_alternative= state.is_npe_alternative
        ; is_exceptional= state.is_exceptional
        ; fault= state.fault
        ; has_uncaught_exception= has_uncaught_npes state }
    in
    match FeatureMap.find_opt feature feature_map with
    | Some states ->
        FeatureMap.add feature (state :: states) feature_map
    | None ->
        FeatureMap.add feature [state] feature_map
  in
  let feature_partitioned = List.fold disjuncts ~init:FeatureMap.empty ~f:add_state in
  let rec _merge worklist acc =
    match worklist with
    | [] ->
        acc
    | hd :: tl ->
        let joinable, unjoinable = List.partition_tf tl ~f:(joinable hd) in
        if List.is_empty joinable then _merge tl (hd :: acc)
        else
          let joinable' = List.map joinable ~f:(weak_join hd) in
          _merge (joinable' @ unjoinable) acc
  in
  FeatureMap.fold (fun _ disjuncts -> _merge disjuncts) feature_partitioned []


let merge disjuncts = debug_time "Merge" ~f:merge ~arg:disjuncts
