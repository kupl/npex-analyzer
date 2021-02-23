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
module Reg = WeakMap.Make (Ident) (Val)

module Mem = struct
  include WeakMap.Make (Loc) (Val)
end

type t = {reg: Reg.t; mem: Mem.t; pc: PC.t; is_npe_alternative: bool; is_exceptional: bool}

let pp fmt {reg; mem; pc; is_npe_alternative; is_exceptional} =
  F.fprintf fmt
    "@[<v 2> - Register:@,\
    \ %a@]@. @[<v 2> - Memory:@,\
    \ %a@]@. @[<v 2> - Path Conditions:@,\
    \ %a@]@. @[<v 2> - Is NPE Alternative? Is Exceptional?@,\
    \ %b,%b@]@." Reg.pp reg Mem.pp mem PC.pp pc is_npe_alternative is_exceptional


let leq ~lhs ~rhs = phys_equal lhs rhs

let bottom = {reg= Reg.bottom; mem= Mem.bottom; pc= PC.empty; is_npe_alternative= false; is_exceptional= false}

let fold_memory {mem} ~init ~f = Mem.fold (fun l v acc -> f acc l v) mem init

(* type get_summary = Procname.t -> t option *)

(* Basic Queries *)

let is_unknown_loc {mem} l = Loc.is_unknown l || not (Mem.mem l mem)

let is_unknown_id {reg} id = Val.is_bottom (Reg.find id reg)

let is_exceptional {is_exceptional} = is_exceptional

let is_npe_alternative {is_npe_alternative} = is_npe_alternative

let is_valid_pc astate pathcond = PC.is_valid pathcond astate.pc

(* Read & Write *)
let read_loc {mem} l = Mem.find l mem

let read_id {reg} id = Reg.find id reg

let equal_values astate v = PC.equal_values astate.pc v

let inequal_values astate v = PC.inequal_values astate.pc v

let store_loc astate l v : t = {astate with mem= Mem.strong_update l v astate.mem}

let store_reg astate id v = {astate with reg= Reg.strong_update id v astate.reg}

let remove_id astate id =
  if Reg.mem id astate.reg then {astate with reg= Reg.remove id astate.reg}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_pvar astate ~line ~pv =
  let pvar_loc = Loc.of_pvar pv ~line in
  if Mem.mem pvar_loc astate.mem then {astate with mem= Mem.remove pvar_loc astate.mem}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_locals astate ~locals =
  List.fold locals ~init:astate ~f:(fun acc pv -> (* No temp variables in summary *)
                                                  remove_pvar acc ~line:0 ~pv)


let remove_temps astate ~line vars =
  List.fold vars ~init:astate ~f:(fun astate' var ->
      match var with
      | Var.LogicalVar id ->
          remove_id astate' id
      | Var.ProgramVar pv ->
          remove_pvar astate' ~line ~pv)


let add_pc astate pathcond : t list =
  let pc' = PC.add pathcond astate.pc in
  if PC.is_invalid pc' then [] else [{astate with pc= pc'}]


let mark_npe_alternative astate = {astate with is_npe_alternative= true}

let set_exception astate = {astate with is_exceptional= true}

let unwrap_exception astate = {astate with is_exceptional= false}

let replace_value astate ~(src : Val.t) ~(dst : Val.t) =
  let pc' = PC.replace_value astate.pc ~src ~dst in
  let mem' = Mem.map (fun v -> if phys_equal v src then dst else v) astate.mem in
  let reg' = Reg.map (fun v -> if phys_equal v src then dst else v) astate.reg in
  {astate with pc= pc'; mem= mem'; reg= reg'}


(* Symbolic domain *)
let resolve_unknown_loc astate typ loc : t =
  match Val.symbol_from_loc_opt typ loc with
  | Some symval ->
      let mem' = Mem.add loc symval astate.mem in
      {astate with mem= mem'}
  | None ->
      store_loc astate loc (Val.of_typ typ)


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


(* Summary resolve *)
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
    | Val.Vexn sheap ->
        resolve_symheap sym_resolved_map sheap |> Val.to_exn
    | Val.Vextern _ ->
        Val.top
    | _ as v ->
        v


  and resolve_symexp sym_resolved_map = function
    | SymExp.Symbol s when not (mem s sym_resolved_map) ->
        raise (Unexpected (F.asprintf "%a is not resolved" SymDom.Symbol.pp s))
    | SymExp.Symbol s ->
        find s sym_resolved_map
    | _ as x ->
        (* TODO: s1 + s2 -> resolve(s1) + resolve(s2) *)
        Val.Vint x


  let construct astate callee_state init =
    let symvals_to_resolve =
      let add_if_symbol v acc_symvals =
        match v with
        | Val.Vint (SymExp.Symbol _) ->
            Val.Set.add v acc_symvals
        | Val.Vheap (SymHeap.Symbol _) ->
            Val.Set.add v acc_symvals
        | _ ->
            acc_symvals
      in
      Mem.fold (fun _ v acc_symvals -> add_if_symbol v acc_symvals) callee_state.mem Val.Set.empty
      |> PC.PCSet.fold
           (fun cond acc_symvals ->
             match cond with
             | PathCond.PEquals (v1, v2)
             | PathCond.Equals (v1, v2)
             | PathCond.Not (PathCond.PEquals (v1, v2))
             | PathCond.Not (PathCond.Equals (v1, v2)) ->
                 add_if_symbol v1 acc_symvals |> add_if_symbol v2
             | _ ->
                 L.(die InternalError) "Invalid path-codition : %a@." PathCond.pp cond)
           (PC.to_pc_set callee_state.pc)
    in
    let symvals = List.sort (Val.Set.elements symvals_to_resolve) ~compare:Val.compare in
    let update_resolved_loc s typ resolved_loc acc =
      if is_unknown_loc astate resolved_loc then
        match Val.symbol_from_loc_opt typ resolved_loc with
        | Some symval ->
            add s symval acc
        | None ->
            add s (Val.of_typ typ) acc
      else add s (read_loc astate resolved_loc) acc
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
        | Symbol.Param pv, [] ->
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


  let rec resolve_pc sym_resolved_map = function
    | PathCond.PEquals (v1, v2) ->
        PathCond.PEquals (resolve_val sym_resolved_map v1, resolve_val sym_resolved_map v2)
    | PathCond.Not pc ->
        PathCond.Not (resolve_pc sym_resolved_map pc)
    | PathCond.Equals (v1, v2) ->
        PathCond.Equals (resolve_val sym_resolved_map v1, resolve_val sym_resolved_map v2)


  let replace_mem sym_resolved_map mem_to_resolve mem_to_update =
    (* replace memory l |-> v by resolved_map (s |-> v) *)
    Mem.fold
      (fun l v -> Mem.add (resolve_loc sym_resolved_map l) (resolve_val sym_resolved_map v))
      mem_to_resolve mem_to_update


  let replace_pc sym_resolved_map pc_to_resolve pc_to_update =
    PC.replace_by_map pc_to_resolve ~f:(resolve_val sym_resolved_map) |> PC.join pc_to_update
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
  L.d_printfln "[DEBUG]: init sym_resolved_map@. - %a@.====================================@." SymResolvedMap.pp
    init_sym_resolved_map ;
  L.d_printfln "[DEBUG]: sym_resolved_map@. - %a@.====================================@." SymResolvedMap.pp
    sym_resolved_map ;
  let mem', pc' =
    try
      ( SymResolvedMap.replace_mem sym_resolved_map callee_summary.mem astate.mem
      , SymResolvedMap.replace_pc sym_resolved_map callee_summary.pc astate.pc )
    with Unexpected msg ->
      L.(die InternalError)
        "Failed to resolve callee memory@. Callee mem : %a@. Init_resolved_map : %a@. Sym_resolved_map : %a@. \
         Caller mem: %a@. Msg: %s@."
        pp callee_summary SymResolvedMap.pp init_sym_resolved_map SymResolvedMap.pp sym_resolved_map pp astate msg
  in
  if PC.is_invalid pc' then (
    L.d_printfln " - memory: %a@. - invalid pc: %a@." Mem.pp mem' PC.pp pc' ;
    L.d_printfln " - original pc: %a@. - symresolved_map: %a@." PC.pp callee_summary.pc SymResolvedMap.pp
      sym_resolved_map ;
    None )
  else
    Some
      { astate with
        mem= mem'
      ; pc= pc'
      ; is_exceptional= callee_summary.is_exceptional
      ; is_npe_alternative= callee_summary.is_npe_alternative || astate.is_npe_alternative }


(* Eval functions *)
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
      Val.lte v1 v1
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
  | Exp.Exn e ->
      eval astate node instr e |> Val.to_exn
  | Exp.Const (Cstr str) ->
      Val.make_string str
  | Exp.Const (Cint intlit) when IntLit.isnull intlit ->
      Val.make_null (Node.of_pnode node instr) ~pos
  | Exp.Const (Cint intlit) ->
      Val.of_intlit intlit
  | Exp.Const (Cfloat _) ->
      (* TODO? *)
      Val.top
  | Exp.Const (Cclass _) ->
      Val.unknown
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
    | _ as v ->
        L.(die InternalError) "lvalue expression %a cannot be evaluated to %a" Exp.pp exp Val.pp v )
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
  | Exp.Const (Cclass _) ->
      (* value of the class variable is unknown, so init by global *)
      Loc.unknown
      (* let cls_name = Ident.name_to_string cls in
         let cls_var = Pvar.mk_global (Mangled.from_string cls_name) in
         Loc.of_pvar cls_var *)
  | _ ->
      L.(die InternalError) "%a is not allowed as lvalue expression in java" Exp.pp exp


let init_with_formals formals : t =
  List.fold formals ~init:bottom ~f:(fun astate (pv, typ) -> resolve_unknown_loc astate typ (Loc.of_pvar pv))


let append_ctx astate offset =
  let reg = Reg.map (Val.append_ctx ~offset) astate.reg in
  let mem =
    Mem.fold (fun l v -> Mem.add (Loc.append_ctx ~offset l) (Val.append_ctx ~offset v)) astate.mem Mem.empty
  in
  let pc = PC.replace_by_map ~f:(Val.append_ctx ~offset) astate.pc in
  {astate with reg; mem; pc}
