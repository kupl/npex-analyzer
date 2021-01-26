open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode
module Loc = SymDom.Loc
module Val = SymDom.Val
module PathCond = SymDom.PathCond
module PC = SymDom.PC
module SymExp = SymDom.SymExp
module SymHeap = SymDom.SymHeap

module SymTbl = struct
  include PrettyPrintable.MakePPMonoMap (Loc) (Val)

  let add l v t = if Val.is_top v then t else add l v t

  let to_symbol = function
    | Val.Vint (SymExp.Symbol s) | Val.Vheap (SymHeap.Symbol s) ->
        s
    | _ as v ->
        L.(die InternalError) "SymTbl has non-symbolic value %a@." Val.pp v
end

module Reg = WeakMap.Make (Ident) (Val)
module Mem = WeakMap.Make (Loc) (Val)

type t = {reg: Reg.t; mem: Mem.t; symtbl: SymTbl.t; pc: PC.t; is_npe_alternative: bool; is_exceptional: bool}

let pp fmt {symtbl; reg; mem; pc; is_npe_alternative; is_exceptional} =
  F.fprintf fmt
    "@[<v 2> - Symbol Table:@,\
    \ %a@]@. @[<v 2> - Register:@,\
    \ %a@]@. @[<v 2> - Memory:@,\
    \ %a@]@. @[<v 2> - Path Conditions:@,\
    \ %a@]@. @[<v 2> - Is NPE Alternative? Is Exceptional?@,\
    \ %b,%b@]@." SymTbl.pp symtbl Reg.pp reg Mem.pp mem PC.pp pc is_npe_alternative is_exceptional


let leq ~lhs ~rhs = phys_equal lhs rhs

let bottom =
  { reg= Reg.bottom
  ; mem= Mem.bottom
  ; pc= PC.empty
  ; symtbl= SymTbl.empty
  ; is_npe_alternative= false
  ; is_exceptional= false }


let fold_memory {mem} ~init ~f = Mem.fold (fun l v acc -> f acc l v) mem init

type get_summary = Procname.t -> t option

(* Basic Queries *)

let is_unknown_loc {mem} l = Loc.is_unknown l || not (Mem.mem l mem)

let is_unknown_id {reg} id = Val.is_bottom (Reg.find id reg)

let is_exceptional {is_exceptional} = is_exceptional

let is_npe_alternative {is_npe_alternative} = is_npe_alternative

let is_valid_pc astate pathcond = PC.is_valid pathcond astate.pc

(* Read & Write *)
let read_loc {mem} l = Mem.find l mem

let read_symtbl {symtbl} l = SymTbl.find l symtbl

let equal_values astate v =
  PC.fold
    (function
      | PathCond.PEquals (v1, v2) when Val.equal v1 v ->
          fun acc -> v2 :: acc
      | PathCond.PEquals (v1, v2) when Val.equal v2 v ->
          fun acc -> v1 :: acc
      | _ ->
          fun acc -> acc)
    astate.pc [v]


let store_loc astate l v : t = {astate with mem= Mem.strong_update l v astate.mem}

let store_reg astate id v = {astate with reg= Reg.strong_update id v astate.reg}

let remove_id astate id =
  if Reg.mem id astate.reg then {astate with reg= Reg.remove id astate.reg}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_pvar astate ~pv =
  let pvar_loc = Loc.of_pvar pv in
  if Mem.mem pvar_loc astate.mem then {astate with mem= Mem.remove (Loc.of_pvar pv) astate.mem}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_locals astate ~locals = List.fold locals ~init:astate ~f:(fun acc pv -> remove_pvar acc ~pv)

let remove_temps astate vars =
  List.fold vars ~init:astate ~f:(fun astate' var ->
      match var with Var.LogicalVar id -> remove_id astate' id | Var.ProgramVar pv -> remove_pvar astate' ~pv)


let add_pc astate pathcond : t list =
  let pc' = PC.add pathcond astate.pc in
  if PC.exists PathCond.is_invalid pc' then [] else [{astate with pc= pc'}]


let mark_npe_alternative astate = {astate with is_npe_alternative= true}

let set_exception astate = {astate with is_exceptional= true}

let unwrap_exception astate = {astate with is_exceptional= false}

(* Symbolic domain *)
let resolve_unknown_loc astate typ loc : t =
  if Loc.is_symbolizable loc then
    let symval =
      if Typ.is_pointer typ then SymHeap.make_symbol () |> Val.of_symheap
      else if Typ.is_int typ then SymExp.make_symbol () |> Val.of_symexp
      else (* maybe float *) Val.of_typ typ
    in
    let symtbl' = SymTbl.add loc symval astate.symtbl in
    let mem' = Mem.add loc symval astate.mem in
    {astate with symtbl= symtbl'; mem= mem'}
  else store_loc astate loc (Val.of_typ typ)


(* Summary resolve *)
module SymResolvedMap = struct
  include PrettyPrintable.MakePPMonoMap (SymDom.Symbol) (Val)

  let get_symbols sym_resolved_map = fold (fun s _ -> IntSet.add s) sym_resolved_map IntSet.empty

  let is_resolvable sym_resolved_map loc =
    match Loc.get_symbol_opt loc with Some symbol -> mem symbol sym_resolved_map | None -> true


  let next_works sym_resolved_map callee_symtbl =
    let resolved_symbols = get_symbols sym_resolved_map in
    let resolvable_symbols =
      SymTbl.fold
        (fun l v acc -> if is_resolvable sym_resolved_map l then IntSet.add (SymTbl.to_symbol v) acc else acc)
        callee_symtbl IntSet.empty
    in
    IntSet.diff resolvable_symbols resolved_symbols


  let rec resolve_loc sym_resolved_map = function
    | Loc.SymHeap sheap -> (
      match resolve_symheap sym_resolved_map sheap with
      | Val.Vheap sh ->
          Loc.SymHeap sh
      | _ as v ->
          raise (Unexpected (F.asprintf "%a is cannot resolved as loc" Val.pp v)) )
    | Loc.Field (l, fn) ->
        Loc.Field (resolve_loc sym_resolved_map l, fn)
    | Loc.Index l ->
        Loc.Index (resolve_loc sym_resolved_map l)
    | Loc.Var _ as l ->
        l


  and resolve_symheap sym_resolved_map = function
    | SymHeap.Symbol s ->
        find s sym_resolved_map
    | _ as sheap ->
        Val.Vheap sheap


  let rec resolve_val sym_resolved_map = function
    | Val.Vint symexp ->
        resolve_symexp sym_resolved_map symexp
    | Val.Vheap sheap | Val.Vexn sheap ->
        resolve_symheap sym_resolved_map sheap
    | _ as v ->
        v


  and resolve_symexp sym_resolved_map = function SymExp.Symbol s -> find s sym_resolved_map | _ -> Val.top

  let rec resolve_symtbl astate callee_symtbl acc works =
    if IntSet.is_empty works then acc
    else
      let symtbl_new, sym_resolved_map_new =
        SymTbl.fold
          (* input: loc_to_resolve, symbol
             1. resolve loc_to_resolve by sym_resolved_map
             2. if resolved_loc is known to caller state, bind symbol -> mem(resolved_loc)
             3. if resolved_loc is unknown to caller state,
                introduce new symbol, update symtbl, and bind symbol -> new_symbol *)
            (fun l v (symtbl, sym_resolved_map) ->
            let symbol_of_v = SymTbl.to_symbol v in
            if IntSet.mem symbol_of_v works then
              let resolved_loc =
                try resolve_loc sym_resolved_map l
                with Unexpected msg ->
                  raise
                    (Unexpected
                       (F.asprintf "%s@.Failed to resolve loc %a by %a@." msg Loc.pp l pp sym_resolved_map))
              in
              if is_unknown_loc astate resolved_loc then
                if SymTbl.mem resolved_loc symtbl then
                  (* There already exists an introduced symbol to resolved_loc *)
                  let sym_resolved_map' = add symbol_of_v (SymTbl.find resolved_loc symtbl) sym_resolved_map in
                  (symtbl, sym_resolved_map')
                else if Loc.is_symbolizable resolved_loc then
                  let new_symbolic_value =
                    match v with
                    | Vint _ ->
                        Val.of_symexp (SymExp.make_symbol ())
                    | Vheap _ ->
                        Val.of_symheap (SymHeap.make_symbol ())
                    | _ ->
                        L.(die InternalError) "%a has non symbolic value %a" Loc.pp l Val.pp v
                  in
                  let symtbl' = SymTbl.add resolved_loc new_symbolic_value symtbl in
                  let sym_resolved_map' = add symbol_of_v new_symbolic_value sym_resolved_map in
                  (symtbl', sym_resolved_map')
                else
                  (* unknown, but is not symbolizable location *)
                  let new_symbolic_value =
                    match v with Vint _ -> Val.intTop | Vheap _ -> Val.unknown | _ -> Val.top
                  in
                  (* TODO: figure out when this happens *)
                  let sym_resolved_map' = add symbol_of_v new_symbolic_value sym_resolved_map in
                  (symtbl, sym_resolved_map')
              else (symtbl, add symbol_of_v (read_loc astate resolved_loc) sym_resolved_map)
            else (symtbl, sym_resolved_map))
          callee_symtbl acc
      in
      let nextworks = next_works sym_resolved_map_new callee_symtbl in
      resolve_symtbl astate callee_symtbl (symtbl_new, sym_resolved_map_new) nextworks


  and resolve_pc sym_resolved_map = function
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
    PC.fold
      (fun pc acc ->
        let cond_to_add = resolve_pc sym_resolved_map pc in
        if PC.mem cond_to_add acc then acc
        else (* L.progress "%a is already in set!@." PathCond.pp cond_to_add ; *)
          PC.add cond_to_add acc)
      pc_to_resolve pc_to_update
end

let init_with_formals formals : t =
  List.fold formals ~init:bottom ~f:(fun astate (pv, typ) -> resolve_unknown_loc astate typ (Loc.of_pvar pv))


let resolve_summary astate ~actual_values ~formals callee_summary =
  let init_sym_resolved_map =
    List.fold2_exn formals actual_values ~init:SymResolvedMap.empty ~f:(fun sym_resolved_map (fv, typ) v ->
        if Typ.is_pointer typ || Typ.is_int typ then
          let symbol_of_fv = SymTbl.find (Loc.of_pvar fv) callee_summary.symtbl |> SymTbl.to_symbol in
          SymResolvedMap.add symbol_of_fv v sym_resolved_map
        else sym_resolved_map)
  in
  let symtbl', sym_resolved_map =
    try
      SymResolvedMap.resolve_symtbl astate callee_summary.symtbl (astate.symtbl, init_sym_resolved_map)
        (SymResolvedMap.next_works init_sym_resolved_map callee_summary.symtbl)
    with Unexpected msg -> L.(die InternalError) "%s@.%a" msg Mem.pp callee_summary.mem
  in
  let mem' = SymResolvedMap.replace_mem sym_resolved_map callee_summary.mem astate.mem in
  let pc' = SymResolvedMap.replace_pc sym_resolved_map callee_summary.pc astate.pc in
  if PC.exists PathCond.is_invalid pc' then None
  else
    Some
      { astate with
        mem= mem'
      ; pc= pc'
      ; symtbl= symtbl'
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


let rec eval_lv astate exp =
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
      eval_lv astate e
  | Exp.Lindex (e1, _) ->
      eval_lv astate e1 |> Loc.append_index
  | Exp.Lvar pv ->
      Loc.of_pvar pv
  | Exp.Lfield (e, fn, _) ->
      eval_lv astate e |> Loc.append_field ~fn
  | Exp.Const (Cclass _) ->
      (* value of the class variable is unknown, so init by global *)
      Loc.unknown
      (* let cls_name = Ident.name_to_string cls in
         let cls_var = Pvar.mk_global (Mangled.from_string cls_name) in
         Loc.of_pvar cls_var *)
  | _ ->
      L.(die InternalError) "%a is not allowed as lvalue expression in java" Exp.pp exp
