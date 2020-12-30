open! IStd
open! Vocab
module F = Format
module L = Logging
module Allocsite = InstrNode
module Node = InstrNode

module Context = struct
  type cvalue = {callsite: Sil.instr; callee: Procname.t} [@@deriving compare]

  type t = cvalue list

  let compare = List.compare compare_cvalue

  let pp_cvalue fmt {callsite} = (Sil.pp_instr ~print_types:true Pp.text) fmt callsite

  let pp fmt context = (Pp.seq pp_cvalue) fmt context

  let append acc instr callee : t = {callsite= instr; callee} :: acc

  let empty : t = []

  let[@warning "-8"] pop (_ :: rest) = rest
end

module Loc = struct
  type t =
    | Id of Context.t * Ident.t
    | Pvar of Context.t * Pvar.t
    | Allocsite of Context.t * Allocsite.t
    | Null of Context.t * Allocsite.t * int
    | Field of t * Fieldname.t
    | Index of t
    | Extern of Context.t * Allocsite.t
  [@@deriving compare]

  let rec pp fmt = function
    | Id (ctx, id) ->
        F.fprintf fmt "(Id) ctx(%a) %a" Context.pp ctx Ident.pp id
    | Pvar (ctx, v) ->
        F.fprintf fmt "(Pvar) ctx(%a) %a" Context.pp ctx Pvar.pp_value v
    | Allocsite (ctx, a) ->
        F.fprintf fmt "(Allocsite) ctx(%a) %a" Context.pp ctx Allocsite.pp a
    | Field (l, f) ->
        F.fprintf fmt "(Field) (%a).(%a)" pp l Fieldname.pp f
    | Index l ->
        F.fprintf fmt "(Index) (%a)[*]" pp l
    | Null (ctx, a, i) ->
        if i > 0 then F.fprintf fmt "(Null) ctx(%a) %a at %d-th arg" Context.pp ctx Allocsite.pp a i
        else F.fprintf fmt "(Null) ctx(%a) %a" Context.pp ctx Allocsite.pp a
    | Extern (ctx, a) ->
        F.fprintf fmt "(Extern) ctx(%a) %a" Context.pp ctx Allocsite.pp a


  let compare x y =
    match (x, y) with
    | Pvar (_, v1), Pvar (_, v2) when Pvar.is_global v1 && Pvar.is_global v2 ->
        if String.equal (Pvar.to_string v1) (Pvar.to_string v2) then 0 else compare x y
    | _ ->
        compare x y


  let equal = [%compare.equal: t]

  let make_null ~ctx ~node ~pos = Null (ctx, node, pos)

  let make_extern ~ctx ~node = Extern (ctx, node)

  let make_allocsite ~ctx ~node = Allocsite (ctx, node)

  let of_id ctx id = Id (ctx, id)

  let of_pvar ctx pv = Pvar (ctx, pv)

  let allocsite_of = function
    | Allocsite (_, a) ->
        a
    | _ as l ->
        L.(die InternalError) "cannot extract allocsite from %a" pp l


  let pvar_of = function Pvar (_, pv) -> pv | _ as l -> L.(die InternalError) "cannot extract pvar from %a" pp l

  let rec base_of = function Field (l, _) -> base_of l | Index l -> base_of l | _ as l -> l
end

module AbsLoc = struct
  type t = Bot | Loc of Loc.t | Top [@@deriving compare]

  let equal = [%compare.equal: t]

  let bottom = Bot

  let top = Top

  let is_bottom = equal Bot

  let is_top = equal Top

  let join x y = match (x, y) with Bot, Bot -> Bot | _, _ -> Top

  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs =
    if phys_equal lhs rhs then true else match (lhs, rhs) with Bot, _ -> true | _, Top -> true | _ -> false


  let is_null = function Loc (Null _) -> true | _ -> false

  let is_extern = function Loc (Extern _) -> true | _ -> false

  let of_id ctx id = Loc (Loc.of_id ctx id)

  let of_pvar ctx pv = Loc (Loc.of_pvar ctx pv)

  let pp fmt = function Bot -> F.fprintf fmt "Bot" | Top -> F.fprintf fmt "Top" | Loc l -> Loc.pp fmt l

  let append_field loc ~fn =
    match loc with
    | Top ->
        top
    | Bot | Loc (Id _) | Loc (Null _) ->
        bottom
    | Loc (Index _) ->
        loc
    | Loc loc ->
        Loc (Field (loc, fn))


  let append_index loc =
    match loc with
    | Top ->
        top
    | Bot | Loc (Id _) | Loc (Null _) ->
        bottom
    | Loc (Index _) ->
        loc
    | Loc loc ->
        Loc (Index loc)


  let make_null ~ctx ~node ~pos = Loc (Loc.make_null ~ctx ~node ~pos)

  let make_extern ~ctx ~node = Loc (Loc.make_extern ~ctx ~node)

  let make_allocsite ~ctx ~node = Loc (Loc.make_allocsite ~ctx ~node)
end

module Reg = WeakMap.Make (AbsLoc) (AbsLoc)
module Mem = WeakMap.Make (AbsLoc) (AbsLoc)

type state = {reg: Reg.t; mem: Mem.t; ctx: Context.t}

let empty = {reg= Reg.empty; mem= Mem.empty; ctx= Context.empty}

let pp fmt {reg; mem; ctx} = F.fprintf fmt "REG: %a@. MEM: %a@. CTX: %a@." Reg.pp reg Mem.pp mem Context.pp ctx

let points_to_of {mem} loc = Mem.find loc mem

let rec eval ({reg; ctx} as state) ~node ~pos : Exp.t -> AbsLoc.t = function
  | Var id ->
      Reg.find (AbsLoc.of_id ctx id) reg
  | Lvar pv when Pvar.is_global pv ->
      AbsLoc.of_pvar Context.empty pv
  | Lvar pv ->
      AbsLoc.of_pvar ctx pv
  | UnOp _ ->
      AbsLoc.top
  | BinOp (binop, e1, e2) ->
      eval_binop state binop ~node ~pos e1 e2
  | Const c ->
      eval_const state ~node ~pos c
  | Cast (_, e) ->
      eval state ~node ~pos e
  | Lfield (e, fn, _) ->
      AbsLoc.append_field (eval state ~node ~pos e) ~fn
  | Lindex (e, _) ->
      AbsLoc.append_index (eval state ~node ~pos e)
  | _ ->
      AbsLoc.bottom


and eval_const {ctx} ~node ~pos : Const.t -> AbsLoc.t = function
  | Cint intlit when IntLit.iszero intlit ->
      AbsLoc.make_null ~ctx ~node ~pos
  | _ ->
      AbsLoc.bottom


and eval_binop state (binop : Binop.t) ~node ~pos e1 e2 =
  match binop with
  | PlusPI when Exp.(is_null_literal e2 || is_zero e2) ->
      eval state ~node ~pos e1
  | MinusPI when Exp.(is_null_literal e2 || is_zero e2) ->
      eval state ~node ~pos e1
  | PlusPI | MinusPI ->
      AbsLoc.append_index (eval state ~node ~pos e1)
  | _ ->
      AbsLoc.bottom


let exec_instr ({mem; reg; ctx} as state) node =
  match Node.get_instr node with
  | Sil.Load {id; e} ->
      let value = Mem.find (eval state e ~node ~pos:0) mem in
      {state with reg= Reg.strong_update (AbsLoc.of_id ctx id) value reg}
  | Sil.Store {e1; e2} ->
      let value = eval state e2 ~node ~pos:0 in
      let loc = eval state e1 ~node ~pos:0 in
      {state with mem= Mem.strong_update loc value mem}
  | Sil.Call ((ret_id, _), Const (Cfun procname), _, _, _) when Models.is_new procname ->
      let value = AbsLoc.make_allocsite ~ctx ~node in
      let loc = AbsLoc.of_id ctx ret_id in
      {state with reg= Reg.strong_update loc value reg}
  | Sil.Call ((ret_id, _), _, _, _, _) ->
      (* Extern call *)
      let value = AbsLoc.make_extern ~ctx ~node in
      let loc = AbsLoc.of_id ctx ret_id in
      {state with reg= Reg.strong_update loc value reg}
  | _ ->
      state


let bind_argument ({ctx} as state) callee ~formals node =
  match Node.get_instr node with
  | Sil.Call (_, _, arg_typs, _, _) as instr ->
      let values = List.mapi arg_typs ~f:(fun i (arg_exp, _) -> eval state arg_exp ~node ~pos:i) in
      let new_ctx = Context.append ctx instr callee in
      let locs = List.map formals ~f:(fun (pv, _) -> AbsLoc.of_pvar new_ctx pv) in
      List.fold2_exn locs values ~init:{state with ctx= new_ctx} ~f:(fun ({mem} as state) loc value ->
          {state with mem= Mem.strong_update loc value mem})
  | _ as instr ->
      L.(die InternalError) "%a is not call instruction@." (Sil.pp_instr ~print_types:true Pp.text) instr


let bind_retvar ({ctx; reg; mem} as state) ~retvar = function
  | Sil.Call ((ret_id, _), _, _, _, _) ->
      let value = Mem.find (AbsLoc.of_pvar ctx retvar) mem in
      let new_ctx = Context.pop ctx in
      let loc = AbsLoc.of_id new_ctx ret_id in
      {state with ctx= new_ctx; reg= Reg.strong_update loc value reg}
  | _ as instr ->
      L.(die InternalError) "%a is not call instruction@." (Sil.pp_instr ~print_types:true Pp.text) instr
