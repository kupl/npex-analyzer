open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode

module Allocsite = struct
  type t = InstrNode.t * int [@@deriving compare]

  let pp fmt (instr_node, cnt) = F.fprintf fmt "%a_%d" Location.pp_line (InstrNode.get_loc instr_node) cnt

  let _cnt = ref 0

  let make node =
    _cnt := !_cnt + 1 ;
    (node, !_cnt)
end

module Null = struct
  type t = InstrNode.t * int

  (* We recored position of null constant to easily locate null source,
   * but we do not treat each value as distinguishable (null1 == null2)
   * (it is ok because null shall not be used as a key of a data-structure) *)
  let compare : t -> t -> int = fun _ _ -> 0

  let pp fmt (instr_node, pos) =
    if Int.equal pos 0 then F.fprintf fmt "%a" Location.pp_line (InstrNode.get_loc instr_node)
    else F.fprintf fmt "%a-%dth" Location.pp_line (InstrNode.get_loc instr_node) pos


  let make ?(pos = 0) node : t = (node, pos)
end

module Symbol = struct
  (* Symbol is simply implemented as int 
   * If domain requires join operation, symbol cannot be implemented as int *)
  type t = int [@@deriving compare]

  let pp fmt x = F.fprintf fmt "$%d" x

  let _counter = ref (-1)

  let make_fresh () =
    _counter := !_counter + 1 ;
    !_counter
end

module SymHeap = struct
  type t =
    | Allocsite of Allocsite.t
    | Extern of Allocsite.t
    | Null of Null.t
    | String of string
    | Symbol of Symbol.t
    | Unknown
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let make_allocsite node = Allocsite (Allocsite.make node)

  let make_extern node = Extern (Allocsite.make node)

  let make_null ?(pos = 0) node = Null (Null.make ~pos node)

  let make_string str = String str

  let get_class_name_opt = function
    | Allocsite (node, _) -> (
      match Node.get_instr node with
      | Sil.Call (_, Exp.Const (Const.Cfun procname), [(Exp.Sizeof {typ}, _)], _, _) when Models.is_new procname
        -> (
        match typ.desc with Tstruct name -> Some name | _ -> None )
      | _ ->
          None )
    | _ ->
        None


  let of_symbol s = Symbol s

  let unknown = Unknown

  let is_symbolic = function Symbol _ -> true | _ -> false

  let is_unknown = function Unknown -> true | _ -> false

  let is_extern = function Extern _ -> true | _ -> false

  let is_null = function Null _ -> true | _ -> false

  let is_concrete = function Allocsite _ | String _ | Null _ -> true | _ -> false

  let pp fmt = function
    | Allocsite allocsite ->
        F.fprintf fmt "(Allocsite) %a" Allocsite.pp allocsite
    | Extern allocsite ->
        F.fprintf fmt "(Extern) %a" Allocsite.pp allocsite
    | Null null ->
        F.fprintf fmt "(Null) %a" Null.pp null
    | String str ->
        F.fprintf fmt "(String) %s" str
    | Symbol s ->
        F.fprintf fmt "%a" Symbol.pp s
    | Unknown ->
        F.fprintf fmt "(Unknown)"
end

module SymExp = struct
  type t =
    | IntLit of IntLit.t
    | Symbol of Symbol.t
    | Unary of t * Unop.t
    | Binary of t * t * Binop.t
    | Extern of Allocsite.t
    | IntTop
  [@@deriving compare]

  let rec pp fmt = function
    | IntLit intlit ->
        IntLit.pp fmt intlit
    | Symbol s ->
        Symbol.pp fmt s
    | Unary (sexp, uop) ->
        F.fprintf fmt "%s(%a)" (Unop.to_string uop) pp sexp
    | Binary (sexp1, sexp2, binop) ->
        F.fprintf fmt "(%a) %s (%a)" pp sexp1 (Binop.str Pp.text binop) pp sexp2
    | Extern allocsite ->
        F.fprintf fmt "(ExVal) %a" Allocsite.pp allocsite
    | IntTop ->
        F.fprintf fmt "IntTop"


  (* let is_concrete = function IntTop -> false | _ -> true *)

  let equal = [%compare.equal: t]

  let intTop = IntTop

  let of_symbol s : t = Symbol s

  let of_intlit intlit : t = IntLit intlit

  let is_top = equal intTop

  let rec is_constant = function IntLit _ -> true | Unary (e, _) -> is_constant e | _ -> false

  let is_symbolic = function Symbol _ -> true | _ -> false

  let make_extern node = Extern (Allocsite.make node)

  let rec get_intlit = function
    | IntLit il ->
        Some il
    | Unary (e, Neg) -> (
      match get_intlit e with Some il -> Some (IntLit.neg il) | _ -> None )
    | _ ->
        None
end

module Loc = struct
  type t = Var of Pvar.t | SymHeap of SymHeap.t | Field of t * Fieldname.t | Index of t [@@deriving compare]

  let rec pp fmt = function
    | Var v ->
        F.fprintf fmt "(Pvar) %a" Pvar.pp_value v
    | SymHeap s ->
        F.fprintf fmt "(SymHeap) %a" SymHeap.pp s
    | Field (l, f) ->
        F.fprintf fmt "(Field) (%a).(%a)" pp l Fieldname.pp f
    | Index l ->
        F.fprintf fmt "(Index) (%a)[*]" pp l


  let compare x y =
    match (x, y) with
    | Var v1, Var v2 when Pvar.is_global v1 && Pvar.is_global v2 ->
        if String.equal (Pvar.to_string v1) (Pvar.to_string v2) then 0 else compare x y
    | _ ->
        compare x y


  let rec get_symbol_opt = function
    | Var _ ->
        None
    | SymHeap (Symbol s) ->
        Some s
    | SymHeap _ ->
        None
    | Field (l, _) ->
        get_symbol_opt l
    | Index l ->
        get_symbol_opt l


  let rec is_heap = function SymHeap _ -> true | Field (l, _) -> is_heap l | Index l -> is_heap l | _ -> false

  let rec is_unknown = function
    | SymHeap sh ->
        SymHeap.is_unknown sh
    | Field (l, _) ->
        is_unknown l
    | Index l ->
        is_unknown l
    | _ ->
        false


  let rec is_extern = function
    | SymHeap sh ->
        SymHeap.is_extern sh
    | Field (l, _) ->
        is_extern l
    | Index l ->
        is_extern l
    | _ ->
        false


  let is_null = function SymHeap h -> SymHeap.is_null h | _ -> false

  let rec is_symbolizable = function
    | Var _ ->
        true
    | SymHeap (Symbol _) ->
        true
    | SymHeap _ ->
        (* concrete heap is not symbolizable *)
        false
    | Field (l, _) ->
        is_symbolizable l
    | Index _ ->
        false


  let equal = [%compare.equal: t]

  let unknown = SymHeap SymHeap.unknown

  let make_extern node = SymHeap (SymHeap.make_extern node)

  let make_allocsite node = SymHeap (SymHeap.make_allocsite node)

  let make_null ?(pos = 0) node = SymHeap (SymHeap.make_null node ~pos)

  let make_string str = SymHeap (SymHeap.make_string str)

  let rec append_index = function (Var _ | SymHeap _ | Field _) as l -> Index l | Index _ as l -> l

  let append_field ~fn l = Field (l, fn)

  let of_pvar pv : t = Var pv

  let rec base_of = function Field (l, _) -> base_of l | Index l -> base_of l | _ as l -> l
end

module LocSet = PrettyPrintable.MakePPSet (Loc)

module Val = struct
  type t = Vint of SymExp.t | Vheap of SymHeap.t | Vexn of SymHeap.t | Bot | Top [@@deriving compare]

  let pp fmt = function
    | Vint i ->
        F.fprintf fmt "(SymExp) %a" SymExp.pp i
    | Vheap h ->
        F.fprintf fmt "(SymHeap) %a" SymHeap.pp h
    | Vexn sh ->
        F.fprintf fmt "(Exn) %a" SymHeap.pp sh
    | Bot ->
        F.fprintf fmt "Bot"
    | Top ->
        F.fprintf fmt "Top"


  let bottom = Bot (* undefined *)

  let top = Top (* type is not resolved, error! *)

  let get_const = function Vint se -> Option.map ~f:(fun il -> Const.Cint il) (SymExp.get_intlit se) | _ -> None

  let is_bottom = function Bot -> true | _ -> false

  let is_top = function Top -> true | _ -> false

  (* TODO: remove it after merge *)
  let equal x y =
    match (x, y) with
    | Vint i1, Vint i2 ->
        SymExp.equal i1 i2
    | Vheap h1, Vheap h2 | Vexn h1, Vexn h2 ->
        SymHeap.equal h1 h2
    | Bot, Bot | Top, Top ->
        true
    | _ ->
        false


  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | Vint i1, Vint i2 ->
        SymExp.equal i1 i2
    | Vheap h1, Vheap h2 ->
        SymHeap.equal h1 h2
    | Bot, _ ->
        true
    | _, Top ->
        true
    | _ ->
        false


  let equal lhs rhs =
    match (lhs, rhs) with
    | Vint i1, Vint i2 ->
        SymExp.equal i1 i2
    | Vheap h1, Vheap h2 ->
        SymHeap.equal h1 h2
    | _ ->
        false


  let get_class_name_opt = function Vheap sh -> SymHeap.get_class_name_opt sh | _ -> None

  let to_exn = function Vheap sh -> Vexn sh | _ as v -> L.(die InternalError) "%a cannot be throwable" pp v

  let zero = Vint (SymExp.of_intlit IntLit.zero)

  let one = Vint (SymExp.of_intlit IntLit.one)

  let make_allocsite node = Vheap (SymHeap.make_allocsite node)

  let make_extern node typ =
    if Typ.is_pointer typ then Vheap (SymHeap.make_extern node)
    else if Typ.is_int typ then Vint (SymExp.make_extern node)
    else top


  let make_null ?(pos = 0) node = Vheap (SymHeap.make_null node ~pos)

  let make_string str = Vheap (SymHeap.make_string str)

  let intTop = Vint SymExp.intTop

  let unknown = Vheap SymHeap.unknown

  let is_abstract = function
    | Vint symexp ->
        SymExp.is_top symexp
    | Vheap symheap ->
        SymHeap.is_unknown symheap
    | Top ->
        true
    | Bot ->
        true
    | _ ->
        false


  let is_concrete = function
    | Vint symexp ->
        SymExp.is_constant symexp
    | Vheap symheap ->
        SymHeap.is_concrete symheap
    | _ ->
        false


  let is_constant = function
    | Vint symexp ->
        SymExp.is_constant symexp
    | Vheap symheap ->
        SymHeap.is_null symheap
    | _ ->
        false


  let of_intlit intlit = Vint (SymExp.of_intlit intlit)

  let of_symheap sh = Vheap sh

  let of_symexp sexp = Vint sexp

  let of_typ typ = if Typ.is_pointer typ then unknown else if Typ.is_int typ then intTop else top

  let get_default_by_typ instr_node typ =
    if Typ.is_pointer typ then make_null ~pos:0 instr_node else if Typ.is_int typ then zero else top


  let of_const = function Const.Cint intlit -> of_intlit intlit | Const.Cstr str -> make_string str | _ -> top

  let is_true x = equal x one

  let is_false x = equal x zero

  let is_symbolic = function
    | Vint symexp ->
        SymExp.is_symbolic symexp
    | Vheap sheap ->
        SymHeap.is_symbolic sheap
    | _ ->
        false


  let join x y =
    match (x, y) with
    | Bot, Bot ->
        Bot
    | Bot, v | v, Bot ->
        v
    | Vint i1, Vint i2 when SymExp.equal i1 i2 ->
        Vint i1
    | Vheap h1, Vheap h2 when SymHeap.equal h1 h2 ->
        Vheap h1
    | _ ->
        Top


  let widen ~prev ~next ~num_iters:_ = join prev next
end

module PathCond = struct
  type t = PEquals of Val.t * Val.t | Not of t | Equals of Val.t * Val.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let true_cond = PEquals (Val.zero, Val.zero) (* top *)

  let false_cond = Not true_cond

  let is_true = equal true_cond

  let is_false = equal false_cond

  let rec is_unknown = function
    | (PEquals (v1, v2) | Equals (v1, v2)) when Val.is_abstract v1 || Val.is_abstract v2 ->
        true
    | Not x ->
        is_unknown x
    | _ ->
        false


  let rec is_valid = function
    | _ as x when is_unknown x ->
        false
    | PEquals (v1, v2) ->
        Val.equal v1 v2
    | Not cond ->
        is_invalid cond
    | _ ->
        (* TODO: add *)
        false


  and is_invalid = function
    | _ as x when is_unknown x ->
        false
    | PEquals (v1, v2) when Val.is_concrete v1 && Val.is_concrete v2 ->
        not (Val.equal v1 v2)
    | Not cond ->
        is_valid cond
    | _ ->
        (* TODO: add *)
        false


  let make_negation = function Not x -> x | _ as x -> Not x

  let make_physical_equals binop v1 v2 =
    (* if v1 or v2 contain symbol, then make condition
       else if no symbol in v1 or v2, it evaluates to true or false *)
    L.d_printfln "Make physical equals from (%s, %a, %a)" (Binop.str Pp.text binop) Val.pp v1 Val.pp v2 ;
    match (binop, v1, v2) with
    | Binop.Eq, v1, v2 ->
        PEquals (v1, v2)
    | Binop.Ne, v1, v2 ->
        Not (PEquals (v1, v2))
    | _ ->
        (* TODO: implement less than, greater than, etc.*)
        raise (TODO (F.asprintf "non equal condition(%s) are not supported" (Binop.str Pp.text binop)))


  (* TODO: do it *)
  let rec pp fmt = function
    | PEquals (v1, v2) ->
        F.fprintf fmt "%a == %a" Val.pp v1 Val.pp v2
    | Not (PEquals (v1, v2)) ->
        F.fprintf fmt "%a != %a" Val.pp v1 Val.pp v2
    | Not pc ->
        F.fprintf fmt "Not (%a)" pp pc
    | Equals (v1, v2) ->
        F.fprintf fmt "Equals (%a, %a)" Val.pp v1 Val.pp v2


  let rec vals_of_path_cond = function
    | PEquals (v1, v2) | Equals (v1, v2) ->
        [v1; v2]
    | Not pc ->
        vals_of_path_cond pc
end

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

module PC = struct
  include AbstractDomain.FiniteSet (PathCond)

  let compute_transitives pathcond pc =
    let open PathCond in
    fold
      (fun cond acc ->
        match (pathcond, cond) with
        | PEquals (v1, v2), PEquals (v1', v2') when Val.equal v1 v1' ->
            add (PEquals (v2, v2')) acc
        | PEquals (v1, v2), PEquals (v2', v1') when Val.equal v1 v1' ->
            add (PEquals (v2, v2')) acc
        | PEquals (v2, v1), PEquals (v1', v2') when Val.equal v1 v1' ->
            add (PEquals (v2, v2')) acc
        | PEquals (v2, v1), PEquals (v2', v1') when Val.equal v1 v1' ->
            add (PEquals (v2, v2')) acc
        | PEquals (v1, v2), Not (PEquals (v1', v2')) when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | PEquals (v1, v2), Not (PEquals (v2', v1')) when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | PEquals (v2, v1), Not (PEquals (v1', v2')) when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | PEquals (v2, v1), Not (PEquals (v2', v1')) when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | Not (PEquals (v1, v2)), PEquals (v1', v2') when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | Not (PEquals (v1, v2)), PEquals (v2', v1') when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | Not (PEquals (v2, v1)), PEquals (v1', v2') when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | Not (PEquals (v2, v1)), PEquals (v2', v1') when Val.equal v1 v1' ->
            add (Not (PEquals (v2, v2'))) acc
        | _ ->
            acc)
      pc (singleton pathcond)


  let is_valid pathcond pc = PathCond.is_valid pathcond || mem pathcond pc

  let add pathcond pc =
    if PathCond.is_unknown pathcond || PathCond.is_valid pathcond then pc
    else if PathCond.is_invalid pathcond then singleton PathCond.false_cond
    else
      let transitives = compute_transitives pathcond pc in
      union pc (filter (fun cond -> not (PathCond.is_valid cond)) transitives)
end

type t = {reg: Reg.t; mem: Mem.t; symtbl: SymTbl.t; pc: PC.t; is_npe_alternative: bool}

let pp fmt {symtbl; reg; mem; pc; is_npe_alternative} =
  F.fprintf fmt
    "@[<v 2> - Symbol Table:@,\
    \ %a@]@. @[<v 2> - Register:@,\
    \ %a@]@. @[<v 2> - Memory:@,\
    \ %a@]@. @[<v 2> - Path Conditions:@,\
    \ %a@]@. @[<v 2> - Is NPE Alternative: %b@]@." SymTbl.pp symtbl Reg.pp reg Mem.pp mem PC.pp pc
    is_npe_alternative


let leq ~lhs ~rhs = false

let bottom = {reg= Reg.bottom; mem= Mem.bottom; pc= PC.empty; symtbl= SymTbl.empty; is_npe_alternative= false}

let fold_memory {mem} ~init ~f = Mem.fold (fun l v acc -> f acc l v) mem init

type get_summary = Procname.t -> t option

(* Basic Queries *)

let is_unknown_loc {mem} l = Loc.is_unknown l || not (Mem.mem l mem)

let is_unknown_id {reg} l = not (Reg.mem l reg)

(* Read & Write *)
let read_loc {mem} l = Mem.find l mem

let read_symtbl {symtbl} l = SymTbl.find l symtbl

let store_loc astate l v : t = {astate with mem= Mem.strong_update l v astate.mem}

let store_reg astate id v = {astate with reg= Reg.strong_update id v astate.reg}

let remove_id astate id = {astate with reg= Reg.remove id astate.reg}

let remove_pvar astate ~pv = {astate with mem= Mem.remove (Loc.of_pvar pv) astate.mem}

let remove_locals astate ~locals = List.fold locals ~init:astate ~f:(fun acc pv -> remove_pvar acc ~pv)

let remove_temps astate vars =
  List.fold vars ~init:astate ~f:(fun astate' var ->
      match var with Var.LogicalVar id -> remove_id astate' id | Var.ProgramVar pv -> remove_pvar astate' ~pv)


let add_pc astate pathcond : t list =
  let pc' = PC.add pathcond astate.pc in
  if PC.exists PathCond.is_invalid pc' then [] else [{astate with pc= pc'}]


let get_path_conditions {pc} = PC.elements pc

let is_valid_pc astate pathcond = PC.is_valid pathcond astate.pc

let mark_npe_alternative astate = {astate with is_npe_alternative= true}

(* Symbolic domain *)
let resolve_unknown_loc astate typ loc : t =
  if Loc.is_symbolizable loc then
    let symbol = Symbol.make_fresh () in
    let symval =
      if Typ.is_pointer typ then SymHeap.of_symbol symbol |> Val.of_symheap
      else if Typ.is_int typ then SymExp.of_symbol symbol |> Val.of_symexp
      else (* maybe float *) Val.of_typ typ
    in
    let symtbl' = SymTbl.add loc symval astate.symtbl in
    let mem' = Mem.add loc symval astate.mem in
    {astate with symtbl= symtbl'; mem= mem'}
  else store_loc astate loc (Val.of_typ typ)


(* Summary resolve *)
module SymResolvedMap = struct
  include PrettyPrintable.MakePPMonoMap (Symbol) (Val)

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
                  let new_symbol = Symbol.make_fresh () in
                  let new_symbolic_value =
                    match v with
                    | Vint _ ->
                        Val.of_symexp (SymExp.of_symbol new_symbol)
                    | Vheap _ ->
                        Val.of_symheap (SymHeap.of_symbol new_symbol)
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
    PC.fold (fun pc -> PC.add (resolve_pc sym_resolved_map pc)) pc_to_resolve pc_to_update
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
  if PC.exists PathCond.is_invalid pc' then None else Some {astate with mem= mem'; pc= pc'; symtbl= symtbl'}


(* Eval functions *)
let eval_uop unop v = Val.top

let eval_binop binop v1 v2 = Val.top

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


let is_npe_alternative {is_npe_alternative} = is_npe_alternative

let pc_to_formula astate =
  let exception Not_Convertable of Val.t in
  let open Specification.Formula in
  let rec convert_val_to_aexpr : Val.t -> AccessExpr.t = function
    (* Convert symbolic values *)
    | (Val.Vint (SymExp.Symbol _) | Val.Vheap (SymHeap.Symbol _)) as v -> (
      match SymTbl.find_first (fun l -> Val.equal v (SymTbl.find l astate.symtbl)) astate.symtbl with
      | Loc.Field (Loc.Var pv, f), _ ->
          AccessExpr.AccessExpr (pv, [AccessExpr.FieldAccess f])
      | Loc.Field (Loc.SymHeap h, f), _ ->
          let[@warning "-8"] (AccessExpr.AccessExpr (pv, accesses)) = convert_val_to_aexpr (Val.Vheap h) in
          AccessExpr.AccessExpr (pv, accesses @ [AccessExpr.FieldAccess f])
      | Loc.Var pv, _ ->
          AccessExpr.AccessExpr (pv, [])
      | _ ->
          (* TODO: multiple field access, ... *)
          raise (Not_Convertable v) )
    (* Convert constant values *)
    | Val.Vint (SymExp.IntLit i) ->
        AccessExpr.Primitive (Const.Cint i)
    | Val.Vheap (SymHeap.Null _) ->
        AccessExpr.null
    | Val.Vheap (SymHeap.String str) ->
        AccessExpr.Primitive (Const.Cstr str)
    (* TODO: binary expression of aexpr, ... *)
    | _ as v ->
        raise (Not_Convertable v)
  in
  let rec convert_cond_to_formula : PathCond.t -> formula = function
    | PathCond.PEquals (v1, v2) ->
        Atom (Predicate (Binary Equals, [convert_val_to_aexpr v1; convert_val_to_aexpr v2]))
    | PathCond.Not cond ->
        Neg (convert_cond_to_formula cond)
    | _ ->
        (* TODO: make Equals formula from Equals PC *)
        Atom True
  in
  PC.fold
    (fun cond acc ->
      try
        let formula = convert_cond_to_formula cond in
        Specification.Conjunctions.add formula acc
      with Not_Convertable v ->
        L.progress "[WARNING]: failed to convert %a since no aepxr found for %a" PathCond.pp cond Val.pp v ;
        acc)
    astate.pc Specification.Conjunctions.empty


let rec loc_to_access_expr state =
  let open IOption.Let_syntax in
  function
  | Loc.Var pv ->
      Some (AccessExpr.of_pvar pv)
  | Loc.Field (l', fld) ->
      let+ base = loc_to_access_expr state l' in
      AccessExpr.append_access base (AccessExpr.FieldAccess fld)
  | Loc.Index l' ->
      let+ base = loc_to_access_expr state l' in
      AccessExpr.(append_access base (ArrayAccess dummy))
  | Loc.SymHeap sh ->
      symHeap_to_access_expr state sh


and symHeap_to_access_expr ({mem} as state) sh =
  let ae : AccessExpr.t option =
    Mem.fold
      (fun l v -> function Some _ as acc -> acc | None ->
            if Val.equal v (Val.of_symheap sh) then loc_to_access_expr state l else None)
      mem None
  in
  IOption.if_none_evalopt
    ~f:(fun () ->
      L.debug_dev
        "Could not convert %a to access expr@.(Memory does not contain any location whose value matches with the \
         symbolic heap)"
        SymHeap.pp sh ;
      None)
    ae
