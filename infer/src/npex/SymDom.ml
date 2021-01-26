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

  let compare x y =
    match (x, y) with Null _, Null _ -> 0 | Null _, _ -> 1 | _, Null _ -> -1 | _, _ -> compare x y


  let equal = [%compare.equal: t]

  let make_allocsite node = Allocsite (Allocsite.make node)

  let make_extern node = Extern (Allocsite.make node)

  let make_null ?(pos = 0) node = Null (Null.make ~pos node)

  let make_string str = String str

  let make_symbol () = Symbol (Symbol.make_fresh ())

  let unknown = Unknown

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


  let equal = [%compare.equal: t]

  let lt x y =
    match (x, y) with
    | IntLit x, IntLit y ->
        if IntLit.lt x y then IntLit IntLit.one else IntLit IntLit.zero
    | _ ->
        IntTop


  let lte x y =
    match (x, y) with
    | Symbol _, Symbol _ when equal x y ->
        IntLit IntLit.one
    | IntLit _, IntLit _ when equal x y ->
        IntLit IntLit.one
    | IntLit _, IntLit _ ->
        lt x y
    | _ ->
        IntTop


  let of_intlit intlit : t = IntLit intlit

  let make_symbol () : t = Symbol (Symbol.make_fresh ())

  let make_extern node = Extern (Allocsite.make node)

  let intTop = IntTop

  let is_top = equal intTop

  let rec is_constant = function IntLit _ -> true | Unary (e, _) -> is_constant e | _ -> false

  let is_symbolic = function Symbol _ -> true | _ -> false

  let add x y = match (x, y) with IntLit x, IntLit y -> IntLit (IntLit.add x y) | _ -> IntTop

  let sub x y = match (x, y) with IntLit x, IntLit y -> IntLit (IntLit.sub x y) | _ -> IntTop

  let rec get_intlit = function
    | IntLit il ->
        Some il
    | Unary (e, Neg) -> (
      match get_intlit e with Some il -> Some (IntLit.neg il) | _ -> None )
    | _ ->
        None
end

module LocCore = struct
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


  let equal = [%compare.equal: t]
end

module LocSet = AbstractDomain.FiniteSet (LocCore)

module Loc = struct
  include LocCore
  module Cache = WeakMap.Make (LocCore) (LocSet)

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


  let unknown = SymHeap SymHeap.unknown

  let make_extern node = SymHeap (SymHeap.make_extern node)

  let make_allocsite node = SymHeap (SymHeap.make_allocsite node)

  let make_null ?(pos = 0) node = SymHeap (SymHeap.make_null node ~pos)

  let make_string str = SymHeap (SymHeap.make_string str)

  let _cache = ref Cache.empty

  let append_index l =
    let appended = match l with Var _ | SymHeap _ | Field _ -> Index l | Index _ -> l in
    _cache := Cache.weak_update l (LocSet.singleton appended) !_cache ;
    appended


  let append_field ~fn l =
    let appended = Field (l, fn) in
    _cache := Cache.weak_update l (LocSet.singleton appended) !_cache ;
    appended


  let fields_of l = Cache.find l !_cache

  let of_pvar pv : t = Var pv

  let rec base_of = function Field (l, _) -> base_of l | Index l -> base_of l | _ as l -> l
end

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


  let compare x y =
    match (x, y) with
    | Vheap s1, Vheap s2 ->
        SymHeap.compare s1 s2
    | Vheap _, _ ->
        1
    | _, Vheap _ ->
        -1
    | _ ->
        compare x y


  let lt v1 v2 = match (v1, v2) with Vint s1, Vint s2 -> Vint (SymExp.lt s1 s2) | _ -> Vint IntTop

  let lte v1 v2 = match (v1, v2) with Vint s1, Vint s2 -> Vint (SymExp.lte s1 s2) | _ -> Vint IntTop

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
    | Vheap h1, Vheap h2 | Vexn h1, Vexn h2 ->
        SymHeap.equal h1 h2
    | _ ->
        false


  let get_class_name_opt = function Vheap sh -> SymHeap.get_class_name_opt sh | _ -> None

  let to_exn = function Vheap sh -> Vexn sh | _ as v -> L.(die InternalError) "%a cannot be throwable" pp v

  let zero = Vint (SymExp.of_intlit IntLit.zero)

  let one = Vint (SymExp.of_intlit IntLit.one)

  let add x y = match (x, y) with Vint x, Vint y -> Vint (SymExp.add x y) | _ -> Top

  let sub x y = match (x, y) with Vint x, Vint y -> Vint (SymExp.sub x y) | _ -> Top

  let make_allocsite node = Vheap (SymHeap.make_allocsite node)

  let make_extern node typ =
    if Typ.is_pointer typ then Vheap (SymHeap.make_extern node)
    else if Typ.is_int typ then Vint (SymExp.make_extern node)
    else top


  let make_null ?(pos = 0) node = Vheap (SymHeap.make_null node ~pos)

  let make_string str = Vheap (SymHeap.make_string str)

  let intTop = Vint SymExp.intTop

  let unknown = Vheap SymHeap.unknown

  let is_null = function Vheap symheap -> SymHeap.is_null symheap | _ -> false

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

  let to_loc = function
    | Vheap h ->
        Loc.SymHeap h
    | _ as v ->
        raise (Unexpected (F.asprintf "Non-locational value %a cannot be converted to location" pp v))
end

module PathCond = Constraint.Make (Val)
module PC = Constraint.MakePC (Val)
