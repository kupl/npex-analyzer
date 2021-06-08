open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode

module Counter (Key : PrettyPrintable.PrintableOrderedType) = struct
  include PrettyPrintable.MakePPMonoMap (Key) (Int)

  let _counter = ref empty

  let get k =
    match find_opt k !_counter with
    | Some cnt ->
        _counter := add k (cnt + 1) !_counter ;
        cnt
    | None ->
        _counter := add k 1 !_counter ;
        0
end

module Allocsite = struct
  module Counter = Counter (Node)

  type t = InstrNode.t * int [@@deriving compare]

  let pp fmt (instr_node, cnt) =
    if Int.equal cnt 0 then F.fprintf fmt "%a" Location.pp_line (InstrNode.get_loc instr_node)
    else F.fprintf fmt "%a_%d" Location.pp_line (InstrNode.get_loc instr_node) cnt


  let increment (instr_node, cnt) offset = (instr_node, cnt + offset)

  let make node = (node, Counter.get node)
end

module Null = struct
  type t = {node: InstrNode.t [@compare.ignore]; pos: int [@compare.ignore]; is_model: bool [@compare.ignore]}
  [@@deriving compare]

  let pp_node fmt node = F.fprintf fmt "%a" Location.pp_line (InstrNode.get_loc node)

  let pp_node_model fmt (node, is_model) =
    if is_model then F.fprintf fmt "%a (Model)" pp_node node else F.fprintf fmt "%a" pp_node node


  let pp fmt {node; pos; is_model} =
    if Int.equal pos 0 then F.fprintf fmt "%a" pp_node_model (node, is_model)
    else F.fprintf fmt "%a-%dth" pp_node_model (node, is_model) pos


  let pp_src fmt {node; pos} =
    F.fprintf fmt "%a-%dth (%a)" InstrNode.pp node pos Location.pp_file_pos (InstrNode.get_loc node)


  let make ?(pos = 0) ?(is_model = false) node : t = {node; pos; is_model}
end

module SymbolCore = struct
  type access = Field of Fieldname.t | Index of IntLit.t [@@deriving compare]

  type base = Global of Pvar.t * access | Param of Pvar.t [@@deriving compare]

  type t = base * access list [@@deriving compare]

  let pp_access fmt = function
    | Field fn ->
        F.fprintf fmt ".%s" (Fieldname.to_simplified_string fn)
    | Index i ->
        F.fprintf fmt "[%a]" IntLit.pp i


  let pp_base fmt = function
    | Global (pv, access) ->
        F.fprintf fmt "G$(%a%a)" (Pvar.pp Pp.text) pv pp_access access
    | Param pv ->
        F.fprintf fmt "P(%a)" (Pvar.pp Pp.text) pv


  let pp fmt (base, accesses) = F.fprintf fmt "$(%a%a)" pp_base base (Pp.seq pp_access) accesses

  (* sort to resolve pvar first *)
  let compare (base1, accs1) (base2, accs2) =
    let len1, len2 = (List.length accs1, List.length accs2) in
    if Int.equal len1 len2 then compare (base1, accs1) (base2, accs2) else if len1 < len2 then -1 else 1


  let sub_symbols (base, accesses) : t list =
    match List.rev accesses with
    | [] ->
        []
    | _ :: tl ->
        List.fold (List.rev tl)
          ~init:([(base, [])], [])
          ~f:(fun (acc, accesses') access ->
            let new_accesses = accesses' @ [access] in
            let new_subsymbol = (base, new_accesses) in
            (new_subsymbol :: acc, new_accesses))
        |> fst


  let is_pvar = function Param _, [] -> true | _ -> false

  let make_global pv fn = (Global (pv, Field fn), [])

  let of_pvar pv = (Param pv, [])

  let append_field ~fn (base, accs) = (base, accs @ [Field fn])

  let append_index ~index (base, accs) = (base, accs @ [Index index])

  let to_ap : t -> AccessExpr.t =
    let append_symbol_access aexpr = function
      | Field fn ->
          AccessExpr.append_access aexpr (AccessExpr.FieldAccess fn)
      | Index intlit ->
          AccessExpr.append_access aexpr (AccessExpr.ArrayAccess (AccessExpr.of_const (Cint intlit)))
    in
    function
    | Global (pv, access), accesses ->
        List.fold (access :: accesses) ~init:(AccessExpr.of_formal pv) ~f:append_symbol_access
    | Param pv, accesses ->
        List.fold accesses ~init:(AccessExpr.of_formal pv) ~f:append_symbol_access
end

module Symbol = struct
  include SymbolCore
  module Set = PrettyPrintable.MakePPSet (SymbolCore)
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

  let make_null ?(pos = 0) ?(is_model = false) node = Null (Null.make ~pos ~is_model node)

  let make_string str = String str

  let of_symbol symbol = Symbol symbol

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

  let is_allocsite = function Allocsite _ -> true | _ -> false

  let append_ctx ~offset = function
    | Allocsite allocsite ->
        Allocsite (Allocsite.increment allocsite offset)
    | Extern allocsite ->
        Extern (Allocsite.increment allocsite offset)
    | _ as s ->
        s


  let pp fmt = function
    | Allocsite allocsite ->
        F.fprintf fmt "Allocsite %a" Allocsite.pp allocsite
    | Extern allocsite ->
        F.fprintf fmt "Extern %a" Allocsite.pp allocsite
    | Null null ->
        F.fprintf fmt "Null %a" Null.pp null
    | String str ->
        F.fprintf fmt "String %s" str
    | Symbol s ->
        F.fprintf fmt "%a" Symbol.pp s
    | Unknown ->
        F.fprintf fmt "Unknown"


  let to_null = function Null null -> null | _ as s -> L.(die InternalError) "%a is not null heap@." pp s
end

module SymExp = struct
  type t = IntLit of IntLit.t | FloatLit of float | Symbol of Symbol.t | Extern of Allocsite.t | IntTop
  [@@deriving compare]

  let pp fmt = function
    | IntLit intlit ->
        IntLit.pp fmt intlit
    | FloatLit flit ->
        F.fprintf fmt "%f" flit
    | Symbol s ->
        Symbol.pp fmt s
    | Extern allocsite ->
        F.fprintf fmt "ExVal %a" Allocsite.pp allocsite
    | IntTop ->
        F.fprintf fmt "IntTop"


  let equal = [%compare.equal: t]

  let lt x y =
    match (x, y) with
    | IntLit x, IntLit y ->
        if IntLit.lt x y then IntLit IntLit.one else IntLit IntLit.zero
    | FloatLit x, FloatLit y ->
        if Int.is_negative (Float.compare x y) then IntLit IntLit.one else IntLit IntLit.zero
    | _ ->
        IntTop


  let lte x y =
    match (x, y) with
    | (Symbol _, Symbol _ | Extern _, Extern _ | IntLit _, IntLit _ | FloatLit _, FloatLit _) when equal x y ->
        IntLit IntLit.one
    | _ ->
        lt x y


  let of_intlit intlit : t = IntLit intlit

  let of_float flit : t = FloatLit flit

  let of_symbol symbol : t = Symbol symbol

  let make_extern node = Extern (Allocsite.make node)

  let intTop = IntTop

  let is_top = equal intTop

  let is_constant = function IntLit _ | FloatLit _ -> true | _ -> false

  let is_symbolic = function Symbol _ -> true | _ -> false

  let add x y =
    match (x, y) with
    | IntLit x, IntLit y ->
        IntLit (IntLit.add x y)
    | Extern _, _ | _, Extern _ ->
        make_extern Node.dummy
    | _ ->
        IntTop


  let sub x y =
    match (x, y) with
    | IntLit x, IntLit y ->
        IntLit (IntLit.sub x y)
    | Extern _, _ | _, Extern _ ->
        make_extern Node.dummy
    | _ ->
        IntTop


  let get_intlit = function IntLit il -> Some il | _ -> None

  let append_ctx ~offset = function Extern x -> Extern (Allocsite.increment x offset) | _ as s -> s
end

module LocCore = struct
  type t =
    | IllTempVar of Pvar.t * int
    | TempVar of Pvar.t
    | Var of Pvar.t
    | SymHeap of SymHeap.t
    | Field of t * Fieldname.t
    | Index of t * SymExp.t
  [@@deriving compare]

  let rec pp fmt = function
    | IllTempVar (v, line) ->
        F.fprintf fmt "(IilTempPvar) %a%d" Pvar.pp_value v line
    | TempVar v ->
        F.fprintf fmt "(TempPvar) %a" Pvar.pp_value v
    | Var v ->
        F.fprintf fmt "(Pvar) %a" Pvar.pp_value v
    | SymHeap s ->
        F.fprintf fmt "(SymHeap) %a" SymHeap.pp s
    | Field (l, f) ->
        F.fprintf fmt "(Field) (%a).(%s)" pp l (Fieldname.to_simplified_string f)
    | Index (l, s) ->
        F.fprintf fmt "(Index) (%a)[%a]" pp l SymExp.pp s


  let compare x y =
    match (x, y) with
    | Var v1, Var v2 when Pvar.is_global v1 && Pvar.is_global v2 ->
        if String.equal (Pvar.to_string v1) (Pvar.to_string v2) then 0 else compare x y
    | _ ->
        compare x y


  let equal = [%compare.equal: t]

  let append_index l ~index = Index (l, index)

  let append_field ~fn l = Field (l, fn)

  let of_pvar ?(line = 0) pv : t =
    if Pvar.is_frontend_tmp pv then if is_ill_temp_var pv then IllTempVar (pv, line) else TempVar pv else Var pv


  let rec base_of = function Field (l, _) -> base_of l | Index (l, _) -> base_of l | _ as l -> l
end

module Loc = struct
  include LocCore

  let is_temp = function TempVar _ -> true | _ -> false

  let is_ill_temp = function IllTempVar _ -> true | _ -> false

  let is_rec ~f = function Index (l, _) -> f l | Field (l, _) -> f l | _ as l -> f l

  let is_symheap = function SymHeap _ -> true | _ -> false

  let rec is_heap = is_rec ~f:is_symheap

  (* check whether location is abstract *)
  let rec is_unknown = is_rec ~f:(function SymHeap sh -> SymHeap.is_unknown sh | _ -> false)

  let rec is_extern = is_rec ~f:(function SymHeap sh -> SymHeap.is_extern sh | _ -> false)

  let rec is_allocsite = is_rec ~f:(function SymHeap sh -> SymHeap.is_allocsite sh | _ -> false)

  let rec is_concrete = function
    | Var _ | TempVar _ | IllTempVar _ ->
        true
    | SymHeap sh ->
        SymHeap.is_concrete sh
    | Field (l, _) ->
        is_concrete l
    | Index (l, _) ->
        is_concrete l


  let is_var = function Var _ | TempVar _ | IllTempVar _ -> true | _ -> false

  let is_return = function Var pv -> Pvar.is_return pv | _ -> false

  let is_null = function SymHeap h -> SymHeap.is_null h | _ -> false

  let unknown = SymHeap SymHeap.unknown

  let make_extern node = SymHeap (SymHeap.make_extern node)

  let make_allocsite node = SymHeap (SymHeap.make_allocsite node)

  let make_null ?(pos = 0) ?(is_model = false) node = SymHeap (SymHeap.make_null node ~is_model ~pos)

  let make_string str = SymHeap (SymHeap.make_string str)

  let rec append_ctx ~offset = function
    | SymHeap sh ->
        SymHeap (SymHeap.append_ctx ~offset sh)
    | Field (l, fn) ->
        Field (append_ctx ~offset l, fn)
    | Index (l, index) ->
        Index (append_ctx l ~offset, index)
    | _ as l ->
        l


  let to_symheap = function SymHeap s -> s | _ as l -> L.(die InternalError) "%a is not heap location" pp l

  let rec replace_heap ~src ~dst = function
    | SymHeap sh when SymHeap.equal sh src ->
        SymHeap dst
    | Field (l, fn) ->
        Field (replace_heap l ~src ~dst, fn)
    | Index (l, index) ->
        Index (replace_heap l ~src ~dst, index)
    | _ as l ->
        l


  module Set = AbstractDomain.FiniteSet (LocCore)
  module Map = PrettyPrintable.MakePPMap (LocCore)
end

module ValCore = struct
  type t = Vint of SymExp.t | Vheap of SymHeap.t | Vexn of t | Vextern of Procname.t * t list | Bot | Top
  [@@deriving compare]

  let rec pp fmt = function
    | Vint i ->
        F.fprintf fmt "(SymExp) %a" SymExp.pp i
    | Vheap h ->
        F.fprintf fmt "(SymHeap) %a" SymHeap.pp h
    | Vexn (Vheap h) ->
        F.fprintf fmt "(Exn) %a" SymHeap.pp h
    | Vextern (callee, args) ->
        F.fprintf fmt "(Extern) %s(%a)" (Procname.get_method callee) (Pp.seq pp ~sep:",") args
    | Bot ->
        F.fprintf fmt "Bot"
    | Top ->
        F.fprintf fmt "Top"
    | Vexn v ->
        L.(die InternalError) "Invalid exceptional value: %a@." pp v


  let equal = [%compare.equal: t]

  let lt v1 v2 = match (v1, v2) with Vint s1, Vint s2 -> Vint (SymExp.lt s1 s2) | _ -> Vint IntTop

  let lte v1 v2 = match (v1, v2) with Vint s1, Vint s2 -> Vint (SymExp.lte s1 s2) | _ -> Vint IntTop

  let bottom = Bot (* undefined *)

  let top = Top (* type is not resolved, error! *)

  let get_const = function Vint se -> Option.map ~f:(fun il -> Const.Cint il) (SymExp.get_intlit se) | _ -> None

  let is_bottom = function Bot -> true | _ -> false

  let is_top = function Top -> true | _ -> false

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


  let is_different_type x y =
    match (x, y) with
    | Vint _, Vheap _ | Vint _, Vexn _ | Vheap _, Vint _ | Vheap _, Vexn _ | Vexn _, Vint _ | Vexn _, Vheap _ ->
        true
    | _ ->
        false


  let get_class_name_opt = function Vheap sh -> SymHeap.get_class_name_opt sh | _ -> None

  let to_exn = function
    | Vheap sh ->
        Vexn (Vheap sh)
    | _ as v ->
        L.(die InternalError) "%a cannot be throwable" pp v


  let unwrap_exn = function Vexn sh -> sh | _ as v -> raise (Unexpected (F.asprintf "%a is not throwable" pp v))

  let zero = Vint (SymExp.of_intlit IntLit.zero)

  let one = Vint (SymExp.of_intlit IntLit.one)

  let add x y = match (x, y) with Vint x, Vint y -> Vint (SymExp.add x y) | _ -> Top

  let sub x y = match (x, y) with Vint x, Vint y -> Vint (SymExp.sub x y) | _ -> Top

  let make_allocsite node = Vheap (SymHeap.make_allocsite node)

  let make_extern node typ =
    match Typ.(typ.desc) with
    | Tint _ | Tfloat _ ->
        Vint (SymExp.make_extern node)
    | Tptr _ | Tarray _ ->
        L.d_printfln "[PROGRESS]: make extern from type: %a" (Typ.pp_full Pp.text) typ ;
        Vheap (SymHeap.make_extern node)
    | _ ->
        top


  let make_null ?(pos = 0) ?(is_model = false) node = Vheap (SymHeap.make_null node ~is_model ~pos)

  let make_string str = Vheap (SymHeap.make_string str)

  let intTop = Vint SymExp.intTop

  let unknown = Vheap SymHeap.unknown

  let default_null = make_null Node.dummy

  let is_null = function Vheap symheap -> SymHeap.is_null symheap | _ -> false

  let rec is_abstract = function
    | Vint symexp ->
        SymExp.is_top symexp
    | Vheap symheap ->
        SymHeap.is_unknown symheap
    | Top ->
        true
    | Bot ->
        true
    | Vextern (callee, _) when Procname.is_infer_undefined callee ->
        true
    | Vextern (_, args) ->
        List.exists args ~f:is_abstract
    | _ ->
        false


  let is_extern = function Vheap (SymHeap.Extern _) | Vint (SymExp.Extern _) -> true | _ -> false

  let is_concrete = function
    | Vint symexp ->
        SymExp.is_constant symexp
    | Vheap symheap ->
        SymHeap.is_concrete symheap
    | _ ->
        false


  let rec is_constant = function
    | Vint symexp ->
        SymExp.is_constant symexp
    | Vheap symheap ->
        SymHeap.is_null symheap
    | Vextern (callee, _) when Procname.is_infer_undefined callee ->
        false
    | Vextern (_, args) ->
        List.for_all args ~f:is_constant
    | _ ->
        false


  let of_intlit intlit = Vint (SymExp.of_intlit intlit)

  let of_float flit = Vint (SymExp.of_float flit)

  let of_symheap sh = Vheap sh

  let of_symexp sexp = Vint sexp

  let top_of_typ typ =
    match Typ.(typ.desc) with Tint _ | Tfloat _ -> intTop | Tptr _ | Tarray _ -> unknown | _ -> top


  let get_default_by_typ instr_node typ =
    match Typ.(typ.desc) with
    | Tint _ ->
        zero
    | Tfloat _ ->
        of_float 0.0
    | Tptr _ ->
        make_null ~pos:0 instr_node
    | Tarray _ ->
        L.d_printfln "   - default value of array: extern@." ;
        make_extern instr_node typ
    | _ ->
        L.d_printfln "   - default value of %a: typ@." (Typ.pp_full Pp.text) typ ;
        L.progress "[WARNING]: get default by typ %a@." (Typ.pp_full Pp.text) typ ;
        top


  let proc_neg = Procname.from_string_c_fun "NPEX_NEG"

  let neg_of = function
    | Vint _ as v ->
        Vextern (proc_neg, [v])
    | _ as v ->
        L.(die InternalError) "Could not negate non-integer value %a" pp v


  let proc_lt = Procname.from_string_c_fun "lt"

  let proc_le = Procname.from_string_c_fun "le"

  let make_lt_pred lhs rhs = Vextern (proc_lt, [lhs; rhs])

  let make_le_pred lhs rhs = Vextern (proc_le, [lhs; rhs])

  let is_true x = equal x one

  let is_false x = equal x zero

  let is_symbolic = function
    | Vint symexp ->
        SymExp.is_symbolic symexp
    | Vheap sheap ->
        SymHeap.is_symbolic sheap
    | _ ->
        false


  let weak_join lhs rhs =
    match (lhs, rhs) with
    | _, _ when equal lhs rhs ->
        lhs
    | Vint _, _ | _, Vint _ ->
        make_extern Node.dummy Typ.int
    | Vheap _, _ | _, Vheap _ ->
        make_extern Node.dummy Typ.void_star
    | Vexn _, _ | _, Vexn _ ->
        Vexn (make_extern Node.dummy Typ.void_star)
    | _ ->
        top


  let join = weak_join

  let widen ~prev ~next ~num_iters:_ = join prev next

  let npe = to_exn (make_string "java.lang.NullPointerException")

  let symbol_from_loc_opt typ loc =
    let open IOption.Let_syntax in
    let+ symbol =
      match loc with
      | Loc.Var pv ->
          Some (Symbol.of_pvar pv)
      | Loc.Field (Loc.Var pv, fn) when Pvar.is_global pv ->
          Some (Symbol.make_global pv fn)
      | Loc.Field (Loc.Var pv, fn) when Pvar.is_global pv ->
          Some (Symbol.make_global pv fn)
      | Loc.Field (Loc.SymHeap (Symbol s), fn) ->
          Some (Symbol.append_field s ~fn)
      | Loc.Index (Loc.SymHeap (Symbol s), SymExp.IntLit index) ->
          Some (Symbol.append_index s ~index)
      | _ ->
          None
    in
    if Typ.is_pointer typ then Vheap (SymHeap.of_symbol symbol)
    else if Typ.is_int typ then Vint (SymExp.of_symbol symbol)
    else top_of_typ typ


  let to_loc = function
    | Vheap h ->
        Loc.SymHeap h
    | Top ->
        Loc.SymHeap SymHeap.unknown
    | _ as v ->
        raise (Unexpected (F.asprintf "Non-locational value %a cannot be converted to location" pp v))


  let to_symexp = function
    | Vint s ->
        s
    | Top ->
        SymExp.intTop
    | _ as v ->
        raise (Unexpected (F.asprintf "Non-integer value %a cannot be converted to symexp" pp v))


  let to_symheap = function
    | Vheap s ->
        s
    | Top ->
        SymHeap.unknown
    | _ as v ->
        raise (Unexpected (F.asprintf "Non-heap value %a cannot be converted to symheap" pp v))


  let rec append_ctx ~offset = function
    | Vint symexp ->
        Vint (SymExp.append_ctx ~offset symexp)
    | Vheap symheap ->
        Vheap (SymHeap.append_ctx ~offset symheap)
    | Vexn v ->
        Vexn (append_ctx ~offset v)
    | Vextern (pname, vlist) ->
        Vextern (pname, List.map ~f:(append_ctx ~offset) vlist)
    | _ as v ->
        v


  let rec replace_sub (x : t) ~(src : t) ~(dst : t) =
    if equal x src then dst
    else
      match (x, dst) with
      | Vextern _, Vextern _ ->
          (* TODO: support only single function *) x
      | Vextern (mthd, args), _ ->
          Vextern (mthd, List.map args ~f:(replace_sub ~src ~dst))
      | Vexn x, Vheap _ ->
          Vexn (replace_sub x ~src ~dst)
      | _ ->
          x


  let rec replace_by_map x ~f =
    match x with Vextern (mthd, args) -> Vextern (mthd, List.map args ~f:(replace_by_map ~f)) | _ -> f x


  let rec get_subvalues = function
    | Vextern (_, args) as v ->
        v :: List.concat_map args ~f:get_subvalues
    | Vexn v ->
        v :: get_subvalues v
    | _ as v ->
        [v]
end

module Val = struct
  include ValCore
  module Set = PrettyPrintable.MakePPSet (ValCore)
  module Map = PrettyPrintable.MakePPMap (ValCore)
end

let neg i = if IntLit.iszero i then IntLit.one else IntLit.zero

module PathCond = struct
  include Constraint.Make (Val)

  let make_lt_pred lhs rhs : t = PEquals (Val.make_lt_pred lhs rhs, Val.one)

  let make_le_pred lhs rhs : t = PEquals (Val.make_le_pred lhs rhs, Val.one)

  let normalize = function
    (* neg(a) == true => a == false *)
    | PEquals (Val.Vint (SymExp.IntLit i), Val.Vextern (proc, [v]))
    | PEquals (Val.Vextern (proc, [v]), Val.Vint (SymExp.IntLit i))
      when Procname.equal proc Val.proc_neg ->
        (* L.d_printfln "%a == %a(%a) is normalied to %a" IntLit.pp i Procname.pp proc Val.pp v IntLit.pp
           (neg i) ; *)
        PEquals (v, Val.Vint (SymExp.IntLit (neg i)))
    | Not (PEquals (Val.Vint (SymExp.IntLit i), Val.Vextern (proc, [v])))
    | Not (PEquals (Val.Vextern (proc, [v]), Val.Vint (SymExp.IntLit i)))
      when Procname.equal proc Val.proc_neg ->
        L.d_printfln "%a == %a(%a) is normalizable" IntLit.pp i Procname.pp proc Val.pp v ;
        PEquals (v, Val.Vint (SymExp.IntLit i))
    | _ as pathcond ->
        pathcond
end

module PC = struct
  include Constraint.MakePC (Val)

  let[@warning "-57"] add pathcond pc =
    let open PathCond in
    (* TODO: inequality solver *)
    match pathcond with
    | (PEquals (Val.Vextern (proc, [lhs; rhs]), truth) | PEquals (truth, Val.Vextern (proc, [lhs; rhs])))
      when Procname.equal proc Val.proc_le && Val.equal truth Val.one ->
        let is_lte = Val.lte lhs rhs in
        if Val.is_true is_lte then pc
        else if Val.is_false is_lte then add false_cond pc
        else add pathcond pc |> add (Not (PEquals (Val.make_lt_pred rhs lhs, Val.one)))
    | (PEquals (Val.Vextern (proc, [lhs; rhs]), truth) | PEquals (truth, Val.Vextern (proc, [lhs; rhs])))
      when Procname.equal proc Val.proc_lt && Val.equal truth Val.one ->
        let is_lt = Val.lt lhs rhs in
        if Val.is_true is_lt then pc
        else if Val.is_false is_lt then add false_cond pc
        else add pathcond pc |> add (Not (PEquals (Val.make_le_pred rhs lhs, Val.one)))
    | _ ->
        add pathcond pc
end

module Reg = struct
  include WeakMap.Make (Ident) (Val)

  let weak_join ~lhs ~rhs = mapi (fun l v -> Val.weak_join v (find l rhs)) lhs
end

module Mem = struct
  (* Allocsite[Index] has null as default value 
   * Other location has bottom as default value *)
  include WeakMap.Make (Loc) (Val)

  let find k t =
    match k with
    | Loc.Index (Loc.SymHeap (SymHeap.Allocsite (node, cnt)), _) when not (mem k t) ->
        Val.top
        (* Newly allocated array has default value *)
        (* TODO: find typ by node (new_array type) *)
        (* match Node.get_instr node with *)
        (* | Sil.Call (_, Const (Cfun procname), [(Sizeof {typ= Typ.{desc= Tptr (subtyp, _)}}, _)], _, _)
             when Procname.equal procname BuiltinDecl.__new_array ->
               L.progress " - try to get default from pointer of %a@." (Typ.pp_full Pp.text) subtyp ;
               Val.get_default_by_typ node subtyp
           | Sil.Call (_, Const (Cfun procname), [(Sizeof {typ= Typ.{desc= Tarray {elt}}}, _)], _, _)
             when Procname.equal procname BuiltinDecl.__new_array ->
               L.d_printfln " - try to get default from array of %a@." (Typ.pp_full Pp.text) elt ;
               Val.get_default_by_typ node elt *)
        (* | _ ->
            find k t ) *)
    | _ ->
        find k t


  let mem l t = Val.is_bottom (find l t) |> not

  let strong_update k v t = if Val.equal v (find k t) then t else strong_update k v t

  let weak_join ~lhs ~rhs =
    (* TODO: what if 
     * l -> v   | l -> bot
     * l -> bot | l -> bot *)
    mapi (fun l v -> Val.weak_join v (find l rhs)) lhs

  (* union (fun _ v1 v2 -> if Val.equal v1 v2 then Some v1 else Some (Val.weak_join v1 v2)) lhs rhs *)
end
