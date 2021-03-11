open! IStd
open! Vocab
module Val = SymDom.Val
module Domain = SpecCheckerDomain

(** constants *)
let null_pos = -1

let inter_symstr = "NPEX_intermediate"

let bot_str = "NPEX_bot"

(** Null Spec Model *)
type abstract_type = Aint | Afloat | Aobject | Avoid [@@deriving compare]

let to_string_abstract_type = function Aint -> "int" | Afloat -> "float" | Aobject -> "Object" | Avoid -> "void"

let abstract_type_from_typ typ =
  let open Typ in
  match typ.desc with
  | Tint _ ->
      Aint
  | Tfloat _ ->
      Afloat
  | Tvoid ->
      Avoid
  | Tptr _ ->
      Aobject
  | Tstruct _ | Tarray _ | Tfun ->
      Aobject
  | TVar _ ->
      L.(die ExternalError) "TVar type is C++, not in Java"


type abstract_value = ANull | Aintermediate [@@deriving compare]

type method_kind = Static | Constructor | Virtual [@@deriving compare]

let to_string_abstract_value = function ANull -> "Null" | Aintermediate -> "InterVal"

module Key = struct
  type t =
    { arg_length: int
    ; model_index: int
    ; ret_type: abstract_type
    ; model_type: abstract_value
    ; method_kind: method_kind }
  [@@deriving compare]

  let pp fmt {model_index; ret_type; model_type} =
    (* TODO: print method kind *)
    let model_type_str = to_string_abstract_value model_type in
    let ret_typ_str = to_string_abstract_type ret_type in
    match model_index with
    | 0 ->
        F.fprintf fmt "%s:%s.foo(...)" ret_typ_str model_type_str
    | 1 ->
        F.fprintf fmt "%s:....foo(%s, ...)" ret_typ_str model_type_str
    | 2 ->
        F.fprintf fmt "%s:....foo(..., %s, ...)" ret_typ_str model_type_str
    | 3 ->
        F.fprintf fmt "%s:....foo(..., ..., %s, ...)" ret_typ_str model_type_str
    | _ ->
        F.fprintf fmt "%s:....foo(..., ..., ..., %s)" ret_typ_str model_type_str


  let default_of ret_type =
    (* NULL.foo() *) {arg_length= 1; model_index= 0; ret_type; model_type= ANull; method_kind= Virtual}


  let make ?(arg_length = 1) ?(model_index = 0) ?(model_type = ANull) ?(method_kind = Virtual) ret_type =
    {arg_length; model_index; ret_type; model_type; method_kind}
end

module Value = struct
  type context_info =
    { method_name: string
    ; return_type: string
    ; repo: string
    ; class_name: string
    ; argument_type: string list
    ; mutable frequency: int [@compare.ignore] }
  [@@deriving compare]

  type value = AccessExpr.t [@@deriving compare]

  type t = context_info * value [@@deriving compare]

  let pp fmt ({method_name; frequency}, aexpr) =
    F.fprintf fmt "%s -> %a (%d)" method_name AccessExpr.pp aexpr frequency


  let dummy = {method_name= ""; return_type= ""; repo= ""; class_name= ""; argument_type= []; frequency= 0}

  let default_of method_name value : t = ({dummy with method_name}, value)
end

type call_context =
  { arg_values: Val.t list
  ; node: Procdesc.Node.t
  ; instr: Sil.instr
  ; ret_typ: Ident.t * Typ.t
  ; arg_typs: (Exp.t * Typ.t) list
  ; callee: Procname.t }

module VSet = PrettyPrintable.MakePPSet (Value)
include PrettyPrintable.MakePPMonoMap (Key) (VSet)

let add k v acc =
  match find_opt k acc with
  (* TODO: increment frequency *)
  | Some vset ->
      add k (VSet.add v vset) acc
  | None ->
      add k (VSet.singleton v) acc


let _model = ref None

let from_json () = match !_model with None -> (* TODO: *) empty | Some model -> model

let bot_value = AccessExpr.of_const (Cstr bot_str)

let empty_str_value = AccessExpr.of_const (Cstr "")

let zero_float_value = AccessExpr.of_const (Cfloat 0.0)

let default_models =
  empty
  |> (* null.get(_) *) add (Key.make ~arg_length:2 Aobject) (Value.default_of "get" AccessExpr.null)
  |> (* null.get() *) add (Key.default_of Aobject) (Value.default_of "get" AccessExpr.null)
  |> (* null.get() *) add (Key.default_of Aint) (Value.default_of "get" AccessExpr.zero)
  |> (* null.get() *) add (Key.default_of Afloat) (Value.default_of "get" zero_float_value)
  |> (* null.set(_) *) add (Key.make ~arg_length:2 Avoid) (Value.default_of "set" bot_value)
  |> (* null.size() *) add (Key.default_of Aint) (Value.default_of "size" AccessExpr.zero)
  |> (* null.length() *) add (Key.default_of Aint) (Value.default_of "length" AccessExpr.zero)
  |> (* null.write() *) add (Key.default_of Avoid) (Value.default_of "write" bot_value)
  |> (* null.equals(_) *) add (Key.make ~arg_length:2 Aint) (Value.default_of "equals" AccessExpr.zero)
  |> (* null.isEmpty() *) add (Key.default_of Aint) (Value.default_of "isEmpty" AccessExpr.one)
  |> (* null.booleanValue() *) add (Key.default_of Aint) (Value.default_of "booleanValue" AccessExpr.zero)
  |> (* _.add(null) *) add (Key.make ~arg_length:2 ~model_index:1 Avoid) (Value.default_of "add" bot_value)
  |> (* _.find(null) *)
  add (Key.make ~arg_length:2 ~model_index:1 Aobject) (Value.default_of "find" AccessExpr.null)


let add_models_to_learn x =
  x
  |> (* null.isStatic(_) *) add (Key.default_of Aint) (Value.default_of "isStatic" AccessExpr.zero)
  |> (* null.isMemberOf(_, _) *) add (Key.make ~arg_length:3 Aint) (Value.default_of "isMemberOf" AccessExpr.zero)
  |> (* null.startsWith(_) *) add (Key.make ~arg_length:2 Aint) (Value.default_of "startsWith" AccessExpr.zero)
  |> (* null.isFailOnCCE(_) *) add (Key.default_of Aint) (Value.default_of "isFailOnCCE" AccessExpr.zero)
  |> (* null.hasNext(_) *) add (Key.default_of Aint) (Value.default_of "hasNext" AccessExpr.zero)
  |> (* null.toUpperCase(_) *)
  add (Key.make ~arg_length:2 Aobject) (Value.default_of "toUpperCase" AccessExpr.null)
  |> (* _.assertValid(null) *)
  add (Key.make ~arg_length:2 ~model_index:1 Avoid) (Value.default_of "assertValid" bot_value)
  |> (* _.matcher(null) *)
  add (Key.make ~arg_length:2 ~model_index:1 Aobject) (Value.default_of "matcher" AccessExpr.null)
  |> (* null.matches() *)
  add (Key.make ~arg_length:1 ~model_index:0 Aint) (Value.default_of "matches" AccessExpr.zero)
  |> (* null.matches() *)
  add (Key.make ~arg_length:2 ~model_index:0 Aint) (Value.default_of "remove" AccessExpr.zero)
  |> (* null.isMarkUp() *)
  add (Key.make ~arg_length:1 ~model_index:0 Aint) (Value.default_of "isMarkup" AccessExpr.zero)
  |> (* deleteQuietly(null) *)
  add (Key.make ~method_kind:Static Avoid) (Value.default_of "deleteQuietly" bot_value)


let add_models_require_context x =
  x
  |> (* null.toString() -> null *) add (Key.default_of Aobject) (Value.default_of "toString" AccessExpr.null)
  |> (* null.toString() -> null *) add (Key.default_of Aobject) (Value.default_of "getString" empty_str_value)
  |> (* init(this,null) -> null *)
  add
    (Key.make Avoid ~arg_length:2 ~model_index:1 ~method_kind:Constructor)
    (Value.default_of "<init>" AccessExpr.null)
  |> (* init(this,_,_,null,_,_) -> null *)
  add
    (Key.make Avoid ~arg_length:6 ~model_index:3 ~method_kind:Constructor)
    (Value.default_of "<init>" AccessExpr.null)


let is_matchable {callee} Value.({method_name}, _) =
  (* TODO: design matching function *)
  (* String.equal (Procname.get_method callee) method_name *)
  String.is_prefix (Procname.get_method callee) ~prefix:method_name


let is_model_null = function Val.Vheap (Null (_, pos)) -> Int.equal null_pos pos | _ -> false

let compute_similarity {callee} Value.({method_name}, _) =
  String.compare (Procname.get_method callee) method_name |> Int.abs


let model = (* TODO: from_json() *) default_models |> add_models_to_learn |> add_models_require_context

let get_method_kind proc =
  match proc with
  | Procname.Java mthd when Procname.Java.is_static mthd ->
      Static
  | _ when Procname.is_constructor proc ->
      Constructor
  | _ ->
      Virtual


let get equal_values callee_context =
  let {arg_values; ret_typ; callee} = callee_context in
  let key_opt =
    List.find_mapi arg_values ~f:(fun index v : Key.t option ->
        let open SymDom.Val in
        List.find_map (equal_values v) ~f:(function
          | Vheap (Null (_, pos)) when Int.equal null_pos pos ->
              let arg_length = List.length arg_values in
              let model_index = index in
              let ret_type = abstract_type_from_typ (snd ret_typ) in
              let model_type = ANull in
              let method_kind = get_method_kind callee in
              Some Key.{arg_length; model_index; ret_type; model_type; method_kind}
          | Vheap (String s) when String.equal s inter_symstr ->
              let arg_length = List.length arg_values in
              let model_index = index in
              let ret_type = abstract_type_from_typ (snd ret_typ) in
              let model_type = Aintermediate in
              let method_kind = get_method_kind callee in
              Some Key.{arg_length; model_index; ret_type; model_type; method_kind}
          | _ ->
              None))
  in
  match key_opt with
  | Some key -> (
      L.d_printfln "[NullSpecModel] Find applicable key: %a" Key.pp key ;
      match find_opt key model with
      | Some values ->
          (* TODO: design similarity function and select most similar one *)
          L.d_printfln "Model candidates:@,%a" VSet.pp values ;
          VSet.filter (is_matchable callee_context) values
          |> VSet.elements
          |> List.sort ~compare:(fun v1 v2 ->
                 (* lower similarity, more similar *)
                 compute_similarity callee_context v1 - compute_similarity callee_context v2)
          |> List.map ~f:snd
          |> List.hd
      | None ->
          None )
  | None ->
      None


let exec_null_model astate node instr ret_typ arg_typs callee =
  let instr_node = InstrNode.of_pnode node instr in
  function
  | model_aexpr when AccessExpr.equal AccessExpr.null model_aexpr && Procname.is_constructor callee ->
      (* new A(null) -> null *)
      let value = Domain.Val.make_null ~pos:null_pos instr_node in
      let[@warning "-8"] Exp.Var id, _ = List.hd_exn arg_typs in
      [Domain.store_reg astate id value]
  | model_aexpr when AccessExpr.equal AccessExpr.null model_aexpr ->
      let value = Domain.Val.make_null ~pos:null_pos instr_node in
      [Domain.store_reg astate (fst ret_typ) value]
  | model_aexpr when AccessExpr.equal model_aexpr bot_value ->
      (* empty *)
      [astate]
  | AccessExpr.Primitive const, [] ->
      let value = Domain.eval astate node instr (Exp.Const const) in
      [Domain.store_reg astate (fst ret_typ) value]
  | model_aexpr ->
      (*TODO: *)
      L.progress "[TODO]: design eval function for %a@." AccessExpr.pp model_aexpr ;
      [astate]


let exec_null_model_opt astate node instr ret_typ arg_typs callee =
  let arg_values =
    (* TODO: optimize it *)
    List.mapi arg_typs ~f:(fun i (arg_exp, _) -> Domain.eval astate node instr arg_exp ~pos:i)
  in
  let call_context = {arg_values; node; instr; ret_typ; arg_typs; callee} in
  match get (Domain.equal_values astate) call_context with
  | Some model_value ->
      L.d_printfln "Null model found: %a@," AccessExpr.pp model_value ;
      Some (exec_null_model astate node instr ret_typ arg_typs callee model_value)
  | None ->
      None
