open! IStd
open! Vocab
module Val = SymDom.Val

(** constants *)
let null_pos = -1

let inter_symstr = "NPEX_intermediate"

let empty_str = "NPEX_empty"

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

let to_string_abstract_value = function ANull -> "Null" | Aintermediate -> "InterVal"

module Key = struct
  type t = {arg_length: int; model_index: int; ret_type: abstract_type; model_type: abstract_value}
  [@@deriving compare]

  let pp fmt {model_index; ret_type; model_type} =
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


  let default_of ret_type = (* NULL.foo() *) {arg_length= 1; model_index= 0; ret_type; model_type= ANull}

  let make ?(arg_length = 1) ?(model_index = 0) ?(model_type = ANull) ret_type =
    {arg_length; model_index; ret_type; model_type}
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

let empty_value = AccessExpr.Primitive (Cstr empty_str)

let default_models =
  empty
  |> (* null.get(_) *) add (Key.make ~arg_length:2 Aobject) (Value.default_of "get" AccessExpr.null)
  |> (* null.get() *) add (Key.default_of Aobject) (Value.default_of "get" AccessExpr.null)
  |> (* null.get() *) add (Key.default_of Aint) (Value.default_of "get" AccessExpr.zero)
  |> (* null.set(_) *) add (Key.make ~arg_length:2 Avoid) (Value.default_of "set" empty_value)
  |> (* null.size() *) add (Key.default_of Aint) (Value.default_of "size" AccessExpr.zero)
  |> (* null.length() *) add (Key.default_of Aint) (Value.default_of "length" AccessExpr.zero)
  |> (* null.write() *) add (Key.default_of Avoid) (Value.default_of "write" empty_value)
  |> (* null.equals(_) *) add (Key.make ~arg_length:2 Aint) (Value.default_of "equals" AccessExpr.zero)
  |> (* null.startsWith(_) *) add (Key.make ~arg_length:2 Aint) (Value.default_of "startsWith" AccessExpr.zero)
  |> (* _.add(null) *) add (Key.make ~arg_length:2 ~model_index:1 Avoid) (Value.default_of "add" empty_value)
  |> (* _.find(null) *)
  add (Key.make ~arg_length:2 ~model_index:1 Aobject) (Value.default_of "find" AccessExpr.null)


let add_models_to_learn x =
  x
  |> (* null.isFailOnCCE(_) *) add (Key.make ~arg_length:1 Aint) (Value.default_of "isFailOnCCE" AccessExpr.zero)
  |> (* null.toUpperCase(_) *)
  add (Key.make ~arg_length:2 Aobject) (Value.default_of "toUpperCase" AccessExpr.null)
  |> (* _.invoke(_, null) *)
  add (Key.make ~arg_length:3 ~model_index:2 Aobject) (Value.default_of "invoke" AccessExpr.null)


let is_matchable {callee} Value.({method_name}, _) =
  (* TODO: design matching function *)
  (* String.equal (Procname.get_method callee) method_name *)
  String.is_prefix (Procname.get_method callee) ~prefix:method_name


let is_model_null = function Val.Vheap (Null (_, pos)) -> Int.equal null_pos pos | _ -> false

let get equal_values callee_context =
  let {arg_values; ret_typ} = callee_context in
  let model = (* TODO: from_json() *) default_models |> add_models_to_learn in
  let key_opt =
    List.find_mapi arg_values ~f:(fun index v : Key.t option ->
        let open SymDom.Val in
        List.find_map (equal_values v) ~f:(function
          | Vheap (Null (_, pos)) when Int.equal null_pos pos ->
              let arg_length = List.length arg_values in
              let model_index = index in
              let ret_type = abstract_type_from_typ (snd ret_typ) in
              let model_type = ANull in
              Some Key.{arg_length; model_index; ret_type; model_type}
          | Vheap (String s) when String.equal s inter_symstr ->
              let arg_length = List.length arg_values in
              let model_index = index in
              let ret_type = abstract_type_from_typ (snd ret_typ) in
              let model_type = Aintermediate in
              Some Key.{arg_length; model_index; ret_type; model_type}
          | _ ->
              None))
  in
  match key_opt with
  | Some key -> (
      L.d_printfln "[NullSpecModel] Find applicable key: %a" Key.pp key ;
      let open IOption.Let_syntax in
      match find_opt key model with
      | Some values ->
          (* TODO: design similarity function and select most similar one *)
          L.d_printfln "Model candidates:@.%a" VSet.pp values ;
          VSet.filter (is_matchable callee_context) values |> VSet.elements |> List.map ~f:snd |> List.hd
      | None ->
          None )
  | None ->
      None
