open! IStd
open! Vocab
module MValue = NullModel.MValue
module Pos = NullModel.Pos

module Key = struct
  type t =
    {arg_length: int; method_name: string; model_index: int; ret_type: abstract_type; method_kind: method_kind}
  [@@deriving compare]

  and abstract_type = Aint | Afloat | Aobject | Avoid [@@deriving compare]

  and method_kind = Static | Constructor | Virtual [@@deriving compare]

  let equal_abstract_type = [%compare.equal: abstract_type]

  let equal_method_kind = [%compare.equal: method_kind]

  let is_prefix callee ~prefix:{arg_length; method_name; model_index; ret_type; method_kind} =
    Int.equal callee.arg_length arg_length
    && String.is_prefix callee.method_name ~prefix:method_name
    && Int.equal model_index callee.model_index
    && equal_abstract_type ret_type callee.ret_type
    && equal_method_kind method_kind callee.method_kind


  let to_string_abstract_type = function
    | Aint ->
        "int"
    | Afloat ->
        "float"
    | Aobject ->
        "Object"
    | Avoid ->
        "void"


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


  let pp fmt {model_index; method_name; ret_type} =
    (* TODO: print method kind *)
    let ret_typ_str = to_string_abstract_type ret_type in
    match model_index with
    | 0 ->
        F.fprintf fmt "%s:%s.%s(...)" ret_typ_str "NULL" method_name
    | 1 ->
        F.fprintf fmt "%s:....%s(%s, ...)" ret_typ_str method_name "NULL"
    | 2 ->
        F.fprintf fmt "%s:....%s(..., %s, ...)" ret_typ_str method_name "NULL"
    | 3 ->
        F.fprintf fmt "%s:....%s(..., ..., %s, ...)" ret_typ_str method_name "NULL"
    | _ ->
        F.fprintf fmt "%s:....%s(..., ..., ..., %s)" ret_typ_str method_name "NULL"


  let default_of ret_type method_name = {arg_length= 1; model_index= 0; ret_type; method_kind= Virtual; method_name}

  let make ?(arg_length = 1) ?(model_index = 0) ?(method_kind = Virtual) ret_type method_name =
    {arg_length; model_index; ret_type; method_kind; method_name}


  let get_method_kind proc =
    match proc with
    | Procname.Java mthd when Procname.Java.is_static mthd ->
        Static
    | _ when Procname.is_constructor proc ->
        Constructor
    | _ ->
        Virtual


  let from_instr instr model_index =
    match instr with
    | Sil.Call ((_, ret_typ), Const (Cfun callee), arg_typs, _, _) ->
        let arg_length = List.length arg_typs in
        let method_name = Procname.get_method callee in
        let ret_type = abstract_type_from_typ ret_typ in
        let method_kind = get_method_kind callee in
        Some {arg_length; model_index; ret_type; method_kind; method_name}
    | _ ->
        None
end

module ManualModel = struct
  include PrettyPrintable.MakePPMonoMap (Key) (MValue)

  let skip_value prob = MValue.make_skip ~prob

  let null_value prob = MValue.make_null ~prob

  let empty_str_value prob = MValue.make_const (Const.Cstr "") ~prob

  let zero_float_value prob = MValue.make_const (Const.Cfloat 0.0) ~prob

  let zero_value prob = MValue.make_const (Const.Cint IntLit.zero) ~prob

  let one_value prob = MValue.make_const (Const.Cint IntLit.one) ~prob

  let exn_value prob = MValue.make_exn "EXN" ~prob

  let default_models =
    let prob = 0.99 in
    empty
    |> (* null.get(_) *) add (Key.make ~arg_length:2 Aobject "get") (null_value prob)
    |> (* null.get() *) add (Key.default_of Aobject "get") (null_value prob)
    |> (* null.get() *) add (Key.default_of Aint "get") (zero_value prob)
    |> (* null.get() *) add (Key.default_of Afloat "get") (zero_float_value prob)
    |> (* null.set(_) *) add (Key.make ~arg_length:2 Avoid "set") (skip_value prob)
    |> (* null.size() *) add (Key.default_of Aint "size") (zero_value prob)
    |> (* null.length() *) add (Key.default_of Aint "length") (zero_value prob)
    |> (* null.equals(_) *) add (Key.make ~arg_length:2 Aint "equals") (zero_value prob)
    |> (* null.isEmpty() *) add (Key.default_of Aint "isEmpty") (one_value prob)
    |> (* null.booleanValue() *) add (Key.default_of Aint "booleanValue") (zero_value prob)
    |> (* _.add(null) *) add (Key.make ~arg_length:2 ~model_index:1 Avoid "add") (skip_value prob)
    |> (* _.find(null) *)
    add (Key.make ~arg_length:2 ~model_index:1 Aobject "find") (null_value prob)
    |> (* _.write(null) *) add (Key.make ~arg_length:2 ~model_index:1 Avoid "write") (skip_value prob)
    |> (* _.close() *) add (Key.default_of Avoid "close") (skip_value prob)
    |> (* Class.write(null) *)
    add (Key.make ~arg_length:1 ~model_index:0 ~method_kind:Static Avoid "write") (skip_value prob)


  let add_models_to_learn x =
    let prob = 0.98 in
    x
    |> (* null.isStatic(_) *) add (Key.default_of Aint "isStatic") (zero_value prob)
    |> (* null.isMemberOf(_, _) *)
    add (Key.make ~arg_length:3 Aint "isMemberOf") (zero_value prob)
    |> (* null.startsWith(_) *) add (Key.make ~arg_length:2 Aint "startsWith") (zero_value prob)
    |> (* null.isFailOnCCE(_) *) add (Key.default_of Aint "isFailOnCCE") (zero_value prob)
    |> (* null.hasNext(_) *) add (Key.default_of Aint "hasNext") (zero_value prob)
    |> (* null.toUpperCase(_) *)
    add (Key.make ~arg_length:2 Aobject "toUpperCase") (null_value prob)
    |> (* _.assertValid(null) *)
    add (Key.make ~arg_length:2 ~model_index:1 Avoid "assertValid") (skip_value prob)
    |> (* _.matcher(null) *)
    add (Key.make ~arg_length:2 ~model_index:1 Aobject "matcher") (null_value prob)
    |> (* null.matches() *)
    add (Key.make ~arg_length:1 ~model_index:0 Aint "matches") (zero_value prob)
    |> (* null.matches() *)
    add (Key.make ~arg_length:2 ~model_index:0 Aint "remove") (zero_value prob)
    |> (* null.isMarkUp() *)
    add (Key.make ~arg_length:1 ~model_index:0 Aint "isMarkup") (zero_value prob)
    |> (* deleteQuietly(null) *)
    add (Key.make ~method_kind:Static Avoid "deleteQuietly") (skip_value prob)
    |> (* null.containsKey(_) *)
    add (Key.make ~arg_length:2 Aint "containsKey") (zero_value prob)
    |> (* null.iterator(_) *)
    add (Key.make Aobject "iterator") (null_value prob)
    |> (* null.getChars(_, _, _, _) *)
    add (Key.make ~arg_length:5 ~model_index:0 Avoid "getChars") (skip_value prob)


  let add_models_require_context x =
    let prob = 0.8 in
    x
    |> (* null.toString() -> null *) add (Key.default_of Aobject "toString") (null_value prob)
    |> (* null.toString() -> null *) add (Key.default_of Aobject "getString") (empty_str_value prob)
    |> (* null.getWidth() -> exn *) add (Key.default_of Afloat "getWidth") (exn_value prob)
    |> (* init(this,null) -> null *)
    add (Key.make Avoid ~arg_length:2 ~model_index:1 ~method_kind:Constructor "<init>") (null_value prob)
    |> (* init(this,_,_,null,_,_) -> null *)
    add (Key.make Avoid ~arg_length:6 ~model_index:3 ~method_kind:Constructor "<init>") (null_value prob)


  let model = (* TODO: from_json() *) default_models |> add_models_to_learn |> add_models_require_context

  let model_bindings = bindings model

  let find_opt = function
    | Some callee_key -> (
      match find_opt callee_key model with
      | Some mval ->
          Some mval
      | None ->
          List.find_map model_bindings ~f:(fun (model_key, mval) ->
              if Key.is_prefix callee_key ~prefix:model_key then Some mval else None) )
    | None ->
        None
end

let construct_manual_model proc_desc =
  let all_instr_nodes =
    let all_pnodes = Procdesc.get_nodes proc_desc in
    List.concat_map all_pnodes ~f:InstrNode.list_of_pnode
  in
  let result =
    List.fold ~init:NullModel.empty all_instr_nodes ~f:(fun acc instr_node ->
        let instr = InstrNode.get_instr instr_node in
        List.fold ~init:acc [0; 1; 2; 3; 4; 5; 6] ~f:(fun acc model_index ->
            match ManualModel.find_opt (Key.from_instr instr model_index) with
            | Some mval ->
                let pos : Pos.t = (instr_node, model_index) in
                NullModel.add_element pos mval acc
            | None ->
                acc))
  in
  (* L.progress "Manual Model: %a@." NullModel.pp result ; *)
  result
