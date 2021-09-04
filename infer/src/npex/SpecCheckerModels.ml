open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module SymHeap = SymDom.SymHeap
module Val = SymDom.Val
module Loc = SymDom.Loc
module Node = InstrNode

type exec =
     Domain.t
  -> Procdesc.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> Procname.t
  -> Ident.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> Domain.t list

type model = (Procname.t -> Sil.instr -> bool) * exec

(* For debugging *)
let seql x y =
  L.d_printfln " - compare class %s and %s" x y ;
  String.equal x y


let exception_classes = ["java.lang.Throwable"]

let implements classes typename = List.exists classes ~f:(seql (Typ.Name.name typename))

let implements_interfaces interfaces typename =
  List.exists interfaces ~f:(fun interface ->
      PatternMatch.Java.implements interface (Program.tenv ()) (Typ.Name.name typename))


(** Builtin model functions *)
module BuiltIn = struct
  let cast : model =
    let is_model callee _ = String.equal "__cast" (Procname.get_method callee) in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      (* ret_typ of__cast is Boolean, but is actually pointer type *)
      let arg_exp, _ = List.hd_exn arg_typs in
      (* TODO: check the logic is correct *)
      let value = Domain.eval astate node instr arg_exp in
      (* let value = Domain.Val.make_extern instr_node Typ.void_star in *)
      [Domain.store_reg astate ret_id value]
    in
    (is_model, exec)


  let instanceof : model =
    let is_model callee _ = String.equal "__instanceof" (Procname.get_method callee) in
    let exec astate _ node instr callee (ret_id, _) arg_typs =
      let instr_node = Node.of_pnode node instr in
      (* TODO: add type checking by using sizeof_exp and get_class_name_opt *)
      match arg_typs with
      | [(arg_exp, _); (Exp.Sizeof {typ= {desc= Typ.Tstruct name}}, _)]
        when implements_interfaces exception_classes name ->
          (* Exception catch *)
          let arg_value = Domain.eval astate node instr arg_exp in
          if Val.equal arg_value (Val.npe |> Val.unwrap_exn) then
            (* HEURISTIC 1: uncaught NPE will never catched
               FIXME: this is not desirable *)
            [Domain.store_reg astate ret_id Val.zero]
          else
            (* HEURISTIC 2: ignore exception type  *)
            let null = Domain.Val.make_null instr_node in
            let typ_value = Domain.Val.exn in
            Domain.add_pc astate (Domain.PathCond.make_physical_equals Binop.Ne arg_value null)
            |> List.concat_map ~f:(fun astate' ->
                   Domain.bind_extern_value astate' instr_node (ret_id, Typ.int) callee [arg_value; typ_value])
      | [(arg_exp, _); (Exp.Sizeof {typ}, _)] ->
          let arg_value = Domain.eval astate node instr arg_exp in
          let typ_value = Typ.to_string typ |> Domain.Val.make_string in
          let null_cond op = Domain.PathCond.make_physical_equals op arg_value (Domain.Val.make_null instr_node) in
          let null_states =
            Domain.add_pc astate (null_cond Binop.Eq)
            |> List.map ~f:(fun astate' -> Domain.store_reg astate' ret_id Domain.Val.zero)
          in
          let non_null_states =
            Domain.add_pc astate (null_cond Binop.Ne)
            |> List.concat_map ~f:(fun astate' ->
                   Domain.bind_extern_value astate' instr_node (ret_id, Typ.int) callee [arg_value; typ_value])
          in
          null_states @ non_null_states
      | [(arg_exp, _); (typ_exp, _)] ->
          (* This case happens in lambda function, TODO: refactoring *)
          let arg_value = Domain.eval astate node instr arg_exp in
          let typ_value = Domain.eval astate node instr typ_exp in
          let null_cond op = Domain.PathCond.make_physical_equals op arg_value (Domain.Val.make_null instr_node) in
          let null_states =
            Domain.add_pc astate (null_cond Binop.Eq)
            |> List.map ~f:(fun astate' -> Domain.store_reg astate' ret_id Domain.Val.zero)
          in
          let non_null_states =
            Domain.add_pc astate (null_cond Binop.Ne)
            |> List.concat_map ~f:(fun astate' ->
                   Domain.bind_extern_value astate' instr_node (ret_id, Typ.int) callee [arg_value; typ_value])
          in
          null_states @ non_null_states
      | _ ->
          L.(die InternalError) "wrong invariant of instanceof"
    in
    (is_model, exec)


  let unwrap_exception : model =
    let is_model callee _ = String.equal "__unwrap_exception" (Procname.get_method callee) in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let arg_exp, _ = List.hd_exn arg_typs in
      try
        let value = Domain.eval astate node instr arg_exp |> Domain.Val.unwrap_exn in
        [Domain.unwrap_exception (Domain.store_reg astate ret_id value)]
      with Unexpected msg ->
        L.progress "[WARNING]: ==============@.%s@." msg ;
        []
      (* L.(die InternalError) "%s@.%a@." msg Domain.pp astate *)
    in
    (is_model, exec)


  let models = [instanceof; cast; unwrap_exception]
end

let invoke : model =
  let classes = ["java.lang.reflect.Method"] in
  let is_model callee instr =
    match instr with
    | Sil.Call (_, Const (Cfun (Java mthd)), arg_typs, _, _) ->
        String.equal "invoke" (Procname.get_method callee)
        && Int.equal (List.length arg_typs) 3
        && implements classes (Procname.Java.get_class_type_name mthd)
    | _ ->
        false
  in
  let exec astate proc_desc node instr callee (ret_id, _) arg_typs =
    let[@warning "-8"] ((mthd_exp, _) :: (this_exp, _) :: (arg_arr_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let mthd_value = Domain.eval astate node instr mthd_exp in
    let this_value = Domain.eval astate node instr this_exp in
    let arg_arr_value = Domain.eval astate node instr arg_arr_exp in
    let arg_values =
      let arg_arr_loc = Domain.Val.to_loc arg_arr_value in
      let rec collect_arg_values acc i loc =
        let index_loc = Domain.Loc.append_index ~index:(SymDom.SymExp.of_intlit (IntLit.of_int i)) loc in
        if Domain.is_unknown_loc astate index_loc then acc
        else collect_arg_values (acc @ [Domain.read_loc astate index_loc]) (i + 1) index_loc
      in
      let arg_values = collect_arg_values [] 0 arg_arr_loc in
      mthd_value :: this_value :: arg_values
    in
    let ex_state = Domain.bind_exn_extern astate instr_node (Procdesc.get_ret_var proc_desc) callee arg_values in
    let normal_state = Domain.bind_extern_value astate instr_node (ret_id, Typ.void_star) callee arg_values in
    normal_state @ ex_state
  in
  (is_model, exec)


module Collection = struct
  let mIsEmptyField = Fieldname.make (Typ.Name.Java.from_string "Collection") "mIsEmpty"

  let classes = ["java.util.Iterator"; "java.util.Collection"; "java.util.Enumeration"; "java.util.Collections"]

  let is_model_class classname = implements_interfaces classes classname

  let setIsEmpty astate node instr loc =
    let is_empty_field_loc = Domain.Loc.append_field loc ~fn:mIsEmptyField in
    let is_empty_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.int in
    let astate_stored = Domain.store_loc astate is_empty_field_loc is_empty_value in
    Domain.add_pc astate_stored (Domain.PathCond.make_physical_equals Binop.Eq is_empty_value Domain.Val.one)


  let enumeration_of : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal "enumeration" (Procname.get_method callee) ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let value = Domain.eval astate node instr this_exp in
      [Domain.store_reg astate ret_id value]
    in
    (is_model, exec)


  let empty_enumeration : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [], _, _)
        when String.equal "emptyEnumeration" (Procname.get_method callee) ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) _ =
      let value = Domain.Val.make_allocsite (Node.of_pnode node instr) in
      let astate' = Domain.store_reg astate ret_id value in
      setIsEmpty astate' node instr (Domain.Val.to_loc value)
    in
    (is_model, exec)


  let init : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _) when Procname.Java.is_constructor mthd ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ _ arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      setIsEmpty astate node instr this_loc
    in
    (is_model, exec)


  let read_field astate field_loc =
    let astate =
      if Domain.is_unknown_loc astate field_loc then Domain.resolve_unknown_loc astate Typ.int field_loc
      else astate
    in
    (astate, Domain.read_loc astate field_loc)


  let isEmpty : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal (Procname.get_method callee) "isEmpty" ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let is_empty_field_loc = Domain.Loc.append_field this_loc ~fn:mIsEmptyField in
      let astate', is_empty_value = read_field astate is_empty_field_loc in
      [Domain.store_reg astate' ret_id is_empty_value]
    in
    (is_model, exec)


  let iterator : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal (Procname.get_method callee) "iterator" ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let is_empty_field_loc = Domain.Loc.append_field this_loc ~fn:mIsEmptyField in
      let astate', is_empty_value = read_field astate is_empty_field_loc in
      let iterator = SymDom.SymHeap.make_allocsite (Node.of_pnode node instr) in
      let iterator_is_empty = Domain.Loc.append_field (Domain.Loc.SymHeap iterator) ~fn:mIsEmptyField in
      let astate_stored = Domain.store_loc astate' iterator_is_empty is_empty_value in
      [Domain.store_reg astate_stored ret_id (Domain.Val.of_symheap iterator)]
    in
    (is_model, exec)


  let hasNext : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal (Procname.get_method callee) "hasNext" ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let is_empty_field_loc = Domain.Loc.append_field this_loc ~fn:mIsEmptyField in
      let astate', is_empty_value = read_field astate is_empty_field_loc in
      if Domain.Val.is_true is_empty_value then [Domain.store_reg astate' ret_id Domain.Val.zero]
      else if Domain.Val.is_false is_empty_value then [Domain.store_reg astate' ret_id Domain.Val.one]
      else
        let return_value = Domain.Val.neg_of is_empty_value in
        [Domain.store_reg astate ret_id return_value]
    in
    (is_model, exec)


  let add : model =
    let is_model callee _ =
      match callee with
      | Procname.Java mthd when String.equal (Procname.get_method callee) "add" ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let is_empty_field_loc = Domain.Loc.append_field this_loc ~fn:mIsEmptyField in
      let is_empty_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.int in
      let return_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.int in
      let astate_return_stored = Domain.store_reg astate ret_id return_value in
      let astate_stored = Domain.store_loc astate_return_stored is_empty_field_loc is_empty_value in
      Domain.add_pc astate_stored (Domain.PathCond.make_physical_equals Binop.Eq is_empty_value Domain.Val.zero)
    in
    (is_model, exec)


  let next : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, Typ.{desc= Tptr _})], _, _)
        when String.equal (Procname.get_method callee) "next" ->
          is_model_class (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let is_empty_field_loc = Domain.Loc.append_field this_loc ~fn:mIsEmptyField in
      (* CAUTION: do not make constraint: next_value = next(iterator) *)
      (* HEURISTIC: next always return next value other than NoSuchElement Exception *)
      let is_empty_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.int in
      let next_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.void_star in
      let astate = Domain.store_reg astate ret_id next_value in
      let astate = Domain.store_loc astate is_empty_field_loc is_empty_value in
      let astate_empty =
        Domain.add_pc astate (Domain.PathCond.make_physical_equals Binop.Eq is_empty_value Domain.Val.one)
      in
      let astate_non_empty =
        Domain.add_pc astate (Domain.PathCond.make_physical_equals Binop.Eq is_empty_value Domain.Val.zero)
      in
      astate_empty @ astate_non_empty
    in
    (is_model, exec)


  let models = [init; isEmpty; iterator; next; hasNext; add; enumeration_of; empty_enumeration]
end

module IO = struct
  let mStatus = Fieldname.make (Typ.Name.Java.from_string "Stream") "mStatus"

  let classes =
    ["java.io.FileInputStream"; "java.io.FileOutputStream"; "java.io.InputStream"; "java.io.OutputStream"]


  let init : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _) when Procname.Java.is_constructor mthd ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate pdesc node instr callee _ arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let this_val = Domain.eval astate node instr this_exp in
      let status_field_loc = Domain.Loc.append_field this_loc ~fn:mStatus in
      let normal_state = Domain.store_loc astate status_field_loc Domain.Val.one in
      let exceptional_state =
        Domain.bind_exn_extern astate (Node.of_pnode node instr) (Procdesc.get_ret_var pdesc) callee [this_val]
      in
      normal_state :: exceptional_state
    in
    (is_model, exec)


  let close : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _) when String.equal (Procname.get_method callee) "close"
        ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate pdesc node instr callee _ arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let this_val = Domain.eval astate node instr this_exp in
      let status_field_loc = Domain.Loc.append_field this_loc ~fn:mStatus in
      let normal_state = Domain.store_loc astate status_field_loc Domain.Val.zero in
      let exceptional_state =
        Domain.bind_exn_extern astate (Node.of_pnode node instr) (Procdesc.get_ret_var pdesc) callee [this_val]
      in
      normal_state :: exceptional_state
    in
    (is_model, exec)


  let read : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, _, _, _) when String.equal (Procname.get_method callee) "read" ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate pdesc node instr callee (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_val = Domain.eval astate node instr this_exp in
      (* CAUTION: do not make constraint: read_value = read(file) *)
      let read_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.int in
      let normal_state = Domain.store_reg astate ret_id read_value in
      let exceptional_state =
        Domain.bind_exn_extern astate (Node.of_pnode node instr) (Procdesc.get_ret_var pdesc) callee [this_val]
      in
      normal_state :: exceptional_state
    in
    (is_model, exec)


  let models = [init; close; read]
end

module Primitives = struct
  let mValue = Fieldname.make (Typ.Name.Java.from_string "Primitive") "mValue"

  let classes = ["java.lang.Boolean"]

  let booleanValue : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal (Procname.get_method callee) "booleanValue" ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let value =
        match Domain.eval astate node instr this_exp with
        | Val.Vheap (Symbol s) ->
            let deref_field = SymDom.Symbol.to_ap s |> AccessExpr.get_deref_field in
            if String.equal deref_field "FALSE" then Domain.Val.zero
            else if String.equal deref_field "TRUE" then Domain.Val.one
            else Val.make_extern (Node.of_pnode node instr) Typ.int
        | _ as v ->
            Val.make_extern (Node.of_pnode node instr) Typ.int
      in
      [Domain.store_reg astate ret_id value]
    in
    (is_model, exec)


  let models = [booleanValue]
end

module String = struct
  let classes = ["java.lang.String"]

  let builder_classes = ["java.lang.StringBuilder"]

  let valueField = Fieldname.make (Typ.Name.Java.from_string "String") "value"

  let read_value astate node instr str_exp =
    match Domain.eval astate node instr str_exp with
    | Val.Vheap (SymHeap.String _) as str_value ->
        (astate, str_value)
    | Val.Vheap _ as heap ->
        (astate, heap)
        (* let str_field = Loc.append_field ~fn:valueField (Loc.SymHeap sh) in
           let astate_unknown_resolved = Domain.resolve_unknown_loc astate Typ.void_star str_field in
           let str_value = Domain.read_loc astate str_field in
           (astate_unknown_resolved, str_value) *)
    | _ as v ->
        L.progress "[WARNING]: %a is not allowed as string value@." Val.pp v ;
        let str_value = Val.make_extern (Node.of_pnode node instr) Typ.void_star in
        (astate, str_value)


  let init : model =
    (* TODO: modeling new String() *)
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _); (_, _)], _, _) when Procname.Java.is_constructor mthd ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ _ arg_typs =
      let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let value_field_loc = Domain.Loc.append_field this_loc ~fn:valueField in
      let astate, str_value = read_value astate node instr str_exp in
      [Domain.store_loc astate value_field_loc str_value]
    in
    (is_model, exec)


  let init_default : model =
    let is_model callee instr =
      (* new StringBuilder(), new String() -> new object with empty string *)
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _) when Procname.Java.is_constructor mthd ->
          implements (classes @ builder_classes) (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ _ arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let this_loc = Domain.eval_lv astate node instr this_exp in
      let value_field_loc = Domain.Loc.append_field this_loc ~fn:valueField in
      let astate, str_value = read_value astate node instr (Exp.Const (Cstr "")) in
      [Domain.store_loc astate value_field_loc str_value]
    in
    (is_model, exec)


  let equals : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _); (_, _)], _, _)
        when String.equal (Procname.get_method callee) "equals" ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
      let astate, lhs_value = read_value astate node instr this_exp in
      let astate, rhs_value = read_value astate node instr str_exp in
      let equal_states =
        let equal_cond = Domain.PathCond.make_physical_equals Binop.Eq lhs_value rhs_value in
        Domain.add_pc (Domain.store_reg astate ret_id Val.one) equal_cond
      in
      let non_equal_states =
        let non_equal_cond = Domain.PathCond.make_physical_equals Binop.Ne lhs_value rhs_value in
        Domain.add_pc (Domain.store_reg astate ret_id Val.zero) non_equal_cond
      in
      equal_states @ non_equal_states
    in
    (is_model, exec)


  let isEmpty : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
        when String.equal (Procname.get_method callee) "isEmpty" ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let astate, str_value = read_value astate node instr this_exp in
      match str_value with
      | Val.Vheap (SymHeap.String str) when String.equal str "" ->
          [Domain.store_reg astate ret_id Val.one]
      | Val.Vheap (SymHeap.String _) ->
          [Domain.store_reg astate ret_id Val.zero]
      | _ ->
          let empty_states =
            let empty_cond = Domain.PathCond.make_physical_equals Binop.Eq str_value (Val.make_string "") in
            Domain.add_pc (Domain.store_reg astate ret_id Val.one) empty_cond
          in
          let non_empty_states =
            let empty_cond = Domain.PathCond.make_physical_equals Binop.Ne str_value (Val.make_string "") in
            Domain.add_pc (Domain.store_reg astate ret_id Val.zero) empty_cond
          in
          empty_states @ non_empty_states
    in
    (is_model, exec)


  let is_string = function Val.Vheap (SymHeap.String _) -> true | _ -> false

  let length : model =
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _) when String.equal (Procname.get_method callee) "length"
        ->
          implements classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr callee (ret_id, ret_typ) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
      let astate, str_value = read_value astate node instr this_exp in
      match List.find (Domain.equal_values astate str_value) ~f:is_string with
      | Some (Val.Vheap (SymHeap.String str)) ->
          let length_value = Val.of_intlit (IntLit.of_int (String.length str)) in
          [Domain.store_reg astate ret_id length_value]
      | _ ->
          Domain.bind_extern_value astate (Node.of_pnode node instr) (ret_id, ret_typ) callee [str_value]
    in
    (is_model, exec)


  let append : model =
    (* StringBuilder.append(String) *)
    let is_model callee instr =
      match (callee, instr) with
      | Procname.Java mthd, Sil.Call (_, _, [(_, _); (_, _)], _, _)
        when String.equal (Procname.get_method callee) "append" ->
          implements builder_classes (Procname.Java.get_class_type_name mthd)
      | _ ->
          false
    in
    let exec astate _ node instr _ (ret_id, _) arg_typs =
      let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
      let this_loc_field = Domain.Loc.append_field (Domain.eval_lv astate node instr this_exp) ~fn:valueField in
      let this_value = Domain.eval astate node instr this_exp in
      let astate, str_to_append =
        if Domain.Val.is_null (Domain.eval astate node instr str_exp) then (astate, Domain.Val.make_string "null")
        else read_value astate node instr str_exp
      in
      let astate, this_str = read_value astate node instr this_exp in
      match (this_str, str_to_append) with
      | Val.Vheap (String str1), Val.Vheap (String str2) ->
          let str = String.concat [str1; str2] in
          let astate' = Domain.store_loc astate this_loc_field (Val.Vheap (String str)) in
          [Domain.store_reg astate' ret_id this_value]
      | _ ->
          let str_value = Domain.Val.make_extern (Node.of_pnode node instr) Typ.void_star in
          let astate' = Domain.store_loc astate this_loc_field str_value in
          [Domain.store_reg astate' ret_id this_value]
    in
    (is_model, exec)


  let models = [init; isEmpty; length; equals; append]
end

let models : model list =
  BuiltIn.models @ [invoke] @ Collection.models @ IO.models @ String.models @ Primitives.models


let find_model_opt callee instr = List.find models ~f:(fun (is_model, _) -> is_model callee instr)

let is_model callee instr = find_model_opt callee instr |> Option.is_some

let exec_model : exec =
 fun astate proc_desc node instr callee (ret_id, ret_typ) arg_typs ->
  match find_model_opt callee instr with
  | Some (_, exec) ->
      exec astate proc_desc node instr callee (ret_id, ret_typ) arg_typs
  | None ->
      []

(* let cast = snd cast

let instanceof = snd instanceof

let unwrap_exception = snd unwrap_exception

let invoke = snd invoke

let getter_matcher _ callee_name = 

module Call = struct
  let dispatch : (Tenv.t, exec, unit) ProcnameDispatcher.Call.dispatcher =
    let open ProcnameDispatcher.Call in
    let match_builtin builtin _ s = String.equal s (Procname.get_method builtin) in
    make_dispatcher
      [ +match_builtin BuiltinDecl.__cast <>--> cast
      ; +match_builtin BuiltinDecl.__instanceof <>--> instanceof
      ; +match_builtin BuiltinDecl.__unwrap_exception <>--> unwrap_exception
      ; +PatternMatch.Java.implements "java.lang.reflect.Method" &:: "invoke" <>--> invoke 
      ; +PatternMatch.Java.implements "java.lang.reflect.Method" &:: "invoke" <>--> invoke 
      ]
end *)
