open! IStd
open! Vocab
module F = Format
module L = Logging

module S = struct
  exception UnconvertibleExpr of Exp.t

  type t = base * access list [@@deriving compare]

  and base = Variable of Pvar.t | Primitive of Const.t

  and access = FieldAccess of Fieldname.t | MethodCallAccess of method_call | ArrayAccess of t

  and method_call = Procname.t * t list

  let of_pvar pv : t = (Variable pv, [])

  let of_const const : t = (Primitive const, [])

  let dummy_base = Primitive (Const.Cstr "NPEX_DUMMY")

  let dummy = (dummy_base, [])

  let equal = [%compare.equal: t]

  let equal_access = [%compare.equal: access]

  let equal_base = [%compare.equal: base]

  let rec pp fmt = function
    | base, accesses when equal_base base dummy_base ->
        (Pp.seq pp_access ~sep:".") fmt accesses
    | base, [] ->
        F.fprintf fmt "%a" pp_base base
    | base, accesses ->
        F.fprintf fmt "%a.%a" pp_base base (Pp.seq pp_access ~sep:".") accesses


  and pp_base fmt = function
    | Variable pv ->
        F.fprintf fmt "%s" (Pvar.get_simplified_name pv)
    | Primitive const ->
        (Const.pp Pp.text) fmt const


  and pp_access fmt = function
    | FieldAccess fld ->
        Pp.of_string ~f:Fieldname.to_simplified_string fmt fld
    | MethodCallAccess (method_name, args) ->
        F.fprintf fmt "%s(%a)" (Procname.get_method method_name) (Pp.seq ~sep:", " pp) args
    | ArrayAccess index ->
        F.fprintf fmt "[%a]" pp index


  let to_string t = F.asprintf "%a" pp t

  let get_deref_field (base, accesses) =
    match List.rev accesses |> List.hd with
    | None ->
        F.asprintf "%a" pp_base base
    | Some last_access ->
        F.asprintf "%a" pp_access last_access


  let is_local pdesc (base, _) =
    let formals = Procdesc.get_ret_var pdesc :: (Procdesc.get_pvar_formals pdesc |> List.map ~f:fst) in
    match base with
    | Variable pv when Pvar.is_global pv ->
        false
    | Variable pv when List.mem formals ~equal:Pvar.equal pv ->
        false
    | Variable _ ->
        true
    | Primitive _ ->
        false


  let rec chop_sub_aexpr ~sub access =
    match (sub, access) with
    | [], remaining ->
        Some remaining
    | sub_base :: sub_accesses, org_base :: org_accesses when equal_access sub_base org_base ->
        chop_sub_aexpr ~sub:sub_accesses org_accesses
    | _ ->
        None


  let replace_by_map x ~f = f x

  let replace_sub original ~src ~dst =
    let (src_base, src_access), (dst_base, dst_access), (org_base, org_access) = (src, dst, original) in
    if equal_base src_base org_base then
      (* src:p.f1.f2, dst:q, original: p.f1.f2.f3 
       * output: q.f3, remaining: [f3] *)
      match chop_sub_aexpr ~sub:src_access org_access with
      | Some remaining ->
          (dst_base, dst_access @ remaining)
      | None ->
          original
    else original


  let is_sub_expr ~(sub : t) aexpr = if equal aexpr (replace_sub ~src:sub ~dst:dummy aexpr) then false else true

  let append_access (base, accs) access = (base, accs @ [access])

  module Cache = struct
    let cache = ref ProcVar.Map.empty

    open IOption.Let_syntax

    let rec find_opt pdesc : Exp.t -> t option = function
      | Var id ->
          ProcVar.Map.find_opt (ProcVar.of_id (id, Procdesc.get_proc_name pdesc)) !cache
      | Cast (_, e) ->
          find_opt pdesc e
      | Sizeof _ ->
          Some (of_const (Cint IntLit.one))
      | Lvar pv when Pvar.is_frontend_tmp pv ->
          ProcVar.Map.find_opt (ProcVar.of_pvar pv) !cache
      | Lvar pv ->
          Some (of_pvar pv)
      | Lfield (e, fn, _) ->
          let+ base_aexpr = find_opt pdesc e in
          append_access base_aexpr (FieldAccess fn)
      | Const const ->
          Some (of_const const)
      | Lindex (e1, e2) ->
          let+ base_aexpr = find_opt pdesc e1 and+ index_aexpr = find_opt pdesc e2 in
          append_access base_aexpr (ArrayAccess index_aexpr)
      | _ ->
          None


    let pp = ProcVar.Map.pp ~pp_value:pp

    let find pdesc e =
      match find_opt pdesc e with
      | Some aexpr ->
          aexpr
      | None ->
          (* L.progress "Could not convert %a at %a" Exp.pp e Procname.pp
             (Procdesc.get_proc_name pdesc) ; *)
          raise (UnconvertibleExpr e)


    let add_pv _ pv aexpr = cache := ProcVar.Map.add (ProcVar.of_pvar pv) aexpr !cache

    let add_id pdesc id aexpr =
      cache := ProcVar.Map.add (ProcVar.of_id (id, Procdesc.get_proc_name pdesc)) aexpr !cache
  end

  let contain_method_call_access (_, accs) =
    List.exists accs ~f:(function MethodCallAccess _ -> true | _ -> false)


  let do_instr pdesc instr =
    try
      match instr with
      | Sil.Load {id; e} ->
          Cache.add_id pdesc id (Cache.find pdesc e)
      | Sil.Store {e1= Lvar pv; e2} when Pvar.is_frontend_tmp pv ->
          Cache.add_pv pdesc pv (Cache.find pdesc e2)
      | Sil.Call ((ret, _), Const (Cfun mthd), (Var this, _) :: args, _, CallFlags.{cf_virtual= true}) ->
          let arg_exprs = List.map args ~f:(fun (arg, _) -> Cache.find pdesc arg) in
          let ae = append_access (Cache.find pdesc (Var this)) (MethodCallAccess (mthd, arg_exprs)) in
          Cache.add_id pdesc ret ae
      | Sil.Call ((ret, _), Const (Cfun mthd), (Var this, _) :: args, _, _) ->
          (* this.mthd(...) is not virtual invocation *)
          let this_aexpr = Cache.find pdesc (Var this) in
          if String.equal (to_string this_aexpr) "this" then
            let arg_exprs = List.map args ~f:(fun (arg, _) -> Cache.find pdesc arg) in
            let ae = append_access this_aexpr (MethodCallAccess (mthd, arg_exprs)) in
            Cache.add_id pdesc ret ae
          else ()
      | _ ->
          ()
    with _ -> ()


  let bind_pdesc pdesc =
    let entry_node = Procdesc.get_start_node pdesc in
    if Instrs.is_empty (Procdesc.Node.get_instrs entry_node) then L.progress "empty instrs@." ;
    let entry = Procdesc.get_start_node pdesc |> InstrNode.list_of_pnode |> List.hd_exn in
    let rec do_worklist worklist doneset =
      if InstrNode.Set.is_empty worklist then ()
      else
        let work = InstrNode.Set.choose worklist in
        let rest = InstrNode.Set.remove work worklist in
        ignore (do_instr pdesc (InstrNode.get_instr work)) ;
        let next =
          let succs = InstrNode.get_succs work in
          let exns = InstrNode.get_exn work in
          InstrNode.Set.of_list (succs @ exns) |> InstrNode.Set.union rest
        in
        let new_worklist = InstrNode.Set.diff next doneset in
        let new_doneset = InstrNode.Set.add work doneset in
        do_worklist new_worklist new_doneset
    in
    do_worklist (InstrNode.Set.singleton entry) InstrNode.Set.empty


  let from_IR_exp_opt pdesc exp =
    match Cache.find_opt pdesc exp with
    | Some aexpr ->
        Some aexpr
    | None -> (
        bind_pdesc pdesc ;
        (* Cache.find pdesc exp *)
        match Cache.find_opt pdesc exp with Some aexpr -> Some aexpr | None -> None )


  let from_IR_exp pdesc exp =
    match from_IR_exp_opt pdesc exp with
    | Some aexpr ->
        aexpr
    | None ->
        L.(die InternalError) "Cannot convert %a@.AexprMap: %a@." Exp.pp exp Cache.pp !Cache.cache


  let null = of_const (Cint IntLit.null)

  let zero = of_const (Cint IntLit.zero)

  let one = of_const (Cint IntLit.one)
end

include S
module Set = PrettyPrintable.MakePPSet (S)
module Map = PrettyPrintable.MakePPMap (S)

let rec is_abstract (base, accesses) = is_abstract_base base || List.exists accesses ~f:is_abstract_access

and is_abstract_base _ = false

and is_abstract_access = function
  | FieldAccess _ ->
      false
  | ArrayAccess index ->
      is_abstract index
  | MethodCallAccess (callee, args) ->
      Procname.is_infer_undefined callee || List.exists args ~f:is_abstract


let rec is_concrete (base, accesses) = is_concrete_base base && List.exists accesses ~f:is_concrete_access

and is_concrete_base = function Variable _ -> false | Primitive _ -> true

and is_concrete_access = function
  | FieldAccess _ ->
      true
  | ArrayAccess index ->
      is_concrete index
  | MethodCallAccess (callee, args) ->
      (not (Procname.is_infer_undefined callee)) && List.for_all args ~f:is_concrete


let is_different_type _ _ = false
