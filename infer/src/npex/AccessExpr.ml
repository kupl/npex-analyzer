open! IStd
open! Vocab
module F = Format
module L = Logging

module S = struct
  exception UnconvertibleExpr of Exp.t

  type method_call = Procname.t * t list

  and t = AccessExpr of Pvar.t * access list | Primitive of Const.t [@@deriving compare]

  and access = FieldAccess of Fieldname.t | MethodCallAccess of method_call | ArrayAccess of t
  [@@deriving compare]

  let dummy_pvar = Pvar.mk_tmp "" Procname.empty_block

  let dummy = AccessExpr (dummy_pvar, [])

  (* Infer IntLit's compare does not distinguish pointernesses *)
  type literal_with_pointerness = IntLit.t * pointerness [@@deriving compare]

  and pointerness = bool

  let compare x y =
    match (x, y) with
    | Primitive (Cint i), Primitive (Cint j) when IntLit.isnull i || IntLit.isnull j ->
        compare_literal_with_pointerness (i, IntLit.isnull i) (j, IntLit.isnull j)
    | _ ->
        compare x y


  let equal_access = [%compare.equal: access]

  let rec pp fmt = function
    | AccessExpr (base, accesses) when Pvar.equal base dummy_pvar ->
        (Pp.seq pp_access ~sep:".") fmt accesses
    | AccessExpr (base, accesses) ->
        pp_access_expr fmt (base, accesses)
    | Primitive const ->
        (Const.pp Pp.text) fmt const


  and pp_access_expr fmt (base, accesses) =
    match accesses with
    | [] ->
        F.fprintf fmt "%a" pp_base base
    | _ ->
        F.fprintf fmt "%a.%a" pp_base base (Pp.seq pp_access ~sep:".") accesses


  and pp_base fmt pv = F.fprintf fmt "%s" (Pvar.get_simplified_name pv)

  and pp_method_call fmt (method_name, args) =
    F.fprintf fmt "%s(%a)" (Procname.get_method method_name) (Pp.seq ~sep:", " pp) args


  and pp_access fmt = function
    | FieldAccess fld ->
        Pp.of_string ~f:Fieldname.to_simplified_string fmt fld
    | MethodCallAccess call ->
        pp_method_call fmt call
    | ArrayAccess index ->
        F.fprintf fmt "[%a]" pp index


  let to_string_access_simple = function
    | FieldAccess fld ->
        Fieldname.to_simplified_string fld
    | MethodCallAccess (proc, _) ->
        Procname.get_method proc
    | ArrayAccess _ ->
        L.(die InternalError) "Array field is not supported"


  let to_string t = F.asprintf "%a" pp t

  let of_pvar pv = AccessExpr (pv, [])

  let of_const const = Primitive const

  let equal_base t pv = match t with AccessExpr (base, _) -> Pvar.equal base pv | _ -> false

  let equal = [%compare.equal: t]

  let get_deref_field = function
    | AccessExpr (pv, accesses) -> (
      match List.rev accesses with
      | hd :: _ ->
          to_string_access_simple hd |> String.split ~on:'.' |> List.rev |> List.hd_exn
      | [] ->
          Pvar.get_simplified_name pv )
    | Primitive (Cint intlit) when IntLit.isnull intlit ->
        "null"
    | _ ->
        ""


  let is_local pdesc =
    let formals = Procdesc.get_ret_var pdesc :: (Procdesc.get_pvar_formals pdesc |> List.map ~f:fst) in
    function
    | AccessExpr (pv, _) when Pvar.is_global pv ->
        false
    | AccessExpr (pv, _) when List.mem formals ~equal:Pvar.equal pv ->
        false
    | AccessExpr _ ->
        true
    | _ ->
        false


  let is_sub_expr ~(sub : t) aexpr =
    match (aexpr, sub) with AccessExpr (base, _), AccessExpr (base', _) -> Pvar.equal base base' | _, _ -> false


  let rec chop_sub_aexpr ~sub access =
    match (sub, access) with
    | [], remaining ->
        Some remaining
    | sub_base :: sub_accesses, org_base :: org_accesses when equal_access sub_base org_base ->
        chop_sub_aexpr ~sub:sub_accesses org_accesses
    | _ ->
        None


  let replace_sub original ~src ~dst =
    match (src, dst, original) with
    | AccessExpr (src_base, src_access), AccessExpr (dst_base, dst_access), AccessExpr (org_base, org_access)
      when Pvar.equal src_base org_base -> (
      (* src:p.f1.f2, dst:q, original: p.f1.f2.f3 
       * output: q.f3, remaining: [f3] *)
      match chop_sub_aexpr ~sub:src_access org_access with
      | Some remaining ->
          AccessExpr (dst_base, dst_access @ remaining)
      | None ->
          original )
    | _ when equal src original ->
        (* replace access-path to constant *)
        dst
    | _ ->
        original


  let replace_base ~dst original =
    match (dst, original) with
    | AccessExpr (dst_base, dst_access), AccessExpr (_, access) ->
        AccessExpr (dst_base, dst_access @ access)
    | _ ->
        L.(die InternalError) "Cannot replace constant expression"


  let append_access t access =
    match t with
    | AccessExpr (base, accs) ->
        AccessExpr (base, accs @ [access])
    | _ ->
        L.(die InternalError) "Cannot append access to constant"


  module Cache = struct
    let cache = ref ProcVar.Map.empty

    let rec find_opt pdesc : Exp.t -> t option = function
      | Var id ->
          ProcVar.Map.find_opt (ProcVar.of_id (id, Procdesc.get_proc_name pdesc)) !cache
      | Cast (_, e) ->
          find_opt pdesc e
      | Lvar pv when Pvar.is_frontend_tmp pv ->
          ProcVar.Map.find_opt (ProcVar.of_pvar pv) !cache
      | Lvar pv ->
          Some (AccessExpr (pv, []))
      | Lfield (e, fn, _) -> (
        match find_opt pdesc e with
        | Some (AccessExpr (base, access)) ->
            Some (AccessExpr (base, access @ [FieldAccess fn]))
        | Some (Primitive _) ->
            L.(die InternalError) "Lfield should follow access expression"
        | None ->
            None )
      | Const const ->
          Some (Primitive const)
      | Lindex (e1, e2) -> (
        match (find_opt pdesc e1, find_opt pdesc e2) with
        | Some (AccessExpr (base, access)), Some aexpr ->
            Some (AccessExpr (base, access @ [ArrayAccess aexpr]))
        | _ ->
            L.(die InternalError) "Lindex should follow access expression" )
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

  let contain_method_call_access = function
    | AccessExpr (_, accs) ->
        List.exists accs ~f:(function MethodCallAccess _ -> true | _ -> false)
    | _ ->
        false


  let get_base : t -> Pvar.t = function
    | AccessExpr (base, _) ->
        base
    | _ ->
        L.(die InternalError) "Cannot get base from primitive"


  let compose_expr pdesc = function
    | Exp.Const const ->
        Primitive const
    | Exp.Sizeof _ ->
        Primitive (Cint IntLit.one)
    | e ->
        Cache.find pdesc e


  let do_instr pdesc instr =
    try
      match instr with
      | Sil.Load {id; e} ->
          Cache.add_id pdesc id (Cache.find pdesc e)
      | Sil.Store {e1= Lvar pv; e2} when Pvar.is_frontend_tmp pv ->
          Cache.add_pv pdesc pv (Cache.find pdesc e2)
      | Sil.Call ((ret, _), Const (Cfun mthd), (Var this, _) :: args, _, CallFlags.{cf_virtual= true}) ->
          let arg_exprs = List.map args ~f:(fun (arg, _) -> compose_expr pdesc arg) in
          let ae = append_access (Cache.find pdesc (Var this)) (MethodCallAccess (mthd, arg_exprs)) in
          Cache.add_id pdesc ret ae
      | Sil.Call ((ret, _), Const (Cfun mthd), (Var this, _) :: args, _, _) ->
          (* this.mthd(...) is not virtual invocation *)
          let this_aexpr = Cache.find pdesc (Var this) in
          if String.equal (to_string this_aexpr) "this" then
            let arg_exprs = List.map args ~f:(fun (arg, _) -> compose_expr pdesc arg) in
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


  let null = Primitive (Cint IntLit.null)

  let zero = Primitive (Cint IntLit.zero)

  let one = Primitive (Cint IntLit.one)
end

include S
module Set = PrettyPrintable.MakePPSet (S)
module Map = PrettyPrintable.MakePPMap (S)

let is_abstract = function
  | AccessExpr (_, accesses) ->
      List.exists accesses ~f:(function ArrayAccess _ -> true | _ -> false)
  | _ ->
      false


let is_concrete = function AccessExpr _ -> false | Primitive _ -> true

let is_different_type _ _ = false
