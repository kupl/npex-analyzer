open! IStd
open! Vocab
module F = Format
module L = Logging
module Hashtbl = Caml.Hashtbl

module InstrNode = struct
  type t = {inode: InterNode.t; instr: Sil.instr} [@@deriving compare]

  let equal = [%compare.equal: t]

  let make inode instr = {inode; instr}

  let of_pnode pnode instr =
    let inode = InterNode.of_pnode pnode in
    {inode; instr}


  let dummy = {inode= InterNode.dummy Procname.empty_block; instr= Sil.skip_instr}

  let default = dummy

  let dummy_entry = {inode= InterNode.dummy (Procname.from_string_c_fun "NPEX_entry"); instr= Sil.skip_instr}

  let dummy_exit = {inode= InterNode.dummy (Procname.from_string_c_fun "NPEX_exit"); instr= Sil.skip_instr}

  let inode_of {inode} = inode

  let get_proc_name {inode} = InterNode.get_proc_name inode

  let get_instr {instr} = instr

  let get_instrs {instr} = Instrs.singleton instr

  let get_loc {inode} = InterNode.get_loc inode

  let list_of_pnode pnode =
    let inode = InterNode.of_pnode pnode in
    let instr_list = get_instrs_list pnode in
    List.map instr_list ~f:(fun instr -> {inode; instr})


  let pp fmt {inode; instr} =
    F.fprintf fmt "<%a, %a, %a>" InterNode.pp inode
      (Sil.pp_instr ~print_types:true Pp.text)
      instr SourceFile.pp (InterNode.get_loc inode).Location.file


  let vertex_name {inode; instr} =
    F.asprintf "\"%s-%a\"" (InterNode.to_string inode) (Sil.pp_instr ~print_types:true Pp.text) instr


  let is_last_instr {inode; instr} =
    let instrs = InterNode.get_instrs inode in
    if Instrs.is_empty instrs then false else Sil.equal_instr instr (Option.value_exn (Instrs.last instrs))


  let is_entry {inode} = InterNode.is_entry inode

  let is_exit {inode} = InterNode.is_exit inode

  let get_succs (n : t) =
    if is_last_instr n then
      List.map (InterNode.get_succs n.inode) ~f:(fun inode ->
          let instr = Instrs.nth_exn (InterNode.get_instrs inode) 0 in
          {inode; instr})
    else
      let instrs = get_instrs_list (InterNode.pnode_of n.inode) in
      let idx, _ = Option.value_exn (List.findi instrs ~f:(fun _ instr' -> Sil.equal_instr n.instr instr')) in
      let instr = List.nth_exn instrs (idx + 1) in
      let inode = n.inode in
      [{inode; instr}]


  let get_exn (n : t) =
    let exn_pnodes = Procdesc.Node.get_exn (InterNode.pnode_of n.inode) in
    List.map exn_pnodes ~f:(fun pnode ->
        let instr = Instrs.nth_exn (Procdesc.Node.get_instrs pnode) 0 in
        of_pnode pnode instr)


  let get_kind {inode} = InterNode.get_kind inode

  (* TODO:??? This introduces Out-Of-Memory
     * let _hash : (t, int) Hashtbl.t = Hashtbl.create 1214

     * let hash x =
     *   match Hashtbl.find_opt _hash x with
     *   | Some cached ->
     *       cached
     *   | _ ->
     *       let hashed = Hashtbl.hash (vertex_name x) in
     *       Hashtbl.add _hash x hashed ; hashed
  *)
  let hash x = Hashtbl.hash (vertex_name x)
end

include InstrNode
module Map = PrettyPrintable.MakePPMap (InstrNode)
module Set = PrettyPrintable.MakePPSet (InstrNode)
