module F = Format

type pvar = Pvar.t

let compare_pvar x y =
  if Pvar.is_global x && Pvar.is_global y then
    if String.equal (Pvar.to_string x) (Pvar.to_string y) then 0 else Pvar.compare x y
  else Pvar.compare x y


(* Identifiers are distinguished with procedures *)
module ProcVar = struct
  type t = LogicalVar of ident | ProgramVar of pvar

  and ident = {id: Ident.t; pid: Procname.t; is_return: bool [@compare.ignore]} [@@deriving compare]

  let equal = [%compare.equal: t]

  let of_id ?(is_return = false) (id, pid) = LogicalVar {id; pid; is_return}

  let of_pvar pv = ProgramVar pv

  let of_var pid = function Var.LogicalVar id -> of_id (id, pid) | Var.ProgramVar pv -> of_pvar pv

  let dummy = LogicalVar {id= Ident.create_none (); pid= Procname.empty_block; is_return= false}

  let is_id = function LogicalVar _ -> true | _ -> false

  let is_global = function ProgramVar pv when Pvar.is_global pv -> true | _ -> false

  let is_return = function LogicalVar {is_return} -> is_return | _ -> false

  let global_procname = "_G_"

  let to_exp = function LogicalVar {id} -> Exp.Var id (* DANGER *) | ProgramVar pv -> Exp.Lvar pv

  let procname_of = function
    | LogicalVar {pid} ->
        Some pid
    | ProgramVar pv -> (
      match Pvar.get_declaring_function pv with Some pid -> Some pid | None -> None )


  let pp fmt = function
    | LogicalVar {id; pid} ->
        F.fprintf fmt "%a:%a" Procname.pp pid Ident.pp id
    | ProgramVar pv -> (
      match Pvar.get_declaring_function pv with
      | Some pid ->
          F.fprintf fmt "%a:%a" Procname.pp pid Pvar.pp_value pv
      | None ->
          F.fprintf fmt "%s:%a" global_procname Pvar.pp_value pv )


  let to_string = function LogicalVar {id} -> F.asprintf "%a" Ident.pp id | ProgramVar pv -> Pvar.to_string pv

  let hash var = Hashtbl.hash (F.asprintf "%a" pp var)
end

include ProcVar
module Map = PrettyPrintable.MakePPMap (ProcVar)
module Set = PrettyPrintable.MakePPSet (ProcVar)
