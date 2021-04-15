module Domain = SpecCheckerDomain

type exec =
     Domain.t
  -> Procdesc.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> Procname.t
  -> Ident.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> Domain.t list

val is_model : Procname.t -> Sil.instr -> bool

val exec_model : exec

(* module Call : sig
  val dispatch : (Tenv.t, exec, unit) ProcnameDispatcher.Call.dispatcher
end *)
