module Domain = SpecCheckerDomain

val is_model : Procname.t -> Sil.instr -> bool

val exec_model :
     Domain.t
  -> Procdesc.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> Procname.t
  -> Ident.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> Domain.t list
