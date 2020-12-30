module Make (Key : PrettyPrintable.PrintableOrderedType) (Value : AbstractDomain.WithBottom) : sig
  include module type of AbstractDomain.Map (Key) (Value)

  val find : Key.t -> t -> Value.t

  val weak_update : Key.t -> Value.t -> t -> t

  val strong_update : Key.t -> Value.t -> t -> t
end
