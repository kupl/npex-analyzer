open! IStd

module Make (Key : PrettyPrintable.PrintableOrderedType) (Value : AbstractDomain.WithBottom) = struct
  include AbstractDomain.Map (Key) (Value)

  let find loc m = try find loc m with _ -> Value.bottom

  let weak_update loc v reg = if Value.is_bottom v then reg else add loc (Value.join v (find loc reg)) reg

  let strong_update loc v reg = add loc v reg
end
