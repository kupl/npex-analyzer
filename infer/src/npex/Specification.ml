open! IStd
module F = Format
module L = Logging

module Formula = struct
  type formula = Atom of atom | Neg of formula

  and atom = True | Predicate of func * term list

  and func = Unary of unop | Binary of binop

  and unop = IsConstant | IsImmutable

  and binop = Equals | IsFunctionOf

  and term = AccessExpr.t [@@deriving compare]

  let rec pp_formula fmt = function
    | Atom atom ->
        F.fprintf fmt "%a" pp_atom atom
    | Neg formula ->
        F.fprintf fmt "!(%a)" pp_formula formula


  and pp_atom fmt = function
    | True ->
        F.fprintf fmt "%s" "True"
    | Predicate (func, terms) ->
        F.fprintf fmt "%a(%a)" pp_func func pp_term_list terms


  and pp_func fmt = function Unary unop -> pp_unop fmt unop | Binary binop -> pp_binop fmt binop

  and pp_unop fmt = function
    | IsConstant ->
        F.fprintf fmt "%s" "IsConstant"
    | IsImmutable ->
        F.fprintf fmt "%s" "IsImmutable"


  and pp_binop fmt = function
    | Equals ->
        F.fprintf fmt "%s" "Equals"
    | IsFunctionOf ->
        F.fprintf fmt "%s" "IsFunctionOf"


  and pp_term = AccessExpr.pp

  and pp_term_list fmt terms = Pp.comma_seq ~print_env:Pp.text pp_term fmt terms

  let true_formula = Atom True

  let app_of func terms = Predicate (func, terms)

  let rec get_func_and_terms = function
    | Atom (Predicate (fn, ts)) ->
        (fn, ts)
    | Neg formula ->
        get_func_and_terms formula
    | formula ->
        L.(die InternalError "Formula %a has no predicate" pp_formula formula)
end

module Specification = struct
  open Formula

  type t = {mthd: Procname.t; pre: formula; post: formula; id: string [@compare.ignore]} [@@deriving compare]

  let pp fmt {mthd; pre; post; id} =
    F.fprintf fmt "@[<v>===== Spec %s =====@,Method: %a@,@Pre:  %a@,@Post: %a@]@." id Procname.pp mthd pp_formula
      pre pp_formula post


  let _cnt = ref 0

  let get_count () =
    _cnt := !_cnt + 1 ;
    !_cnt - 1


  let dummy = {mthd= Procname.from_string_c_fun "NPEX_dummy"; pre= Atom True; post= Atom True; id= "Dummy"}

  let create ~prefix ~mthd ~pre ~post = {mthd; pre; post; id= F.asprintf "%s_%d" prefix (get_count ())}

  let to_marshal marhsalled_path spec =
    Utils.with_file_out marhsalled_path ~f:(fun oc -> Marshal.to_channel oc spec [])


  let to_text path spec =
    Utils.with_file_out path ~f:(fun oc -> F.fprintf (F.formatter_of_out_channel oc) "%a@." pp spec)
end

include Specification
module Set = PrettyPrintable.MakePPSet (Specification)

module Conjunctions = PrettyPrintable.MakePPSet (struct
  include Formula

  type t = formula [@@deriving compare]

  let pp = pp_formula
end)

let from_marshal_all () =
  Utils.directory_fold
    (fun acc path ->
      if String.is_suffix path ~suffix:Config.npex_specification_extension then
        Set.add (Utils.with_file_in path ~f:Marshal.from_channel) acc
      else acc)
    Set.empty Config.npex_specifications_directory
  |> Set.elements


let to_marshal_all spec_list : unit =
  if not (Sys.file_exists_exn Config.npex_specifications_directory) then
    Unix.mkdir Config.npex_specifications_directory ;
  List.iter spec_list ~f:(fun spec ->
      to_marshal
        (F.asprintf "%s/%s%s" Config.npex_specifications_directory spec.id Config.npex_specification_extension)
        spec ;
      to_text (F.asprintf "%s/%s.text" Config.npex_specifications_directory spec.id) spec)
