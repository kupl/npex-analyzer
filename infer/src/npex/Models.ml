open! IStd

let new_names = List.map ~f:Procname.from_string_c_fun ["__new"; "__new_array"]

let is_new procname = List.mem ~equal:Procname.equal new_names procname

let is_model = is_new
