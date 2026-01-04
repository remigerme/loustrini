open Z3
open Compile.Env_kind
open Compile.Common

(** Returns the list of names of variables on which variable [name] depends on.
    We exclude toplevel arguments. *)
let slice_name env name =
  let deps = Hashtbl.find env.depends_on name in
  List.filter_map (get_var_opt env) deps

(** Extract names of all variables (streams) in [p_target]. *)
let rec extract_names ctx p_target =
  let names =
    List.fold_left
      (fun acc e -> extract_names ctx e @! acc)
      [] (Expr.get_args p_target)
  in
  let f = Expr.get_func_decl p_target in
  match FuncDecl.get_decl_kind f with
  | Z3enums.OP_UNINTERPRETED ->
      let name = FuncDecl.get_name f in
      let name = Symbol.get_string name in
      add_if_missing name names
  | _ -> names

(** Returns the list of [typed_var_t] on which the property [p_target] depends on. *)
let slice ctx env p_target =
  let names = extract_names ctx p_target in
  flatten_no_dup (List.map (slice_name env) names)
