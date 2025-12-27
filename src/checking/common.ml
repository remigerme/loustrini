open Z3

(** We check that the given property is a boolean. *)
let check_prop_is_bool (prop : Expr.expr) =
  match Sort.get_sort_kind (Expr.get_sort prop) with
  | BOOL_SORT -> ()
  | _ -> raise (Error "The property to check should be a boolean.")
