open Z3

type var_t = { name : string; sort : Sort.sort; def : Expr.expr }

type state_var_t = {
  name : string;
  sort : Sort.sort;
  (* Might be none if the init value is not specified (e.g. state storing a `pre`). *)
  init : Expr.expr option;
  next : Expr.expr;
}

type z3_env_t = {
  mutable vars : var_t list;
  mutable pre_vars : state_var_t list;
  mutable arrow_vars : state_var_t list;
  sort_from_ids : (Ast.Ident.t, Sort.sort) Hashtbl.t;
  node_from_ids : (Ast.Ident.t, Ast.Typed_ast.t_node) Hashtbl.t;
  node_calls : (Ast.Typed_ast.t_node, int) Hashtbl.t;
  mutable max_depth_pre : int;
}

let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nVariables (%d):\n" (List.length env.vars);
  List.iter
    (fun (var : var_t) ->
      Printf.printf "- %s = %s\n" var.name (Expr.to_string var.def))
    env.vars;
  Printf.printf "\nPre variables (%d):\n" (List.length env.pre_vars);
  List.iter
    (fun var ->
      Printf.printf "- %s: init = %s ;;; next = %s\n" var.name
        (match var.init with None -> "" | Some i -> Expr.to_string i)
        (Expr.to_string var.next))
    env.pre_vars;
  Printf.printf "\nArrow variables (%d):\n" (List.length env.arrow_vars);
  List.iter
    (fun var ->
      Printf.printf "- %s: init = %s ;;; next = %s\n" var.name
        (match var.init with None -> "" | Some i -> Expr.to_string i)
        (Expr.to_string var.next))
    env.arrow_vars;
  Printf.printf "=======================\n"

let name_prime name = name ^ "_p"
let expr_of_var ctx (v : var_t) = Expr.mk_const_s ctx v.name v.sort
let expr_of_state_var ctx (s : state_var_t) = Expr.mk_const_s ctx s.name s.sort

let expr_of_var_prime ctx (v : var_t) =
  Expr.mk_const_s ctx (name_prime v.name) v.sort

let expr_of_state_var_prime ctx (s : state_var_t) =
  Expr.mk_const_s ctx (name_prime s.name) s.sort

(** Returns (and creates it if necessary) the nth state variable for arrows. *)
let arrow_state_var ctx env (n_arr : int) =
  let k = List.length env.arrow_vars in
  (* Checking if variable already exists. *)
  if n_arr < k then List.nth env.arrow_vars (k - n_arr - 1)
  else if (* Checking we did not skip a variable. *) n_arr <> k then
    raise (Error (Printf.sprintf "Skipped the variable %i for arrows" k))
  else (* We create a new state variable. *)
    let name = "S_arr_" ^ string_of_int n_arr in
    let first = n_arr = 0 in
    let init = if first then Boolean.mk_true ctx else Boolean.mk_false ctx in
    let bool_s = Boolean.mk_sort ctx in
    let next =
      if first then Boolean.mk_false ctx
      else Boolean.mk_const_s ctx ("S_arr_" ^ string_of_int (n_arr - 1))
    in
    let state_var = { name; sort = bool_s; init = Some init; next } in
    env.arrow_vars <- state_var :: env.arrow_vars;
    state_var

(** Returns the expression where every variable has been replaced by its primed version. *)
let prime_expr ctx env (e : Expr.expr) =
  (* Fetching all variables *)
  let vars = List.map (expr_of_var ctx) env.vars in
  let pre_vars = List.map (expr_of_state_var ctx) env.pre_vars in
  let arrow_vars = List.map (expr_of_state_var ctx) env.arrow_vars in
  let all_vars = vars @ pre_vars @ arrow_vars in

  (* Fetching all primed variables *)
  let vars_prime = List.map (expr_of_var_prime ctx) env.vars in
  let pre_vars_prime = List.map (expr_of_state_var_prime ctx) env.pre_vars in
  let arrow_vars_prime =
    List.map (expr_of_state_var_prime ctx) env.arrow_vars
  in
  let all_vars_prime = vars_prime @ pre_vars_prime @ arrow_vars_prime in

  (* Replacing every variable by its primed version *)
  Expr.substitute e all_vars all_vars_prime

let get_eqs ctx env =
  let eq_var v = Boolean.mk_eq ctx (expr_of_var ctx v) v.def in
  let eqs_var = List.map eq_var env.vars in
  eqs_var

let get_eqs_prime ctx env =
  let eqs = get_eqs ctx env in
  List.map (prime_expr ctx env) eqs

(** Returns equations satisfied by [state_vars] at initiation. *)
let init ctx env =
  let def_init (s : state_var_t) =
    match s.init with
    | None -> None
    | Some e -> Some (Boolean.mk_eq ctx (expr_of_state_var ctx s) e)
  in
  List.filter_map def_init env.pre_vars
  @ List.filter_map def_init env.arrow_vars

(** Returns equations satisfied by primed [state_vars] when doing one step.
    This includes equations to avoid that two state arrow vars are simultaneously true. *)
let trans ctx env =
  let def_next (s : state_var_t) =
    let s_prime = expr_of_state_var_prime ctx s in
    Boolean.mk_eq ctx s_prime s.next
  in
  let not_both_true (es, et) =
    Boolean.mk_not ctx (Boolean.mk_and ctx [ es; et ])
  in
  let lower_triangle l =
    let rec aux = function
      | [] -> []
      | hd :: tl -> List.map (fun e -> (e, hd)) tl @ aux tl
    in
    aux l
  in
  let arrow_exprs = List.map (expr_of_state_var ctx) env.arrow_vars in
  let at_most_one_true = List.map not_both_true (lower_triangle arrow_exprs) in
  List.map def_next env.pre_vars
  @ List.map def_next env.arrow_vars
  @ at_most_one_true
