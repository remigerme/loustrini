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
  mutable state_vars : state_var_t list;
  sort_from_ids : (Ast.Ident.t, Sort.sort) Hashtbl.t;
  node_from_ids : (Ast.Ident.t, Ast.Typed_ast.t_node) Hashtbl.t;
  node_calls : (Ast.Typed_ast.t_node, int) Hashtbl.t;
}

let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nVariables (%d):\n" (List.length env.vars);
  List.iter
    (fun (var : var_t) ->
      Printf.printf "- %s = %s\n" var.name (Expr.to_string var.def))
    env.vars;
  Printf.printf "\nState variables (%d):\n" (List.length env.state_vars);
  List.iter
    (fun var ->
      Printf.printf "- %s: init = %s ;;; next = %s\n" var.name
        (match var.init with None -> "" | Some i -> Expr.to_string i)
        (Expr.to_string var.next))
    env.state_vars;
  Printf.printf "=======================\n"

let name_prime name = name ^ "_p"
let expr_of_var ctx (v : var_t) = Expr.mk_const_s ctx v.name v.sort
let expr_of_state_var ctx (s : state_var_t) = Expr.mk_const_s ctx s.name s.sort

let expr_of_var_prime ctx (v : var_t) =
  Expr.mk_const_s ctx (name_prime v.name) v.sort

let expr_of_state_var_prime ctx (s : state_var_t) =
  Expr.mk_const_s ctx (name_prime s.name) s.sort

(** Returns the expression where every variable has been replaced by its primed version. *)
let prime_expr ctx env (e : Expr.expr) =
  (* Fetching all variables *)
  let vars = List.map (expr_of_var ctx) env.vars in
  let state_vars = List.map (expr_of_state_var ctx) env.state_vars in
  let all_vars = vars @ state_vars in

  (* Fetching all primed variables *)
  let vars_prime = List.map (expr_of_var_prime ctx) env.vars in
  let state_vars_prime =
    List.map (expr_of_state_var_prime ctx) env.state_vars
  in
  let all_vars_prime = vars_prime @ state_vars_prime in

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
  List.filter_map def_init env.state_vars

(** Returns equations satisfied by primed [state_vars] when doing one step. *)
let trans ctx env =
  let def_next (s : state_var_t) =
    let s_prime = expr_of_state_var_prime ctx s in
    Boolean.mk_eq ctx s_prime s.next
  in
  List.map def_next env.state_vars
