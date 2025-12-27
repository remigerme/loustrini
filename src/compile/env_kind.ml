open Z3
open Ast
open Ast.Typed_ast

(** Shorthands for instantiating sorts. *)

let int_s ctx = Arithmetic.Integer.mk_sort ctx
let bool_s ctx = Boolean.mk_sort ctx
let real_s ctx = Arithmetic.Real.mk_sort ctx

(** The global time counter, which is then replaced by different instances using [Expr.substitute].
    Use [eval_expr_with] to perform the substitution. *)
let n_global ctx = Expr.mk_const_s ctx "n" (Arithmetic.Integer.mk_sort ctx)

(** Evaluate an expression for a given value of [n]. *)
let eval_expr_at ctx expr n = Expr.substitute_one expr (n_global ctx) n

type var_t = { name : string; sort : Sort.sort; def : Expr.expr }

type z3_env_t = {
  mutable vars : var_t list;
  (* To handle all cases where we only have an Ast.Ident.t without a base type (e.g. TE_ident) *)
  sort_from_ids : (Ast.Ident.t, Sort.sort) Hashtbl.t;
  (* Storing node info *)
  node_from_ids : (Ident.t, t_node) Hashtbl.t;
  node_calls : (t_node, int) Hashtbl.t;
}

(** Returns the [FuncDecl.func_decl] associated with var [v]. *)
let decl_of_var ctx (v : var_t) =
  FuncDecl.mk_func_decl_s ctx v.name [ int_s ctx ] v.sort

let decl_of_name ctx name sort =
  FuncDecl.mk_func_decl_s ctx name [ int_s ctx ] sort

(** Returns the expression [v(n)]. *)
let expr_of_var ctx (v : var_t) =
  let decl = decl_of_var ctx v in
  FuncDecl.apply decl [ n_global ctx ]

(** Returns the expression defining [v]: [v(n) = def] where "n" might appear in [def]. *)
let def_of_var ctx (v : var_t) =
  let vn = expr_of_var ctx v in
  Boolean.mk_eq ctx vn v.def

(** Return the equations of the system at time [n]. *)
let eqs ctx env n =
  let defs = List.map (def_of_var ctx) env.vars in
  List.map (fun e -> eval_expr_at ctx e n) defs

let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nVariables (%d):\n" (List.length env.vars);
  List.iter
    (fun v -> Printf.printf "- %s: %s\n" v.name (Expr.to_string v.def))
    env.vars;
  Printf.printf "=======================\n"
