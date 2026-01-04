open Z3
open Ast
open Ast.Typed_ast

(** Shorthands for instantiating sorts. *)

let int_s ctx = Arithmetic.Integer.mk_sort ctx
let bool_s ctx = Boolean.mk_sort ctx
let real_s ctx = Arithmetic.Real.mk_sort ctx

(** The global time counter, which is then replaced by different instances using [Expr.substitute].
    Use [eval_expr_with] to perform the substitution. *)
let n_global ctx = Arithmetic.Integer.mk_const_s ctx "n"

let n_plus_1_global ctx =
  let one = Arithmetic.Integer.mk_numeral_i ctx 1 in
  Arithmetic.mk_add ctx [ n_global ctx; one ]

(** Evaluate an expression for a given value of [n]. *)
let eval_expr_at ctx expr n = Expr.substitute_one expr (n_global ctx) n

(** For hardcoded numerals in the program. *)
type const_num_t = Int of int | Real of float

type var_t = { name : string; sort : Sort.sort; def : Expr.expr }

type z3_env_t = {
  mutable vars : var_t list;
  toplevel_args : Common.toplevel_arg_t list;
  mutable hardcoded_numerals : const_num_t list;
  (* Slicing oracle for H-Houdini *)
  depends_on : (string, string list) Hashtbl.t;
  (* To handle all cases where we only have an Ast.Ident.t without a base type (e.g. TE_ident) *)
  sort_from_ids : (Ast.Ident.t, Sort.sort) Hashtbl.t;
  (* Storing node info *)
  node_from_ids : (Ident.t, t_node) Hashtbl.t;
  node_calls : (t_node, int) Hashtbl.t;
}

let get_var env name = List.find (fun v -> v.name = name) env.vars
let get_var_opt env name = List.find_opt (fun v -> v.name = name) env.vars

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

(** Assigns values to toplevel arguments:
    - bools are set to true,
    - ints are set to 0,
    - reals are set to 0.0. *)
let default_inputs ctx env =
  let default_val (arg : Common.toplevel_arg_t) =
    let def =
      match Sort.get_sort_kind arg.sort with
      | BOOL_SORT -> Boolean.mk_true ctx
      | INT_SORT -> Arithmetic.Integer.mk_numeral_i ctx 0
      | REAL_SORT -> Arithmetic.Real.mk_numeral_s ctx "0.0"
      | _ -> raise (Error "to")
    in
    { name = arg.name; sort = arg.sort; def }
  in
  List.map default_val env.toplevel_args

(** THE ultimate debugging tool. Good luck (to myself)! *)
let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nVariables (%d):\n" (List.length env.vars);
  List.iter
    (fun (v : var_t) ->
      Printf.printf "- %s: \n\t- %s\n\t- %s\n" v.name (Expr.to_string v.def)
        (List.fold_left
           (fun acc d -> if acc = "" then d else acc ^ ", " ^ d)
           ""
           (Hashtbl.find env.depends_on v.name)))
    env.vars;
  Printf.printf "\nToplevel args (%d):\n" (List.length env.toplevel_args);
  List.iter
    (fun (v : Common.toplevel_arg_t) ->
      Printf.printf "- %s: %s\n" v.name (Sort.to_string v.sort))
    env.toplevel_args;
  Printf.printf "=======================\n"
