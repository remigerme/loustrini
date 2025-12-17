open Z3
open Env

type error = NonBooleanProperty

exception Error of error

(** Helper as [Boolean.mk_implies] do not support lists of expressions. *)
let mk_implies ctx (p : Expr.expr list) (q : Expr.expr list) =
  let nq = List.map (fun e -> Boolean.mk_not ctx e) q in
  Boolean.mk_and ctx (p @ nq)

let eval_expr_with ctx expr n = Expr.substitute_one expr (n_global ctx) n

let delta_incr ctx env n =
  let exprs = List.map (fun e -> eval_expr_with ctx e n) env.func_defs in
  Boolean.mk_and ctx exprs

let prove ctx env prop =
  (* We check that the given property is a boolean. *)
  let () =
    match Sort.get_sort_kind (Expr.get_sort prop) with
    | BOOL_SORT -> ()
    | _ -> raise (Error NonBooleanProperty)
  in

  (* Creating a solver *)
  let solver = Solver.mk_solver ctx None in

  (* Base case *)
  let zero = Arithmetic.Integer.mk_numeral_i ctx 0 in
  let delta_incr0 = delta_incr ctx env zero in
  let p0 = eval_expr_with ctx prop zero in
  let query0 = mk_implies ctx [ delta_incr0 ] [ p0 ] in
  (match Solver.check solver [ query0 ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown");

  (* Consecution *)
  let one = Arithmetic.Integer.mk_numeral_i ctx 1 in
  let n = Expr.mk_const_s ctx "n" (Arithmetic.Integer.mk_sort ctx) in
  let n_plus_1 = Arithmetic.mk_add ctx [ n; one ] in
  let dn = delta_incr ctx env n in
  let dn_plus_1 = delta_incr ctx env n_plus_1 in
  let pn = eval_expr_with ctx prop n in
  let pn_plus_1 = eval_expr_with ctx prop n_plus_1 in
  let query_ind = mk_implies ctx [ dn; dn_plus_1; pn ] [ pn_plus_1 ] in
  match Solver.check solver [ query_ind ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown"
