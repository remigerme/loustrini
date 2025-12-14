open Z3
open Env_trans

type error = NonBooleanProperty

exception Error of error

(** Helper as [Boolean.mk_implies] do not support lists of expressions. *)
let mk_implies ctx (p : Expr.expr list) (q : Expr.expr list) =
  let nq = List.map (fun e -> Boolean.mk_not ctx e) q in
  Boolean.mk_and ctx (p @ nq)

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
  let query0 = mk_implies ctx (get_eqs ctx env @ init ctx env) [ prop ] in
  (match Solver.check solver [ query0 ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown");

  (* Consecution *)
  let eqs = get_eqs ctx env in
  let eqs_prime = get_eqs_prime ctx env in
  let trans_eqs = trans ctx env in
  let prop_prime = prime_expr ctx env prop in
  let query_ind = mk_implies ctx (eqs @ eqs_prime @ trans_eqs) [ prop_prime ] in
  match Solver.check solver [ query_ind ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown"
