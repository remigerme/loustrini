(* open Z3
open Compile.Env_trans

(** Helper as [Boolean.mk_implies] do not support lists of expressions. *)
let mk_implies ctx (p : Expr.expr list) (q : Expr.expr list) =
  let nq = List.map (fun e -> Boolean.mk_not ctx e) q in
  Boolean.mk_and ctx (p @ nq)

let prove ctx env prop =
  (* We check that the given property is a boolean. *)
  let () =
    match Sort.get_sort_kind (Expr.get_sort prop) with
    | BOOL_SORT -> ()
    | _ -> raise (Error "The property to check should be a boolean.")
  in

  (* Creating a solver *)
  let solver = Solver.mk_solver ctx None in

  (* Trying to learn a strengthened inductive invariant *)
  (* TODO: INPUTS *)
  let inv = Invariant.Houdini.learn ctx env [] in

  (* Checking invariant is non-contradictory *)
  (match Solver.check solver inv with
  | SATISFIABLE -> ()
  | UNSATISFIABLE -> raise (Error "The learned invariant is contradictory.")
  | UNKNOWN -> raise (Error "Invariant is non-contradictory: unknown from Z3."));

  (* Invariant implies desired property *)
  let query_imp = mk_implies ctx (get_eqs ctx env @ inv) [ prop ] in
  (match Solver.check solver [ query_imp ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown");

  (* Base case *)
  let query0 = mk_implies ctx (get_eqs ctx env @ init ctx env) inv in
  (match Solver.check solver [ query0 ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown");

  (* Consecution *)
  let eqs = get_eqs ctx env in
  let eqs_prime = get_eqs_prime ctx env in
  let trans_eqs = trans ctx env in
  let inv_prime = List.map (prime_expr ctx env) inv in
  let query_cons =
    mk_implies ctx (inv @ eqs @ eqs_prime @ trans_eqs) inv_prime
  in
  match Solver.check solver [ query_cons ] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown" *)
