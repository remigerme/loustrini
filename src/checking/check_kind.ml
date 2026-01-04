open Z3
open Compile.Env_kind

type learning_mode = Houdini | HHoudini

let mode_to_string mode =
  match mode with Houdini -> "Houdini" | HHoudini -> "H-Houdini"

let eval_inv_with ctx inv n = List.map (fun h -> eval_expr_at ctx h n) inv

let prove mode ctx env prop =
  (* We check that the given property is a boolean. *)
  Common.check_prop_is_bool prop;

  (* Trying to learn a strengthened inductive invariant *)
  let default_inputs = default_inputs ctx env in
  let inv =
    match mode with
    | Houdini -> prop :: Invariant.Houdini.learn ctx env default_inputs
    | HHoudini -> (
        match Invariant.Hhoudini.learn ctx env default_inputs prop with
        | Some h -> h
        | None ->
            raise (Error "H-Houdini couldn't learn an inductive invariant"))
  in
  Printf.printf "Learned invariants with %s (%d)\n" (mode_to_string mode)
    (List.length inv);
  List.iteri (fun i e -> Printf.printf "%d %s\n" i (Expr.to_string e)) inv;

  (* Creating Z3 variables *)
  let solver = Solver.mk_solver ctx None in
  let zero = Arithmetic.Integer.mk_numeral_i ctx 0 in
  let one = Arithmetic.Integer.mk_numeral_i ctx 1 in
  let n = Arithmetic.Integer.mk_const_s ctx "n" in
  let n_plus_1 = Arithmetic.mk_add ctx [ n; one ] in

  (* Creating Z3 system expressions *)
  let d_n = eqs ctx env n in
  let d_n_plus_1 = eqs ctx env n_plus_1 in
  let inv_n = eval_inv_with ctx inv n in
  let inv_n_plus_1 = eval_inv_with ctx inv n_plus_1 in

  (* Checking invariant is non-contradictory *)
  let q_non_contradictory = d_n @ d_n_plus_1 @ inv_n in
  (match Solver.check solver q_non_contradictory with
  | SATISFIABLE -> print_endline "Learned invariant is non-contradictory."
  | UNSATISFIABLE -> raise (Error "The learned invariant is contradictory.")
  | UNKNOWN -> raise (Error "Invariant is non-contradictory: unknown from Z3."));

  (* Invariant implies desired property *)
  let q_imp = Invariant.Common.mk_implies ctx (d_n @ inv_n) [ prop ] in
  (match Solver.check solver [ q_imp ] with
  | SATISFIABLE ->
      print_endline "ERROR: learned invariant does not imply desired property."
  | UNSATISFIABLE -> print_endline "Learned invariant implies desired property."
  | UNKNOWN -> raise (Error "Invariant implies goal property: unknown from Z3."));

  (* Initiation *)
  let d_0 = eqs ctx env zero in
  let inv_0 = eval_inv_with ctx inv zero in
  let q_0 = Invariant.Common.mk_implies ctx d_0 inv_0 in
  (match Solver.check solver [ q_0 ] with
  | SATISFIABLE -> print_endline "ERROR: Initiation failed (SAT)."
  | UNSATISFIABLE -> print_endline "SUCCESS: Initiation holds (UNSAT)."
  | UNKNOWN -> raise (Error "Initiation: unknown from Z3"));

  (* Consecution *)
  let hyp_n = d_n @ d_n_plus_1 @ inv_n in
  let q_cons = Invariant.Common.mk_implies ctx hyp_n inv_n_plus_1 in
  match Solver.check solver [ q_cons ] with
  | SATISFIABLE -> print_endline "ERROR: Consecution failed (SAT)."
  | UNSATISFIABLE -> print_endline "SUCCESS: Consecution holds (UNSAT)."
  | UNKNOWN -> raise (Error "Consecution: unknown from Z3")
