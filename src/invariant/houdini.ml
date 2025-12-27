open Z3
open Compile.Env_kind

let eval_n_plus_1 ctx e = eval_expr_at ctx e (n_plus_1_global ctx)

(* Example prunning (because my head hurts)
  - h = p ^ q
  - p(n) ^ q(n) ^ not (p(n+1) ^ q(n+1))
    - UNSAT: yeepee
    - SAT: exists cex, not (p(n+1) ^ q(n+1)) (cex) is true
           exists cex, p ^ q (cex) is false
           exists cex  p (cex) false or q (cex) false
           we remove such clauses
*)

(** Prune [h] according to evaluation of [cex] on expressions of [h(n)].
    For consecution, use [n = n_plus_1], for initial sifting, use [n = zero, one, ...]. *)
let prune ctx (h : Expr.expr list) (n : Expr.expr) (cex : Model.model) =
  List.filter
    (fun e ->
      let e_n = eval_expr_at ctx e n in
      (* We do not enable model completion, as it will over-prune. *)
      match Model.eval cex e_n false with
      | Some r -> Boolean.is_true r
      (* We are conservative to avoid over-pruning. *)
      | None -> true)
    h

(* *)

let step solver ctx (h : Expr.expr list) =
  let h_n_plus_1 = List.map (eval_n_plus_1 ctx) h in
  (* The solver is already loaded with system equations *)
  let q_cons = Common.mk_implies ctx h h_n_plus_1 in
  match Solver.check solver [ q_cons ] with
  | SATISFIABLE ->
      let cex = Option.get (Solver.get_model solver) in
      Some (prune ctx h (n_plus_1_global ctx) cex)
  | UNSATISFIABLE -> None
  | UNKNOWN -> raise (Error "Z3 unknown in second loop of Houdini")

(** Iterates until [h] reaches a fixpoint (the empty list in the worst case).
    [solver] must be loaded with [d_n] and [d_n_plus_1]. *)
let rec loop solver ctx (h : Expr.expr list) =
  match step solver ctx h with
  | None -> h
  | Some h_pruned -> loop solver ctx h_pruned

let step_init solver ctx h k =
  let k_var = Arithmetic.Integer.mk_numeral_i ctx k in
  let h_k = List.map (fun e -> eval_expr_at ctx e k_var) h in
  match Solver.check solver [ Common.mk_implies ctx [] h_k ] with
  | SATISFIABLE ->
      let cex = Option.get (Solver.get_model solver) in
      Some (prune ctx h k_var cex)
  | UNSATISFIABLE -> None
  | UNKNOWN -> raise (Error "Z3 unknown when performing initial sift")

(** Iterates until [h] reaches a fixpoint according to values [h(k)].
    IMPORTANT: solver must be loaded with a trace delta(0) ^ ... delta(k).
    Note that if properties in [h] refer not only to [n] but to next variables ([n+1], ...),
    then we need a longer trace to constrain all variables.
    Worst case, this is sound and we simply don't filter potentially invalid properties. *)
let rec loop_init solver ctx (h : Expr.expr list) (k : int) =
  match step_init solver ctx h k with
  | None -> h
  | Some h_pruned -> loop_init solver ctx h_pruned k

let initial_sift ctx env inputs (h : Expr.expr list) =
  let solver = Solver.mk_solver ctx None in
  (* For now, we only use the initial state to perform the initial sift. We could use a longer trace. *)
  let d = 1 in
  let trace = Simulation.get_trace ctx env inputs d in
  Solver.add solver trace;
  let range_k = List.init d (fun x -> x) in
  List.fold_left (fun acc_h k -> loop_init solver ctx acc_h k) h range_k

let learn ctx env inputs =
  let h = Generation.gen_inv ctx env in
  (* Here, we perform the initial sift of h based on positive examples, that is, some trace of execution. *)
  let h = initial_sift ctx env inputs h in
  (* We need to make sure h is satisfiable else the implication is vacuously true. *)
  (* We also load the solver for future use. *)
  let solver = Solver.mk_solver ctx None in
  let n = n_global ctx in
  let n_plus_1 = n_plus_1_global ctx in
  let d_n = eqs ctx env n in
  let d_n_plus_1 = eqs ctx env n_plus_1 in
  Solver.add solver (d_n @ d_n_plus_1);
  (match Solver.check solver h with
  | SATISFIABLE -> ()
  | UNSATISFIABLE ->
      raise (Error "Invariant candidates are contradictory after initial sift.")
  | UNKNOWN ->
      raise
        (Error
           "Z3 unknown when checking invariant candidates are \
            non-contradictory after initial sift"));
  loop solver ctx h
