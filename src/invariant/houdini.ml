open Z3
open Compile.Env_trans

type error = Z3_unknown | VacuouslyTrue

exception Error of error

let prune (h : Expr.expr list) (cex : Model.model) =
  List.filter
    (fun e ->
      (* We do not enable model completion, as it will over-prune. *)
      match Model.eval cex e false with
      | Some r -> Boolean.is_true r
      (* We are conservative to avoid over-pruning. *)
      | None -> true)
    h

let step solver ctx env (h : Expr.expr list) =
  let h_prime = List.map (prime_expr ctx env) h in
  let query_cons = Common.mk_implies ctx h h_prime in
  match Solver.check solver [ query_cons ] with
  | SATISFIABLE ->
      let cex = Option.get (Solver.get_model solver) in
      Some (prune h cex)
  | UNSATISFIABLE -> None
  | UNKNOWN -> raise (Error Z3_unknown)

(** Iterates until h reaches a fixpoint (the empty list in the worst case).
    [solver] must be loaded with [eqs], [eqs_prime], and [trans_eqs]. *)
let rec loop solver ctx env (h : Expr.expr list) =
  match step solver ctx env h with
  | None -> h
  | Some h_pruned -> loop solver ctx env h_pruned

let initial_sift_on_state solver eqs h =
  Solver.reset solver;
  Solver.add solver eqs;
  List.filter
    (fun e ->
      match Solver.check solver [ e ] with
      | UNSATISFIABLE -> false
      | SATISFIABLE -> true
      | UNKNOWN -> raise (Error Z3_unknown))
    h

let initial_sift ctx env (h : Expr.expr list) =
  let solver = Solver.mk_solver ctx None in
  let d = Simulation.get_max_depth_pre env in
  let trace = Simulation.get_trace ctx env d in
  List.fold_left
    (fun acc_h eqs -> initial_sift_on_state solver eqs acc_h)
    h trace

let learn ctx env =
  let h = Generation.gen_inv ctx env in
  (* Here, we perform the initial sift of h based on positive examples, that is, some trace of execution. *)
  let h = initial_sift ctx env h in
  (* We need to make sure h is satisfiable else the implication is vacuously true. *)
  let eqs = get_eqs ctx env in
  let eqs_prime = get_eqs_prime ctx env in
  let trans_eqs = trans ctx env in
  let solver = Solver.mk_solver ctx None in
  (* We load the solver for future use. *)
  Solver.add solver (eqs @ eqs_prime @ trans_eqs);
  (match Solver.check solver h with
  | UNSATISFIABLE -> raise (Error VacuouslyTrue)
  | SATISFIABLE -> ()
  | UNKNOWN -> raise (Error Z3_unknown));
  loop solver ctx env h
