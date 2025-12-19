open Z3
open Compile.Env_trans

let prune (h : Expr.expr list) (cex : Model.model) =
  List.filter
    (fun e ->
      (* We do not enable model completion, as it will over-prune. *)
      match Model.eval cex e false with
      | Some r -> Boolean.is_true r
      (* We are conservative to avoid over-pruning. *)
      | None -> true)
    h

let step solver ctx env eqs eqs_prime trans_eqs (h : Expr.expr list) =
  let h_prime = List.map (prime_expr ctx env) h in
  let query_cons =
    Common.mk_implies ctx (h @ eqs @ eqs_prime @ trans_eqs) h_prime
  in
  match Solver.check solver [ query_cons ] with
  | SATISFIABLE ->
      let cex = Option.get (Solver.get_model solver) in
      Some (prune h cex)
  | UNSATISFIABLE -> None
  | UNKNOWN -> raise (Error "Z3 answered unknown when performing Houdini sift")

let rec loop solver ctx env eqs eqs_prime trans_eqs (h : Expr.expr list) =
  match step solver ctx env eqs eqs_prime trans_eqs h with
  | None -> h
  | Some h_pruned -> loop solver ctx env eqs eqs_prime trans_eqs h_pruned

let start_loop ctx env (h : Expr.expr list) =
  let solver = Solver.mk_solver ctx None in
  let eqs = get_eqs ctx env in
  let eqs_prime = get_eqs_prime ctx env in
  let trans_eqs = trans ctx env in
  loop solver ctx env eqs eqs_prime trans_eqs h

let learn ctx env =
  let h = Generation.gen_inv ctx env in
  (* Here, we would need to sift h based on positive examples, that is, some traces of execution. *)
  start_loop ctx env h

(***********)
(* PROBLEM *)
(***********)

(* What if h contains contradictory predicates (e.g. x >= 0 and x < 0)?
   The consecution will be UNSAT because h is...
   Providing positive examples might filter some contradictory states, but not all of them (e.g. uninitialized variables).
   Can we have a real guarantee on h? *)
