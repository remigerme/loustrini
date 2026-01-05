open Z3
open Compile.Env_kind

exception EmptyAbduct
exception Break

(** https://stackoverflow.com/questions/22132458/library-function-to-find-difference-between-two-lists-ocaml *)
let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

(** At this point, we assume [h] is non-contradictory (fair because of initial sifting).
    We perform naive pruning for now, that is we test every expression of [h].
    TODO: generate should take [p_target] as an input and should not generate inconsistent candidates. *)
let sift_wrt_p_target ctx env p_target h =
  (* First, we check p_target is non-contradictory. *)
  let solver = Solver.mk_solver ctx None in
  let n = n_global ctx in
  let n_plus_1 = n_plus_1_global ctx in
  let d_n = eqs ctx env n in
  let d_n_plus_1 = eqs ctx env n_plus_1 in
  Solver.add solver (d_n @ d_n_plus_1);
  let p_n = eval_expr_at ctx p_target n in
  match Solver.check solver [ p_n ] with
  | UNSATISFIABLE ->
      (* p_target is contradictory, abduct will ultimately return None *)
      []
  | UNKNOWN ->
      raise
        (Error "Z3 unknown when checking that p_target is non-contradictory.")
  | SATISFIABLE ->
      Solver.add solver [ p_n ];
      let non_contradictory e =
        match Solver.check solver [ e ] with
        | SATISFIABLE -> true
        | UNSATISFIABLE -> false
        | UNKNOWN ->
            raise
              (Error
                 "Z3 unknown when performing sifting for individual expression \
                  w.r.t. p_target.")
      in
      List.filter non_contradictory h

let mine ctx env v_slice p_target inputs (k : int) =
  let h = Generation.mine_without_sift ctx env v_slice in
  (* Sift based on positive examples *)
  let h = Houdini.initial_sift ctx env inputs h k in
  (* But we also need to sift w.r.t p_target *)
  sift_wrt_p_target ctx env p_target h

(** Returns a list of expressions from [p_v] making [p_target] inductive, if such a list exists.
    Ideally, I'd love to use cvc5's getAbductNext + ensuring minimality using flags.
    FOR NOW, SUCH ABDUCTS ARE FAR FROM MINIMAL. We generate way too many useless proof obligations.
    We would need to, at least, sift the generated abduct to remove what can be obviously removed.
    I think the best option by far would be to delegate this work to the SMT solver.
    According to the paper, the method presented is faster than cvc5's builtin,
    but I fail to understand how this query can generate multiple different abducts
    (and the minimality is ensured by the SMT anyway). In the VeloCT implementation:
    - hierarchical.py uses cvc5's getAbductNext,
    - learn_inv_distributed.py uses a simple getUnsatCore, I haven't understood how can we have multiple abducts with this. 
    
    Also, Z3's get_unsat_core sometimes returns one huge expression (an and with many sub-expressions)
    instead of a list of simple expressions which would be better for us. *)
let abduct ctx env p_target p_v =
  let solver = Solver.mk_solver ctx None in
  let n = n_global ctx in
  let n_plus_1 = n_plus_1_global ctx in
  (* We load solver with the system equations *)
  let d_n = eqs ctx env n in
  let d_n_plus_1 = eqs ctx env n_plus_1 in
  Solver.add solver (d_n @ d_n_plus_1);
  let p_n = eval_expr_at ctx p_target n in
  let p_n_plus_1 = eval_expr_at ctx p_target n_plus_1 in
  let p_v_n = List.map (fun e -> eval_expr_at ctx e n) p_v in
  (* We check that ^(p_v) ^ p_target is not vacuously false *)
  let q_vac = p_n :: p_v_n in
  (match Solver.check solver q_vac with
  | SATISFIABLE -> ()
  | UNSATISFIABLE ->
      raise
        (Error "Invariant candidates from which to abduct are contradictory")
  | UNKNOWN ->
      raise
        (Error
           "Z3 unknown when checking that invariant candidates from which to \
            abduct are non-contradictory"));
  (* Then we get an abduct as an UNSAT core if it exists *)
  let q_abd = Common.mk_implies ctx (p_n :: p_v_n) [ p_n_plus_1 ] in
  match Solver.check solver [ q_abd ] with
  | SATISFIABLE -> None
  | UNSATISFIABLE -> Some (Solver.get_unsat_core solver)
  | UNKNOWN -> raise (Error "Z3 unknown when abducting for H-Houdini")

(** Positive examples are given by [inputs] and [k], which denotes the length of the trace. *)
let rec h_houdini ctx env p_target p_fail inputs k =
  (* TODO: implement memoization *)
  let valid_solution = ref false in
  let h = ref [ p_target ] in
  let v_slice = Slice.slice ctx env p_target in
  let p_v = mine ctx env v_slice p_target inputs k in
  if List.is_empty p_v then raise EmptyAbduct;
  (* TODO: loop disabled for now as we cannot generate more than abduct anyway,
     so it is pointless to loop forever. Also, the whole "for p in A" part with recursive calls
     do not work as the abduct (unsat core) returned by Z3 is a massive conjunction... *)
  (* while not !valid_solution do *)
  h := [ p_target ];
  let p_v = diff p_v !p_fail in
  let a = abduct ctx env p_target p_v in
  if Option.is_none a then raise EmptyAbduct;
  let a = Option.get a in
  valid_solution := true;
  let handle_p p =
    try
      let h_sol = h_houdini ctx env p p_fail inputs k in
      h := h_sol @ !h
    with EmptyAbduct ->
      valid_solution := false;
      p_fail := p :: !p_fail;
      raise Break
  in
  (try List.iter handle_p a with Break -> ());
  (* done; *)
  !h

let learn ctx env inputs prop =
  (* We use a trace of (arbitrary) length 5 *)
  try Some (h_houdini ctx env prop (ref []) inputs 5) with EmptyAbduct -> None
