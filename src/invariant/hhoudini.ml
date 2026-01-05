open Z3
open Compile.Env_kind

exception EmptyAbduct
exception Break

(** https://stackoverflow.com/questions/22132458/library-function-to-find-difference-between-two-lists-ocaml *)
let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

(** Returns a list of expressions from [p_v] making [p_target] inductive, if such a list exists. *)
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

let rec h_houdini ctx env p_target p_fail positive =
  (* TODO: implement memoization *)
  let valid_solution = ref false in
  let h = ref [ p_target ] in
  let v_slice = Slice.slice ctx env p_target in
  let p_v = Generation.mine ctx env v_slice in
  while not !valid_solution do
    h := [ p_target ];
    let p_v = diff p_v !p_fail in
    let a = abduct ctx env p_target p_v in
    if Option.is_none a then raise EmptyAbduct;
    let a = Option.get a in
    valid_solution := true;
    let handle_p p =
      try
        let h_sol = h_houdini ctx env p p_fail positive in
        h := h_sol @ !h
      with EmptyAbduct ->
        valid_solution := false;
        p_fail := p :: !p_fail;
        raise Break
    in
    try List.iter handle_p a with Break -> ()
  done;
  !h

let learn ctx env _inputs prop =
  let positive =
    []
    (*TODO*)
  in
  try Some (h_houdini ctx env prop (ref []) positive) with EmptyAbduct -> None
