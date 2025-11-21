(* Manual OCaml equivalent of file:///./../examples/incr.smt2 using Z3 bindings. *)

open Z3

let declare_symbol ctx name sort =
  let sym = Symbol.mk_string ctx name in
  Expr.mk_const ctx sym sort

let () =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in

  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let bool_sort = Boolean.mk_sort ctx in

  (* Declare functions *)
  let tic = FuncDecl.mk_func_decl_s ctx "tic" [ int_sort ] bool_sort in
  let aux = FuncDecl.mk_func_decl_s ctx "aux" [ int_sort ] bool_sort in
  let cpt = FuncDecl.mk_func_decl_s ctx "cpt" [ int_sort ] int_sort in

  (* Constants *)
  let zero = Arithmetic.Integer.mk_numeral_i ctx 0 in
  let one = Arithmetic.Integer.mk_numeral_i ctx 1 in

  (* Define recursive function cpt using quantifier *)
  (* For all n: cpt(n) = if n = 0 then 0 else cpt(n-1) + (if tic(n) then 1 else 0) *)
  let n_var = declare_symbol ctx "n" int_sort in

  let cpt_n = FuncDecl.apply cpt [ n_var ] in
  let cpt_n_minus_1 =
    FuncDecl.apply cpt [ Arithmetic.mk_sub ctx [ n_var; one ] ]
  in
  let tic_n = FuncDecl.apply tic [ n_var ] in
  let ite_tic = Boolean.mk_ite ctx tic_n one zero in
  let cpt_rec_case = Arithmetic.mk_add ctx [ cpt_n_minus_1; ite_tic ] in
  let cpt_def =
    Boolean.mk_ite ctx (Boolean.mk_eq ctx n_var zero) zero cpt_rec_case
  in

  let cpt_constraint = Boolean.mk_eq ctx cpt_n cpt_def in
  let cpt_forall =
    Quantifier.mk_forall_const ctx [ n_var ] cpt_constraint None [] [] None None
  in
  Solver.add solver [ Quantifier.expr_of_quantifier cpt_forall ];

  (* Define ok(n) = if n = 0 then true else aux(n) *)
  let ok_expr n =
    Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) (Boolean.mk_true ctx)
      (FuncDecl.apply aux [ n ])
  in

  (* Assert: forall n: (aux(n) <=> cpt(n-1) <= cpt(n)) *)
  let m_var = declare_symbol ctx "m" int_sort in
  let aux_m = FuncDecl.apply aux [ m_var ] in
  let cpt_m = FuncDecl.apply cpt [ m_var ] in
  let cpt_m_minus_1 =
    FuncDecl.apply cpt [ Arithmetic.mk_sub ctx [ m_var; one ] ]
  in
  let le_constraint = Arithmetic.mk_le ctx cpt_m_minus_1 cpt_m in

  let main_constraint =
    Boolean.mk_and ctx
      [
        Boolean.mk_implies ctx aux_m le_constraint;
        Boolean.mk_implies ctx le_constraint aux_m;
      ]
  in

  let main_forall =
    Quantifier.mk_forall_const ctx [ m_var ] main_constraint None [] [] None
      None
  in
  Solver.add solver [ Quantifier.expr_of_quantifier main_forall ];

  (* Assert (not (ok n)) for some constant n *)
  let n_const = declare_symbol ctx "n_const" int_sort in
  Solver.add solver [ Boolean.mk_not ctx (ok_expr n_const) ];

  (* Check satisfiability *)
  print_endline "unsat iff ok is always true:";
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> print_endline "unsat"
  | Solver.SATISFIABLE -> print_endline "sat"
  | Solver.UNKNOWN -> print_endline "unknown"
