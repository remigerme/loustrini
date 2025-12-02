open Z3

let declare_const ctx name sort =
  let sym = Symbol.mk_string ctx name in
  Expr.mk_const ctx sym sort

let declare_func ctx name in_t out_t =
  let func = FuncDecl.mk_func_decl_s ctx name in_t out_t in
  func

(* Z3 setup *)
let ctx = mk_context []
let int_s = Arithmetic.Integer.mk_sort ctx
let bool_s = Boolean.mk_sort ctx
let zero = Arithmetic.Integer.mk_numeral_i ctx 0
let one = Arithmetic.Integer.mk_numeral_i ctx 1

(* Declaring function symbols *)
let tic = declare_func ctx "tic" [ int_s ] bool_s
let ok = declare_func ctx "ok" [ int_s ] bool_s
let cpt = declare_func ctx "cpt" [ int_s ] int_s

let def_cpt n =
  let ite1 =
    Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) zero
      (Expr.mk_app ctx cpt [ Arithmetic.mk_sub ctx [ n; one ] ])
  in
  let ite2 = Boolean.mk_ite ctx (Expr.mk_app ctx tic [ n ]) one zero in
  Boolean.mk_eq ctx
    (Expr.mk_app ctx cpt [ n ])
    (Arithmetic.mk_add ctx [ ite1; ite2 ])

let def_ok n =
  Boolean.mk_eq ctx (Expr.mk_app ctx ok [ n ])
    (Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) (Boolean.mk_true ctx)
       (Arithmetic.mk_le ctx
          (Expr.mk_app ctx cpt [ Arithmetic.mk_sub ctx [ n; one ] ])
          (Expr.mk_app ctx cpt [ n ])))

let delta_incr n = Boolean.mk_and ctx [ def_cpt n; def_ok n ]
let prop n = Expr.mk_app ctx ok [ n ]
let solver = Solver.mk_solver ctx None

(* Initialization *)
let () =
  let s =
    match
      Solver.check solver [ delta_incr zero; Boolean.mk_not ctx (prop zero) ]
    with
    | UNSATISFIABLE -> "unsat initialization"
    | SATISFIABLE -> "sat initialization"
    | UNKNOWN -> "unknwon initialization"
  in
  print_endline s

(* Consecution *)
let () =
  let n = declare_const ctx "n" int_s in
  let n_plus_1 = Arithmetic.mk_add ctx [ n; one ] in
  let s =
    match
      Solver.check solver
        [
          delta_incr n;
          delta_incr n_plus_1;
          prop n;
          Boolean.mk_not ctx (prop n_plus_1);
        ]
    with
    | SATISFIABLE -> "sat consecution"
    | UNSATISFIABLE -> "unsat consecution"
    | UNKNOWN -> "unknown consecution"
  in
  print_endline s
