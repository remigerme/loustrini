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
let x = declare_func ctx "x" [ int_s ] int_s
let y = declare_func ctx "y" [ int_s ] int_s
let ok = declare_func ctx "ok" [ int_s ] bool_s

let def_x n =
  Boolean.mk_eq ctx (Expr.mk_app ctx x [ n ])
    (Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) one
       (Arithmetic.mk_add ctx
          [ Expr.mk_app ctx x [ Arithmetic.mk_sub ctx [ n; one ] ]; one ]))

let def_y n =
  let n_minus_1 = Arithmetic.mk_sub ctx [ n; one ] in
  Boolean.mk_eq ctx (Expr.mk_app ctx y [ n ])
    (Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) one
       (Arithmetic.mk_add ctx
          [ Expr.mk_app ctx x [ n_minus_1 ]; Expr.mk_app ctx y [ n_minus_1 ] ]))

let def_ok n =
  Boolean.mk_eq ctx (Expr.mk_app ctx ok [ n ])
    (Arithmetic.mk_ge ctx (Expr.mk_app ctx y [ n ]) zero)

let delta_incr n = Boolean.mk_and ctx [ def_x n; def_y n; def_ok n ]
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
          Arithmetic.mk_ge ctx n zero;
          delta_incr n;
          delta_incr n_plus_1;
          prop n;
          Boolean.mk_not ctx (prop n_plus_1);
        ]
    with
    | UNSATISFIABLE -> "unsat consecution"
    | SATISFIABLE -> "sat consecution"
    | UNKNOWN -> "unknwon consecution"
  in
  print_endline s;
  match Solver.get_model solver with
  | None -> ()
  | Some m ->
      print_endline "Found model:";
      print_endline (Model.to_string m)

(* Strengthening *)
let lemma n = Arithmetic.mk_ge ctx (Expr.mk_app ctx x [ n ]) zero
let strong_prop n = Boolean.mk_and ctx [ prop n; lemma n ]

(* Initialization *)
let () =
  let s =
    match
      Solver.check solver [ delta_incr zero; Boolean.mk_not ctx (lemma zero) ]
    with
    | UNSATISFIABLE -> "unsat (lemma) initialization"
    | SATISFIABLE -> "sat (lemma) initialization"
    | UNKNOWN -> "unknwon (lemma) initialization"
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
          Arithmetic.mk_ge ctx n zero;
          delta_incr n;
          delta_incr n_plus_1;
          strong_prop n;
          Boolean.mk_not ctx (strong_prop n_plus_1);
        ]
    with
    | UNSATISFIABLE -> "unsat (strengthened) consecution"
    | SATISFIABLE -> "sat (strengthened) consecution"
    | UNKNOWN -> "unknwon (strengthened) consecution"
  in
  print_endline s
