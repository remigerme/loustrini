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
(* Update *)
let x_update = declare_func ctx "x_update" [ int_s ] int_s
let y_update = declare_func ctx "y_update" [ int_s ] int_s

let update_return_s =
  Tuple.mk_sort ctx
    (Symbol.mk_string ctx "update_return_s")
    [ Symbol.mk_string ctx "f1"; Symbol.mk_string ctx "f2" ]
    [ int_s; int_s ]

let update = declare_func ctx "update" [ int_s ] update_return_s

(* Check *)
let x_check = declare_func ctx "x_check" [ int_s ] int_s
let y_check = declare_func ctx "y_check" [ int_s ] int_s
let ok = declare_func ctx "ok" [ int_s ] bool_s

let check_return_s =
  Tuple.mk_sort ctx
    (Symbol.mk_string ctx "check_return_s")
    [ Symbol.mk_string ctx "f1" ]
    [ bool_s ]

let check = declare_func ctx "check" [ int_s ] check_return_s

let def_x_update n =
  Boolean.mk_eq ctx
    (Expr.mk_app ctx x_update [ n ])
    (Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) one
       (Arithmetic.mk_add ctx
          [ Expr.mk_app ctx x_update [ Arithmetic.mk_sub ctx [ n; one ] ]; one ]))

let def_y_update n =
  let n_minus_1 = Arithmetic.mk_sub ctx [ n; one ] in
  Boolean.mk_eq ctx
    (Expr.mk_app ctx y_update [ n ])
    (Boolean.mk_ite ctx (Boolean.mk_eq ctx n zero) one
       (Arithmetic.mk_add ctx
          [
            Expr.mk_app ctx x_update [ n_minus_1 ];
            Expr.mk_app ctx y_update [ n_minus_1 ];
          ]))

let def_update n =
  let mk_tuple = Tuple.get_mk_decl update_return_s in
  let ret_val =
    Expr.mk_app ctx mk_tuple
      [ Expr.mk_app ctx x_update [ n ]; Expr.mk_app ctx y_update [ n ] ]
  in
  Boolean.mk_eq ctx (Expr.mk_app ctx update [ n ]) ret_val

let def_x_check n =
  let accessors = Tuple.get_field_decls update_return_s in
  let f1 = List.nth accessors 0 in
  Boolean.mk_eq ctx
    (Expr.mk_app ctx x_check [ n ])
    (Expr.mk_app ctx f1 [ Expr.mk_app ctx update [ n ] ])

let def_y_check n =
  let accessors = Tuple.get_field_decls update_return_s in
  let f2 = List.nth accessors 1 in
  Boolean.mk_eq ctx
    (Expr.mk_app ctx y_check [ n ])
    (Expr.mk_app ctx f2 [ Expr.mk_app ctx update [ n ] ])

let def_ok n =
  Boolean.mk_eq ctx (Expr.mk_app ctx ok [ n ])
    (Arithmetic.mk_ge ctx (Expr.mk_app ctx y_check [ n ]) zero)

let def_check n =
  let mk_tuple = Tuple.get_mk_decl check_return_s in
  let ret_val = Expr.mk_app ctx mk_tuple [ Expr.mk_app ctx ok [ n ] ] in
  Boolean.mk_eq ctx (Expr.mk_app ctx check [ n ]) ret_val

(* Validity is given by the return value of the input node, here check. *)
let valid = declare_func ctx "valid" [ int_s ] bool_s

let def_valid n =
  let accessors = Tuple.get_field_decls check_return_s in
  let f1 = List.nth accessors 0 in
  Boolean.mk_eq ctx
    (Expr.mk_app ctx valid [ n ])
    (Expr.mk_app ctx f1 [ Expr.mk_app ctx check [ n ] ])

let delta_incr n =
  Boolean.mk_and ctx
    [
      def_x_update n;
      def_y_update n;
      def_update n;
      def_x_check n;
      def_y_check n;
      def_ok n;
      def_check n;
      def_valid n;
    ]

let prop n = Expr.mk_app ctx valid [ n ]
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
let lemma n = Arithmetic.mk_ge ctx (Expr.mk_app ctx x_check [ n ]) zero
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
