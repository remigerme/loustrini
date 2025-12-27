open Z3
open Compile.Env_kind

let int_s ctx = Arithmetic.Integer.mk_sort ctx
let bool_s ctx = Boolean.mk_sort ctx

let mk_decl ctx name =
  FuncDecl.mk_func_decl_s ctx name [ int_s ctx ] (bool_s ctx)

let eval_n ctx name =
  let decl = mk_decl ctx name in
  FuncDecl.apply decl [ n_global ctx ]

let eval_n_plus_1 ctx name =
  let decl = mk_decl ctx name in
  let one = Arithmetic.Integer.mk_numeral_i ctx 1 in
  let n_plus_1 = Arithmetic.mk_add ctx [ n_global ctx; one ] in
  FuncDecl.apply decl [ n_plus_1 ]

(** Generate [x(n) = true]. *)
let gen_inv_true ctx (x : var_t) =
  let xn = expr_of_var ctx x in
  Boolean.mk_eq ctx xn (Boolean.mk_true ctx)

(** Generate [x(n) = false]. *)
let gen_inv_false ctx (x : var_t) =
  let xn = expr_of_var ctx x in
  Boolean.mk_eq ctx xn (Boolean.mk_false ctx)

(** Generate [x(n) = y(n)]. The following are disabled for now: 
    - [x(n) = y(n+1)],
    - [x(n+1) = y(n)]. *)
let gen_inv_eqs ctx (x : var_t) (y : var_t) =
  let xn = expr_of_var ctx x in
  let yn = expr_of_var ctx y in
  let xn_yn = Boolean.mk_eq ctx xn yn in
  (* let one = Arithmetic.Integer.mk_numeral_i ctx 1 in
  let n_plus_1 = Arithmetic.mk_add ctx [ n_global ctx; one ] in
  let xn_yn1 = Boolean.mk_eq ctx xn (eval_expr_at ctx yn n_plus_1) in
  let xn1_yn = Boolean.mk_eq ctx (eval_expr_at ctx xn n_plus_1) yn in *)
  [ xn_yn (* ; xn_yn1; xn1_yn *) ]

(** Generate [x(n) != y(n)]. The following are disabled for now:
    - [x(n) != y(n+1)],
    - [x(n+1) != y(n)]. *)
let gen_inv_neqs ctx (x : var_t) (y : var_t) =
  List.map (Boolean.mk_not ctx) (gen_inv_eqs ctx x y)

(** [vars] is the list of all boolean variables. *)
let gen_inv_for_vars ctx (vars : var_t list) =
  let trues = List.map (gen_inv_true ctx) vars in
  let falses = List.map (gen_inv_false ctx) vars in
  let lower_triangle l =
    let rec aux = function
      | [] -> []
      | hd :: tl -> List.map (fun e -> (e, hd)) tl @ aux tl
    in
    aux l
  in
  let pairs = lower_triangle vars in
  let eqs = List.map (fun (n1, n2) -> gen_inv_eqs ctx n1 n2) pairs in
  let neqs = List.map (fun (n1, n2) -> gen_inv_neqs ctx n1 n2) pairs in
  trues @ falses @ List.flatten eqs @ List.flatten neqs

(** Instantiate invariants using the following template:
    ib ::= b = true | b = false | b1 = b2 | b1 = not(b2)
    where b, b1, b2 denote boolean variables. *)
let gen_inv ctx env =
  let is_bool_s s = Sort.equal s (bool_s ctx) in
  let vars = List.filter (fun (v : var_t) -> is_bool_s v.sort) env.vars in
  gen_inv_for_vars ctx vars
