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
let _bool_s = Boolean.mk_sort ctx
let one = Arithmetic.Integer.mk_numeral_i ctx 1
let n_global = declare_const ctx "n" int_s

(* Storing FuncDecl *)
let func_decls = Hashtbl.create 10

let register_func_decl name in_s out_s =
  let x = declare_func ctx name in_s out_s in
  Hashtbl.replace func_decls name x

(* Storing FuncDef *)
let func_defs = ref []

(* Defining incr *)
let def_incr (x : Expr.expr) (call : int) =
  (* Naming symbols *)
  let xn = "x_" ^ string_of_int call in
  let ln = "l_" ^ string_of_int call in
  let yn = "y_" ^ string_of_int call in

  (* Defining symbols *)
  register_func_decl xn [ int_s ] int_s;
  register_func_decl ln [ int_s ] int_s;
  register_func_decl yn [ int_s ] int_s;

  let def_l =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx (Hashtbl.find func_decls ln) [ n_global ])
      (Arithmetic.mk_add ctx
         [ Expr.mk_app ctx (Hashtbl.find func_decls xn) [ n_global ]; one ])
  in

  let def_y =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx (Hashtbl.find func_decls yn) [ n_global ])
      (Arithmetic.mk_add ctx
         [
           Expr.mk_app ctx (Hashtbl.find func_decls xn) [ n_global ];
           Expr.mk_app ctx (Hashtbl.find func_decls ln) [ n_global ];
         ])
  in

  let def_x =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx (Hashtbl.find func_decls xn) [ n_global ])
      x
  in

  func_defs := def_l :: def_y :: def_x :: !func_defs;

  Expr.mk_app ctx (Hashtbl.find func_decls yn) [ n_global ]

let a = declare_func ctx "a" [ int_s ] int_s
let b = declare_func ctx "b" [ int_s ] int_s
let z = declare_func ctx "z" [ int_s ] int_s
let t = declare_func ctx "t" [ int_s ] int_s

let def_z =
  Boolean.mk_eq ctx
    (Expr.mk_app ctx z [ n_global ])
    (def_incr (Expr.mk_app ctx a [ n_global ]) 0)

let def_t =
  Boolean.mk_eq ctx
    (Expr.mk_app ctx t [ n_global ])
    (def_incr (Expr.mk_app ctx b [ n_global ]) 1)

let () = func_defs := def_z :: def_t :: !func_defs

let incr_delta n =
  let aux expr = Expr.substitute_one expr n_global n in
  let exprs = List.map aux !func_defs in
  Boolean.mk_and ctx exprs

let n = declare_const ctx "n" int_s
let d = incr_delta n
let dp = incr_delta (Arithmetic.mk_add ctx [ n; one ])
let () = print_endline (Expr.to_string d)
let () = print_endline (Expr.to_string dp)
