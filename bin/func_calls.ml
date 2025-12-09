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

(* Storing FuncDecl *)
let func_decls = Hashtbl.create 10

let register_func_decl name in_s out_s =
  let x = declare_func ctx name in_s out_s in
  Hashtbl.replace func_decls name x

(* Storing FuncDef *)
let func_defs = ref []

(* Defining incr *)
let def_incr _x call =
  (* Naming symbols *)
  let xn = "x_" ^ string_of_int call in
  let ln = "l_" ^ string_of_int call in
  let yn = "y_" ^ string_of_int call in

  (* Defining symbols *)
  register_func_decl xn [ int_s ] int_s;
  register_func_decl ln [ int_s ] int_s;
  register_func_decl yn [ int_s ] int_s;

  let def_l n =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx (Hashtbl.find func_decls ln) [ n ])
      (Arithmetic.mk_add ctx
         [ Expr.mk_app ctx (Hashtbl.find func_decls xn) [ n ]; one ])
  in

  let def_y n =
    Boolean.mk_eq ctx
      (Expr.mk_app ctx (Hashtbl.find func_decls yn) [ n ])
      (Arithmetic.mk_add ctx
         [
           Expr.mk_app ctx (Hashtbl.find func_decls xn) [ n ];
           Expr.mk_app ctx (Hashtbl.find func_decls ln) [ n ];
         ])
  in

  (* We'd like to plumb inputs _x here too, but we can't as we need a function of n, 
     and at this point _x is already evaluated for a given n. *)
  func_defs := def_l :: def_y :: !func_defs

let a = declare_func ctx "a" [ int_s ] int_s
let b = declare_func ctx "b" [ int_s ] int_s
let z = declare_func ctx "z" [ int_s ] int_s
let t = declare_func ctx "t" [ int_s ] int_s

let def_z n =
  (* Here providing a [ n ] would prevent correctly plumbing inputs. *)
  def_incr () 0;
  Boolean.mk_eq ctx (Expr.mk_app ctx z [ n ])
    (Expr.mk_app ctx (Hashtbl.find func_decls "y_0") [ n ])

let def_t n =
  (* Here providing b [ n ] would prevent correctly plumbing inputs. *)
  def_incr () 1;
  Boolean.mk_eq ctx (Expr.mk_app ctx t [ n ])
    (Expr.mk_app ctx (Hashtbl.find func_decls "y_1") [ n ])

let def_x0 n =
  Boolean.mk_eq ctx
    (Expr.mk_app ctx (Hashtbl.find func_decls "x_0") [ n ])
    (Expr.mk_app ctx a [ n ])

let def_x1 n =
  Boolean.mk_eq ctx
    (Expr.mk_app ctx (Hashtbl.find func_decls "x_1") [ n ])
    (Expr.mk_app ctx b [ n ])

let () = func_defs := def_z :: def_t :: def_x0 :: def_x1 :: !func_defs
let incr_delta n = Boolean.mk_and ctx (List.map (fun x -> x n) !func_defs)
let n = declare_const ctx "n" int_s
let d = incr_delta n
let () = print_endline (Expr.to_string d)
