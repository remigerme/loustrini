open Ast
open Ast.Typed_ast
open Ast.Asttypes
open Z3

type error =
  | TooFewArguments
  | TooManyArguments
  | UnknownPrim
  | InvalidOpArguments

exception Error of error

type z3_env_t = {
  func_decls : (string, FuncDecl.func_decl) Hashtbl.t;
  func_defs : (string, Expr.expr -> Expr.expr) Hashtbl.t;
}

(************************************)
(* First step: defining func_decls. *)
(************************************)

let base_ty_to_sort ctx ty =
  match ty with
  | Tbool -> Boolean.mk_sort ctx
  | Tint -> Arithmetic.Integer.mk_sort ctx
  | Treal -> Arithmetic.Real.mk_sort ctx

let define_func_decls_node ctx env (node : t_node) =
  let int_s = Arithmetic.Integer.mk_sort ctx in
  let define_func_decl (v : typed_var) =
    let x, ty = v in
    let out_s = base_ty_to_sort ctx ty in
    let decl = FuncDecl.mk_func_decl_s ctx x.name [ int_s ] out_s in
    Hashtbl.add env.func_decls x.name decl
  in
  List.iter define_func_decl node.tn_input;
  List.iter define_func_decl node.tn_output;
  List.iter define_func_decl node.tn_local

(*******************************************************************)
(* Second step: compiling stream definitions (func_defs) using the *
 * "let def_x : Expr.expr -> Expr.expr = fun n -> ..." technique.  *)
(*******************************************************************)

let compile_const ctx (c : const) =
  match c with
  | Cbool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | Cint i -> Arithmetic.Integer.mk_numeral_i ctx i
  | Creal r -> Arithmetic.Real.mk_numeral_s ctx (string_of_float r)

let compile_op ctx op (es : Expr.expr list) =
  match (op, es) with
  | Op_eq, [ e1; e2 ] -> Boolean.mk_eq ctx e1 e2
  | Op_neq, [ e1; e2 ] -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2)
  | Op_lt, [ e1; e2 ] -> Arithmetic.mk_lt ctx e1 e2
  | Op_le, [ e1; e2 ] -> Arithmetic.mk_le ctx e1 e2
  | Op_gt, [ e1; e2 ] -> Arithmetic.mk_gt ctx e1 e2
  | Op_ge, [ e1; e2 ] -> Arithmetic.mk_ge ctx e1 e2
  | (Op_add | Op_add_f), e -> Arithmetic.mk_add ctx e
  | (Op_sub | Op_sub_f), [ e ] -> Arithmetic.mk_unary_minus ctx e
  | (Op_sub | Op_sub_f), e -> Arithmetic.mk_sub ctx e
  | (Op_mul | Op_mul_f), e -> Arithmetic.mk_mul ctx e
  | (Op_div | Op_div_f), [ e1; e2 ] -> Arithmetic.mk_div ctx e1 e2
  | Op_mod, [ e1; e2 ] -> Arithmetic.Integer.mk_mod ctx e1 e2
  | Op_not, [ e ] -> Boolean.mk_not ctx e
  | Op_and, e -> Boolean.mk_and ctx e
  | Op_or, e -> Boolean.mk_or ctx e
  | Op_impl, [ e1; e2 ] -> Boolean.mk_implies ctx e1 e2
  | Op_if, [ eb; e1; e2 ] -> Boolean.mk_ite ctx eb e1 e2
  | _ -> raise (Error InvalidOpArguments)

let rec compile_expr_desc ctx env n n_pre n_arr (e : t_expr_desc) =
  match e with
  | TE_const c -> compile_const ctx c
  | TE_ident x ->
      let arg =
        if n_pre = 0 then n
        else
          Arithmetic.mk_sub ctx [ n; Arithmetic.Integer.mk_numeral_i ctx n_pre ]
      in
      Expr.mk_app ctx (Hashtbl.find env.func_decls x.name) [ arg ]
  | TE_op (op, es) ->
      let e = List.map (compile_expr ctx env n n_pre n_arr) es in
      compile_op ctx op e
  | TE_app (f, args) ->
      Expr.mk_app ctx
        (Hashtbl.find env.func_decls f.name)
        (List.map (compile_expr ctx env n n_pre n_arr) args)
  | TE_prim (f, args) -> (
      match args with
      | [] -> raise (Error TooFewArguments)
      | [ arg ] -> (
          let earg = compile_expr ctx env n n_pre n_arr arg in
          match f.name with
          | "real_of_int" -> Arithmetic.Integer.mk_int2real ctx earg
          | "int_of_real" -> Arithmetic.Real.mk_real2int ctx earg
          | _ -> raise (Error UnknownPrim))
      | _ -> raise (Error TooManyArguments))
  | TE_arrow (e1, e2) ->
      let einit = compile_expr ctx env n n_pre n_arr e1 in
      let egen = compile_expr ctx env n n_pre (n_arr + 1) e2 in
      let etest =
        Boolean.mk_eq ctx n (Arithmetic.Integer.mk_numeral_i ctx n_arr)
      in
      Boolean.mk_ite ctx etest einit egen
  | TE_pre e -> compile_expr ctx env n (n_pre + 1) n_arr e
  | TE_tuple _es -> assert false (* TODO *)

and compile_expr ctx env n n_pre n_arr (e : t_expr) =
  compile_expr_desc ctx env n n_pre n_arr e.texpr_desc

(************************************************)
(* Third step: compiling a node (aka plumbing). *)
(************************************************)

(** Compiling a single one-to-one equation. At this point, [env] must already be
    populated with [func_decls]. This function populates the [func_defs] field
    with the definition of [x]. *)
let compile_eq_one_to_one ctx env (x : Ident.t) (e : t_expr) =
  let def_x n =
    let xn = Expr.mk_app ctx (Hashtbl.find env.func_decls x.name) [ n ] in
    let xn_body = compile_expr ctx env n 0 0 e in
    Boolean.mk_eq ctx xn xn_body
  in
  Hashtbl.add env.func_defs x.name def_x

let compile_eq _ctx _env (_eq : t_equation) = () (* TODO plumbing *)

(** Compiling a single node. At this point, [env] must already be populated with
    [func_decls] of all functions. *)
let compile_node ctx env (node : t_node) =
  List.iter (compile_eq ctx env) node.tn_equs

(********************************************)
(* Fourth step: putting everything together *)
(********************************************)

let compile_file ctx (f : t_file) =
  (* Create a new env *)
  let func_decls = Hashtbl.create 50 in
  let func_defs = Hashtbl.create 50 in
  let env = { func_decls; func_defs } in

  (* Define all func_decls *)
  List.iter (define_func_decls_node ctx env) f;

  (* Compile all nodes *)
  List.iter (compile_node ctx env) f;

  env
