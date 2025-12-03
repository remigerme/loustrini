open Ast
open Ast.Typed_ast
open Ast.Asttypes
open Z3

type error = TooFewArguments | TooManyArguments | UnknownPrim

exception Error of error

type z3_env_t = {
  func_decls : (string, FuncDecl.func_decl) Hashtbl.t;
  func_defs : (string, Expr.expr -> Expr.expr) Hashtbl.t;
}

let compile_const ctx (c : const) =
  match c with
  | Cbool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | Cint i -> Arithmetic.Integer.mk_numeral_i ctx i
  | Creal r -> Arithmetic.Real.mk_numeral_s ctx (string_of_float r)

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
  | TE_op (_op, _es) -> assert false (* TODO *)
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

(** Handling a single one-to-one equation. At this point, [env] must already be
    populated with [func_decls]. This function populates the [func_defs] field
    with the definition of [x]. *)
let handle_eq_one ctx env (x : Ident.t) (e : t_expr) =
  let def_x n =
    let xn = Expr.mk_app ctx (Hashtbl.find env.func_decls x.name) [ n ] in
    let xn_body = compile_expr ctx env n 0 0 e in
    Boolean.mk_eq ctx xn xn_body
  in
  Hashtbl.add env.func_defs x.name def_x
