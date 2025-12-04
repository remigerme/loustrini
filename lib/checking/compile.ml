open Ast
open Ast.Typed_ast
open Ast.Asttypes
open Z3
open Env

type error =
  | TooFewArguments
  | TooManyArguments
  | UnknownPrim
  | InvalidOpArguments
  | InvalidTupleArityIf
  | InvalidTupleArityEq

exception Error of error

(************************************)
(* First step: defining func_decls. *)
(************************************)

let ident_to_str (x : Ident.t) = Printf.sprintf "%s__%i" x.name x.id

let base_ty_to_sort ctx ty =
  match ty with
  | Tbool -> Boolean.mk_sort ctx
  | Tint -> Arithmetic.Integer.mk_sort ctx
  | Treal -> Arithmetic.Real.mk_sort ctx

let define_func_decls_node ctx env (node : t_node) =
  let int_s = Arithmetic.Integer.mk_sort ctx in
  let define_func_decl (v : typed_var) =
    let x, ty = v in
    let name = ident_to_str x in
    let out_s = base_ty_to_sort ctx ty in
    let decl = FuncDecl.mk_func_decl_s ctx name [ int_s ] out_s in
    Hashtbl.add env.func_decls name decl
  in
  List.iter define_func_decl node.tn_input;
  List.iter define_func_decl node.tn_output;
  List.iter define_func_decl node.tn_local

(*******************************************************************)
(* Second step: compiling stream definitions (func_defs) using the *
 * "let def_x : Expr.expr -> Expr.expr = fun n -> ..." technique.  *)
(*******************************************************************)

(** `if` is polymorphic in Lustre and supports tuples. And we consider it is the
    only polymorphic operator (cf.
    https://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v4/distrib/lustre_tutorial.pdf).
    We emit one [Expr.expr] per member of the tuple. *)
let rec compile_if ctx eb (e1 : Expr.expr list) (e2 : Expr.expr list) =
  match (e1, e2) with
  | [], [] -> []
  | t1 :: q1, t2 :: q2 -> Boolean.mk_ite ctx eb t1 t2 :: compile_if ctx eb q1 q2
  | _, _ -> raise (Error InvalidTupleArityIf)

let compile_const ctx (c : const) =
  match c with
  | Cbool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | Cint i -> Arithmetic.Integer.mk_numeral_i ctx i
  | Creal r -> Arithmetic.Real.mk_numeral_s ctx (string_of_float r)

(** [es] contains the arguments given to the operator. Each argument is
    (potentially) a tuple, although in practice, only the `if` operator is
    polymorphic and supports tuples. *)
let compile_op ctx op (es : Expr.expr list list) =
  let rec extract_val (e : Expr.expr list list) =
    match e with
    | [] -> []
    | [ x ] :: q -> x :: extract_val q
    | _ -> raise (Error InvalidOpArguments)
  in
  match (op, es) with
  | Op_eq, [ [ e1 ]; [ e2 ] ] -> [ Boolean.mk_eq ctx e1 e2 ]
  | Op_neq, [ [ e1 ]; [ e2 ] ] ->
      [ Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2) ]
  | Op_lt, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_lt ctx e1 e2 ]
  | Op_le, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_le ctx e1 e2 ]
  | Op_gt, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_gt ctx e1 e2 ]
  | Op_ge, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_ge ctx e1 e2 ]
  | (Op_add | Op_add_f), e -> [ Arithmetic.mk_add ctx (extract_val e) ]
  | (Op_sub | Op_sub_f), [ [ e ] ] -> [ Arithmetic.mk_unary_minus ctx e ]
  | (Op_sub | Op_sub_f), e -> [ Arithmetic.mk_sub ctx (extract_val e) ]
  | (Op_mul | Op_mul_f), e -> [ Arithmetic.mk_mul ctx (extract_val e) ]
  | (Op_div | Op_div_f), [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_div ctx e1 e2 ]
  | Op_mod, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.Integer.mk_mod ctx e1 e2 ]
  | Op_not, [ [ e ] ] -> [ Boolean.mk_not ctx e ]
  | Op_and, e -> [ Boolean.mk_and ctx (extract_val e) ]
  | Op_or, e -> [ Boolean.mk_or ctx (extract_val e) ]
  | Op_impl, [ [ e1 ]; [ e2 ] ] -> [ Boolean.mk_implies ctx e1 e2 ]
  (* Here e1 and e2 can be tuples! We generate an expression for each member of the tuple. *)
  | Op_if, [ [ eb ]; e1; e2 ] -> compile_if ctx eb e1 e2
  | _ -> raise (Error InvalidOpArguments)

let arg_n ctx n n_pre =
  (* We could just use the generic expression in the else branch. *)
  (* But it is less readable when debugging. *)
  if n_pre = 0 then n
  else Arithmetic.mk_sub ctx [ n; Arithmetic.Integer.mk_numeral_i ctx n_pre ]

let rec compile_expr_desc ctx env n n_pre n_arr (e : t_expr_desc) =
  match e with
  | TE_const c -> [ compile_const ctx c ]
  | TE_ident x ->
      let arg = arg_n ctx n n_pre in
      [ Expr.mk_app ctx (Hashtbl.find env.func_decls (ident_to_str x)) [ arg ] ]
  | TE_op (op, es) ->
      let e = List.map (compile_expr ctx env n n_pre n_arr) es in
      compile_op ctx op e
  | TE_app (_f, _args) -> assert false (* TODO plumbing *)
  | TE_prim (f, args) -> (
      (* We need exactly one argument. *)
      match args with
      | [] -> raise (Error TooFewArguments)
      | [ arg ] -> (
          (* This one argument cannot be a tuple. *)
          match compile_expr ctx env n n_pre n_arr arg with
          | [] (* Should never happen *) -> assert false
          | [ earg ] -> (
              match f.name with
              | "real_of_int" -> [ Arithmetic.Integer.mk_int2real ctx earg ]
              | "int_of_real" -> [ Arithmetic.Real.mk_real2int ctx earg ]
              | _ -> raise (Error UnknownPrim))
          (* Argument was a tuple. *)
          | _ -> raise (Error TooManyArguments))
      | _ -> raise (Error TooManyArguments))
  | TE_arrow (e1, e2) ->
      let einit = compile_expr ctx env n n_pre n_arr e1 in
      let egen = compile_expr ctx env n n_pre (n_arr + 1) e2 in
      let etest =
        Boolean.mk_eq ctx n (Arithmetic.Integer.mk_numeral_i ctx n_arr)
      in
      compile_if ctx etest einit egen
  | TE_pre e -> compile_expr ctx env n (n_pre + 1) n_arr e
  (* To support nested tuples, we simply flatten them by flattening the list of lists. *)
  (* Why do one even uses nested tuples in Lustre??? *)
  | TE_tuple es ->
      let e = List.map (compile_expr ctx env n n_pre n_arr) es in
      List.flatten e

and compile_expr ctx env n n_pre n_arr (e : t_expr) =
  compile_expr_desc ctx env n n_pre n_arr e.texpr_desc

(************************************************)
(* Third step: compiling a node (aka plumbing). *)
(************************************************)

(** Compiling a single many-to-many equation. At this point, [env] must already
    be populated with [func_decls]. This function populates the [func_defs]
    fields with the definitions of each stream defined by the equation. *)
let compile_eq ctx env (eq : t_equation) =
  let def_i i x =
    let name = ident_to_str x in
    let def_x n =
      let xn = Expr.mk_app ctx (Hashtbl.find env.func_decls name) [ n ] in
      (* This is inefficient cause we will compile a tuple of length k a total of k times. *)
      (* But it is not trivial to store the expression once and for all because [n] is a parameter of def_x. *)
      let xn_body = List.nth (compile_expr ctx env n 0 0 eq.teq_expr) i in
      Boolean.mk_eq ctx xn xn_body
    in
    Hashtbl.add env.func_defs name def_x
  in
  List.iteri def_i eq.teq_patt.tpatt_desc

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
