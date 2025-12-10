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
  | ExpectedValueGotTuple
  | InvalidTupleArityIf
  | InvalidTupleArityEq

exception Error of error

(*********)
(* Utils *)
(*********)

(** The global time counter, which is then replaced by different instances using [Expr.substitute]. *)
let n_global ctx = Expr.mk_const_s ctx "n" (Arithmetic.Integer.mk_sort ctx)

(** Retrieve string identifier of a node. For streams, use [ident_to_str_call] instead. *)
let ident_to_str (x : Ident.t) = Printf.sprintf "%s__%i" x.name x.id

(** Retrieve string identifier of a stream. *)
let ident_to_str_call (x : Ident.t) (call : int) =
  Printf.sprintf "%s__call__%i" (ident_to_str x) call

(** Flatten a list of expressions assuming each expression is simple (not a tuple).
    Else it cannot be flattened and an error is emitted. *)
let rec extract_simple_args (e : Expr.expr list list) =
  match e with
  | [] -> []
  | [ x ] :: q -> x :: extract_simple_args q
  | _ -> raise (Error ExpectedValueGotTuple)

(** Get the [Expr.expr] corresponding to the actual value of [n] (taking [n_pre] into account). *)
let arg_n ctx n_pre =
  (* We could just use the generic expression in the else branch. *)
  (* But it is less readable when debugging. *)
  let n = n_global ctx in
  if n_pre = 0 then n
  else Arithmetic.mk_sub ctx [ n; Arithmetic.Integer.mk_numeral_i ctx n_pre ]

(*****************)
(* Compile const *)
(*****************)

let compile_const ctx (c : const) =
  match c with
  | Cbool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | Cint i -> Arithmetic.Integer.mk_numeral_i ctx i
  | Creal r -> Arithmetic.Real.mk_numeral_s ctx (string_of_float r)

(**************)
(* Compile op *)
(**************)

(** `if` is polymorphic in Lustre and supports tuples. And we consider it is the only polymorphic operator 
    (cf. https://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v4/distrib/lustre_tutorial.pdf).
    We emit one [Expr.expr] per member of the tuple. *)
let rec compile_if ctx eb (e1 : Expr.expr list) (e2 : Expr.expr list) =
  match (e1, e2) with
  | [], [] -> []
  | t1 :: q1, t2 :: q2 -> Boolean.mk_ite ctx eb t1 t2 :: compile_if ctx eb q1 q2
  | _, _ -> raise (Error InvalidTupleArityIf)

(** [es] contains the arguments given to the operator. Each argument is (potentially) a tuple, 
    although in practice, only the `if` operator is polymorphic and supports tuples. *)
let compile_op ctx op (es : Expr.expr list list) =
  match (op, es) with
  | Op_eq, [ [ e1 ]; [ e2 ] ] -> [ Boolean.mk_eq ctx e1 e2 ]
  | Op_neq, [ [ e1 ]; [ e2 ] ] ->
      [ Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2) ]
  | Op_lt, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_lt ctx e1 e2 ]
  | Op_le, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_le ctx e1 e2 ]
  | Op_gt, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_gt ctx e1 e2 ]
  | Op_ge, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_ge ctx e1 e2 ]
  | (Op_add | Op_add_f), e -> [ Arithmetic.mk_add ctx (extract_simple_args e) ]
  | (Op_sub | Op_sub_f), [ [ e ] ] -> [ Arithmetic.mk_unary_minus ctx e ]
  | (Op_sub | Op_sub_f), e -> [ Arithmetic.mk_sub ctx (extract_simple_args e) ]
  | (Op_mul | Op_mul_f), e -> [ Arithmetic.mk_mul ctx (extract_simple_args e) ]
  | (Op_div | Op_div_f), [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.mk_div ctx e1 e2 ]
  | Op_mod, [ [ e1 ]; [ e2 ] ] -> [ Arithmetic.Integer.mk_mod ctx e1 e2 ]
  | Op_not, [ [ e ] ] -> [ Boolean.mk_not ctx e ]
  | Op_and, e -> [ Boolean.mk_and ctx (extract_simple_args e) ]
  | Op_or, e -> [ Boolean.mk_or ctx (extract_simple_args e) ]
  | Op_impl, [ [ e1 ]; [ e2 ] ] -> [ Boolean.mk_implies ctx e1 e2 ]
  (* Here e1 and e2 can be tuples! We generate an expression for each member of the tuple. *)
  | Op_if, [ [ eb ]; e1; e2 ] -> compile_if ctx eb e1 e2
  | _ -> raise (Error InvalidOpArguments)

(****************)
(* Compile prim *)
(****************)

let compile_prim ctx (f : Ident.t) (arg : Expr.expr) =
  match f.name with
  | "real_of_int" -> [ Arithmetic.Integer.mk_int2real ctx arg ]
  | "int_of_real" -> [ Arithmetic.Real.mk_real2int ctx arg ]
  | _ -> raise (Error UnknownPrim)

(***************)
(* Compile app *)
(***************)

let base_ty_to_sort ctx ty =
  match ty with
  | Tbool -> Boolean.mk_sort ctx
  | Tint -> Arithmetic.Integer.mk_sort ctx
  | Treal -> Arithmetic.Real.mk_sort ctx

(** Performs the following actions:
    - update the call counter for the node,
    - define a [FuncDecl] for each variable of the node,
    - update [env] with all these new instances,
    - return the list of inputs (we need to link them to their actual values).
*)
let define_func_decls_node ctx env (node : t_node) =
  (* Updating call counter *)
  let call = 1 + Hashtbl.find env.node_calls node in
  Hashtbl.replace env.node_calls node call;

  (* Defining [FuncDecl]s and updating [env] *)
  let int_s = Arithmetic.Integer.mk_sort ctx in
  let define_func_decl (v : typed_var) =
    let x, ty = v in
    let name = ident_to_str_call x call in
    let out_s = base_ty_to_sort ctx ty in
    let decl = FuncDecl.mk_func_decl_s ctx name [ int_s ] out_s in
    Hashtbl.add env.func_decls name decl;
    decl
  in
  let inputs = List.map define_func_decl node.tn_input in
  let _ = List.map define_func_decl node.tn_local in
  let outputs = List.map define_func_decl node.tn_output in
  (inputs, outputs)

(*******************************************************************)
(* Second step: compiling stream definitions (func_defs) using the *
 * "let def_x : Expr.expr -> Expr.expr = fun n -> ..." technique.  *)
(*******************************************************************)

let rec compile_expr_desc ctx env n_pre n_arr call (e : t_expr_desc) =
  match e with
  | TE_const c -> [ compile_const ctx c ]
  | TE_op (op, es) ->
      let e = List.map (compile_expr ctx env n_pre n_arr call) es in
      compile_op ctx op e
  (* For prim we require exactly one argument. *)
  | TE_prim (_, []) -> raise (Error TooFewArguments)
  | TE_prim (f, [ arg ]) -> (
      (* This one argument cannot be a tuple. *)
      match compile_expr ctx env n_pre n_arr call arg with
      | [] (* Should never happen *) -> assert false
      | [ arg ] -> compile_prim ctx f arg
      | _ -> raise (Error TooManyArguments))
  | TE_prim (_, _) -> raise (Error TooManyArguments)
  | TE_arrow (e1, e2) ->
      let einit = compile_expr ctx env n_pre n_arr call e1 in
      let egen = compile_expr ctx env n_pre (n_arr + 1) call e2 in
      let etest =
        Boolean.mk_eq ctx (n_global ctx)
          (Arithmetic.Integer.mk_numeral_i ctx n_arr)
      in
      compile_if ctx etest einit egen
  | TE_pre e -> compile_expr ctx env (n_pre + 1) n_arr call e
  (* To support nested tuples, we simply flatten them by flattening the list of lists. *)
  (* Why do one even uses nested tuples in Lustre??? *)
  | TE_tuple es ->
      let e = List.map (compile_expr ctx env n_pre n_arr call) es in
      List.flatten e
  | TE_ident x ->
      let arg = arg_n ctx n_pre in
      let xf = Hashtbl.find env.func_decls (ident_to_str_call x call) in
      [ Expr.mk_app ctx xf [ arg ] ]
  (* We instantiate new variables for the node being called. *)
  (* We need the function defining the node to be already defined at this point. *)
  (* Hence the need for topological ordering of nodes. *)
  | TE_app (f, args) ->
      let eargs = List.map (compile_expr ctx env n_pre n_arr call) args in
      let args = extract_simple_args eargs in
      let node = Hashtbl.find env.node_from_ids f in
      let outs = compile_node ctx env node args in
      outs

and compile_expr ctx env n_pre n_arr call (e : t_expr) =
  compile_expr_desc ctx env n_pre n_arr call e.texpr_desc

(************************************************)
(* Third step: compiling a node (aka plumbing). *)
(************************************************)

(** Compile a single many-to-many equation.
    - At this point, [env.func_decls] must already be populated.
    - This function populates the [func_defs] fields with the definitions of each stream defined by the equation. *)
and compile_eq ctx env call (eq : t_equation) =
  let exprs = compile_expr ctx env 0 0 call eq.teq_expr in
  let def_eq (x, expr) =
    let name = ident_to_str_call x call in
    let def_x =
      let xn =
        Expr.mk_app ctx (Hashtbl.find env.func_decls name) [ n_global ctx ]
      in
      Boolean.mk_eq ctx xn expr
    in
    env.func_defs <- def_x :: env.func_defs
  in
  List.iter def_eq (List.combine eq.teq_patt.tpatt_desc exprs)

(** Compile a fresh instance of the given node. Performs the following:
    - declare fresh [FuncDecl]s
    - add definitions to plumb inputs to their argument values 
    - compile each equation of the node
    - return the list of evaluated outputs. *)
and compile_node ctx env (node : t_node) (args : Expr.expr list) =
  let inputs, outputs = define_func_decls_node ctx env node in
  let eval f = Expr.mk_app ctx f [ n_global ctx ] in

  (* Defining constraints for inputs *)
  let plumb_input (input, arg) =
    let def = Boolean.mk_eq ctx input arg in
    env.func_defs <- def :: env.func_defs
  in
  let evaluated_inputs = List.map eval inputs in
  List.iter plumb_input (List.combine evaluated_inputs args);

  let call = Hashtbl.find env.node_calls node in
  List.iter (compile_eq ctx env call) node.tn_equs;

  (* Returning evaluated outputs *)
  let evaluated_outputs = List.map eval outputs in
  evaluated_outputs

(********************************************)
(* Fourth step: putting everything together *)
(********************************************)

let init_node_from_ids nodes =
  let node_from_ids = Hashtbl.create (List.length nodes) in
  Hashtbl.replace_seq node_from_ids
    (List.to_seq (List.map (fun n -> (n.tn_name, n)) nodes));
  node_from_ids

let init_node_calls nodes =
  let node_calls = Hashtbl.create (List.length nodes) in
  Hashtbl.replace_seq node_calls
    (List.to_seq (List.map (fun n -> (n, 0)) nodes));
  node_calls

let compile_file ctx (f : t_file) (main : t_node) =
  (* Create a new env *)
  let func_decls = Hashtbl.create 50 in
  let env =
    {
      func_decls;
      func_defs = [];
      node_from_ids = init_node_from_ids f;
      node_calls = init_node_calls f;
    }
  in
  let outputs = compile_node ctx env main [] in
  (env, outputs)
