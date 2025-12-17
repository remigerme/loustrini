open Ast.Typed_ast
open Z3
open Env_kind

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

(** Get the [Expr.expr] corresponding to the actual value of [n] (taking [n_pre] into account). *)
let arg_n ctx n_pre =
  (* We could just use the generic expression in the else branch. *)
  (* But it is less readable when debugging. *)
  let n = n_global ctx in
  if n_pre = 0 then n
  else Arithmetic.mk_sub ctx [ n; Arithmetic.Integer.mk_numeral_i ctx n_pre ]

(***************)
(* Compile app *)
(***************)

(** Defines [FuncDecl]s and updates [env]. *)
let define_func_decl ctx env call (v : typed_var) =
  let int_s = Arithmetic.Integer.mk_sort ctx in
  let x, ty = v in
  let name = Common.ident_to_str_call x call in
  let out_s = Common.base_ty_to_sort ctx ty in
  let decl = FuncDecl.mk_func_decl_s ctx name [ int_s ] out_s in
  Hashtbl.add env.func_decls name decl;
  decl

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

  let inputs = List.map (define_func_decl ctx env call) node.tn_input in
  let _ = List.map (define_func_decl ctx env call) node.tn_local in
  let outputs = List.map (define_func_decl ctx env call) node.tn_output in
  (inputs, outputs)

(*****************)
(* Compile expr  *)
(*****************)

(** Returns the list of expressions seen as a tuple. *)
let rec compile_expr_desc ctx env n_pre n_arr call (e : t_expr_desc) =
  match e with
  | TE_const c -> [ Common.compile_const ctx c ]
  | TE_op (op, es) ->
      let e = List.map (compile_expr ctx env n_pre n_arr call) es in
      Common.compile_op ctx op e
  (* For prim we require exactly one argument. *)
  | TE_prim (_, []) -> raise (Error TooFewArguments)
  | TE_prim (f, [ arg ]) -> (
      (* This one argument cannot be a tuple. *)
      match compile_expr ctx env n_pre n_arr call arg with
      | [] (* Should never happen *) -> assert false
      | [ arg ] -> Common.compile_prim ctx f arg
      | _ -> raise (Error TooManyArguments))
  | TE_prim (_, _) -> raise (Error TooManyArguments)
  | TE_arrow (e1, e2) ->
      let einit = compile_expr ctx env n_pre n_arr call e1 in
      let egen = compile_expr ctx env n_pre (n_arr + 1) call e2 in
      let etest =
        Boolean.mk_eq ctx (n_global ctx)
          (Arithmetic.Integer.mk_numeral_i ctx n_arr)
      in
      Common.compile_if ctx etest einit egen
  | TE_pre e -> compile_expr ctx env (n_pre + 1) n_arr call e
  (* To support nested tuples, we simply flatten them by flattening the list of lists. *)
  (* Why do one even uses nested tuples in Lustre??? *)
  | TE_tuple es ->
      let e = List.map (compile_expr ctx env n_pre n_arr call) es in
      List.flatten e
  | TE_ident x ->
      let arg = arg_n ctx n_pre in
      let xf = Hashtbl.find env.func_decls (Common.ident_to_str_call x call) in
      [ Expr.mk_app ctx xf [ arg ] ]
  (* We instantiate new variables for the node being called. *)
  (* We need the function defining the node to be already defined at this point. *)
  (* Hence the need for topological ordering of nodes. *)
  | TE_app (f, args) ->
      let eargs = List.map (compile_expr ctx env n_pre n_arr call) args in
      let args = Common.extract_simple_args eargs in
      let node = Hashtbl.find env.node_from_ids f in
      let outs_decls = compile_node ctx env node args in
      List.map (fun out -> Expr.mk_app ctx out [ arg_n ctx n_pre ]) outs_decls

and compile_expr ctx env n_pre n_arr call (e : t_expr) =
  compile_expr_desc ctx env n_pre n_arr call e.texpr_desc

(***************************************)
(* Compile equations, nodes, and files *)
(***************************************)

(** Compile a single many-to-many equation.
    - At this point, [env.func_decls] must already be populated.
    - This function populates the [func_defs] fields with the definitions of each stream defined by the equation. *)
and compile_eq ctx env call (eq : t_equation) =
  let exprs = compile_expr ctx env 0 0 call eq.teq_expr in
  let def_eq (x, expr) =
    let name = Common.ident_to_str_call x call in
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
    - return the list of unevaluated outputs (evaluation depends on [n_pre]). *)
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

  (* Returning unevaluated outputs because the evaluation depends on n_pre *)
  outputs

(** Compile a whole file. Returns
    - the [env] that was built during the compilation and contains the definitions,
    - the outputs of the main node, which should be checked for truth. *)
let compile_file ctx (f : t_file) (main : t_node) =
  (* Create a new env *)
  let func_decls = Hashtbl.create 50 in
  let env =
    {
      func_decls;
      func_defs = [];
      node_from_ids = Common.init_node_from_ids f;
      node_calls = Common.init_node_calls f;
    }
  in

  (* Creating symbols for top level arguments *)
  let args = List.map (define_func_decl ctx env 0) main.tn_input in
  let evaluated_args =
    List.map (fun f -> Expr.mk_app ctx f [ n_global ctx ]) args
  in

  (* Compiling the node, evaluating and conjuncting outputs to form the validity property *)
  let outputs = compile_node ctx env main evaluated_args in
  let eval out = Expr.mk_app ctx out [ arg_n ctx 0 ] in
  let outputs = List.map eval outputs in
  let prop = Boolean.mk_and ctx outputs in
  (env, prop)
