open Ast.Typed_ast
open Z3
open Env_kind

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

let decl_of_typed_var_and_deps ctx env call ((x, ty) : typed_var) =
  let name = Common.ident_to_str_call x call in
  let sort = Common.base_ty_to_sort ctx ty in
  (decl_of_name ctx name sort, Hashtbl.find env.depends_on name)

let decl_of_typed_var ctx call ((x, ty) : typed_var) =
  let name = Common.ident_to_str_call x call in
  let sort = Common.base_ty_to_sort ctx ty in
  decl_of_name ctx name sort

let add_if_missing x l = if not (List.mem x l) then x :: l else l

(*****************)
(* Compile expr  *)
(*****************)

(** Returns a list representing a Lustre tuple.
    Each element of the list is a pair (expr, deps). *)
let rec compile_expr_desc ctx env n_pre n_arr call (e : t_expr_desc) =
  match e with
  | TE_const c ->
      env.hardcoded_numerals <-
        (match c with
        | Cint i -> add_if_missing (Int i) env.hardcoded_numerals
        | Creal f -> add_if_missing (Real f) env.hardcoded_numerals
        | Cbool _ -> env.hardcoded_numerals);
      [ (Common.compile_const ctx c, []) ]
  | TE_op (op, es) ->
      let res = List.map (compile_expr ctx env n_pre n_arr call) es in
      Common.compile_op ctx op res
  (* For prim we require exactly one argument. *)
  | TE_prim (_, []) -> raise (Common.Error TooFewArguments)
  | TE_prim (f, [ arg ]) -> (
      (* This one argument cannot be a tuple. *)
      let res = compile_expr ctx env n_pre n_arr call arg in
      match List.split res with
      | [], [] (* Should never happen *) -> assert false
      | [ arg ], [ deps ] -> [ (Common.compile_prim ctx f arg, deps) ]
      | _ -> raise (Common.Error TooManyArguments))
  | TE_prim (_, _) -> raise (Common.Error TooManyArguments)
  | TE_arrow (e1, e2) ->
      let res_init = compile_expr ctx env n_pre n_arr call e1 in
      let res_gen = compile_expr ctx env n_pre (n_arr + 1) call e2 in
      let e_n_arr = Arithmetic.Integer.mk_numeral_i ctx n_arr in
      let etest = Boolean.mk_eq ctx (n_global ctx) e_n_arr in
      Common.compile_if ctx (etest, []) res_init res_gen
  (* We are interested in the 1-step COI so we forget about dependencies if it's more than the first pre. *)
  | TE_pre e ->
      let res = compile_expr ctx env (n_pre + 1) n_arr call e in
      if n_pre = 0 then res else List.map (fun (e, _) -> (e, [])) res
  (* To support nested tuples, we simply flatten them by flattening the list of lists. *)
  (* Why do one even uses nested tuples in Lustre??? *)
  | TE_tuple es ->
      let res = List.map (compile_expr ctx env n_pre n_arr call) es in
      List.flatten res
  | TE_ident x ->
      let name = Common.ident_to_str_call x call in
      let sort = Hashtbl.find env.sort_from_ids x in
      let xf = decl_of_name ctx name sort in
      let arg = arg_n ctx n_pre in
      let deps_of_name = Hashtbl.find env.depends_on name in
      (* We include the dependencies of this identifier if it is not under a pre. *)
      (* In that case, it is just a wire. This works because of TOPOLOGICAL ORDERING. *)
      let deps =
        if n_pre = 0 then add_if_missing name deps_of_name else [ name ]
      in
      [ (FuncDecl.apply xf [ arg ], deps) ]
  (* We compile recursively node calls (no memoization). *)
  (* If there are mutual recursive calls between nodes, bad things will happen. *)
  (* Or rather, nothing will ever happen. *)
  | TE_app (f, args) ->
      let res_args = List.map (compile_expr ctx env n_pre n_arr call) args in
      (* Each argument should be a value and not a tuple *)
      let res_args = Common.extract_simple_args res_args in
      let node = Hashtbl.find env.node_from_ids f in
      let res_outs = compile_node ctx env node res_args in
      let eval (out, deps) = (FuncDecl.apply out [ arg_n ctx n_pre ], deps) in
      List.map eval res_outs

and compile_expr ctx env n_pre n_arr call (e : t_expr) :
    (Expr.expr * string list) list =
  compile_expr_desc ctx env n_pre n_arr call e.texpr_desc

(***************************************)
(* Compile equations, nodes, and files *)
(***************************************)

(** Compile a single many-to-many equation.
    This function populates the [env.vars] field with the definitions of each stream defined by the equation.
    This also populates the [env.depends_on] field for this instance of the variable. *)
and compile_eq ctx env call (eq : t_equation) =
  let res = compile_expr ctx env 0 0 call eq.teq_expr in
  let def_var (x, (expr, deps)) =
    let name = Common.ident_to_str_call x call in
    let sort = Hashtbl.find env.sort_from_ids x in
    let v = { name; sort; def = expr } in
    env.vars <- v :: env.vars;
    Hashtbl.replace env.depends_on name deps
  in
  List.iter def_var (List.combine eq.teq_patt.tpatt_desc res)

(** Compile a fresh instance of the given node. Performs the following:
    - declare fresh [FuncDecl]s
    - add definitions to plumb inputs to their argument values
    - compile each equation of the node
    - return the list of unevaluated outputs (evaluation depends on [n_pre]). *)
and compile_node ctx env node (args : (Expr.expr * string list) list) =
  (* Updating call counter *)
  let call = Hashtbl.find env.node_calls node + 1 in
  Hashtbl.replace env.node_calls node call;

  (* Defining constraints for inputs *)
  let plumb_input ((x, ty), (arg, deps)) =
    let name = Common.ident_to_str_call x call in
    let var = { name; sort = Common.base_ty_to_sort ctx ty; def = arg } in
    env.vars <- var :: env.vars;
    Hashtbl.replace env.depends_on name deps
  in
  List.iter plumb_input (List.combine node.tn_input args);

  (* Compiling equations in topological order *)
  let eqs = Topological.topological_sort node.tn_equs in
  List.iter (compile_eq ctx env call) eqs;

  (* Returning unevaluated outputs because the evaluation depends on n_pre,
     and dependencies of those outputs. *)
  List.map (decl_of_typed_var_and_deps ctx env call) node.tn_output

(** Compile a whole file. Returns
    - the [env] that was built during the compilation and contains the definitions,
    - the outputs of the main node, which should be checked for truth. *)
let compile_file ctx (f : t_file) (main : t_node) =
  (* Create a new env *)
  let env =
    {
      vars = [];
      toplevel_args = Common.init_toplevel_args ctx main;
      hardcoded_numerals = [];
      depends_on = Hashtbl.create 50;
      sort_from_ids = Common.init_sort_from_ids ctx f;
      node_from_ids = Common.init_node_from_ids f;
      node_calls = Common.init_node_calls f;
    }
  in

  (* Creating symbols for top level arguments *)
  let args = List.map (decl_of_typed_var ctx 0) main.tn_input in
  let eval_decl f = FuncDecl.apply f [ n_global ctx ] in
  let evaluated_args = List.map eval_decl args in
  let empty_deps = List.init (List.length args) (fun _ -> []) in
  let res_args = List.combine evaluated_args empty_deps in

  (* Compiling the node, evaluating and conjuncting outputs to form the validity property *)
  let res_outs = compile_node ctx env main res_args in
  let outputs, deps = List.split res_outs in
  let outputs = List.map eval_decl outputs in
  let prop = Boolean.mk_and ctx outputs in
  (env, prop, List.flatten deps)
