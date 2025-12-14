open Z3
open Ast.Typed_ast
open Env_trans

type idx_t = { mutable pre : int; mutable arr : int }

let get_idx_pre idx =
  let i = idx.pre in
  idx.pre <- idx.pre + 1;
  i

let get_idx_arr idx =
  let i = idx.arr in
  idx.arr <- idx.arr + 1;
  i

let var_to_expr ctx env call (v : typed_var) =
  let x, _ = v in
  let sort = Hashtbl.find env.sort_from_ids x in
  Expr.mk_const_s ctx (Common.ident_to_str_call x call) sort

let rec compile_expr_desc ctx env init idx call (e : t_expr_desc) =
  match e with
  | TE_const c -> [ Common.compile_const ctx c ]
  | TE_op (op, es) ->
      let e = List.map (compile_expr ctx env init idx call) es in
      Common.compile_op ctx op e
  (* For prim we require exactly one argument. *)
  | TE_prim (_, []) -> raise (Common.Error TooFewArguments)
  | TE_prim (f, [ arg ]) -> (
      (* This one argument cannot be a tuple. *)
      match compile_expr ctx env init idx call arg with
      | [] (* Should never happen *) -> assert false
      | [ arg ] -> Common.compile_prim ctx f arg
      | _ -> raise (Common.Error TooManyArguments))
  | TE_prim (_, _) -> raise (Common.Error TooManyArguments)
  | TE_pre e ->
      let nexts = compile_expr ctx env init idx call e in
      let def_state (e : Expr.expr) =
        let name = "S_pre_" ^ string_of_int (get_idx_pre idx) in
        let sort = Expr.get_sort e in
        let state_var = { name; sort; init = None; next = e } in
        env.state_vars <- state_var :: env.state_vars;
        expr_of_state_var ctx state_var
      in
      List.map def_state nexts
  | TE_arrow (e1, e2) ->
      let einit = compile_expr ctx env init idx call e1 in
      let egen = compile_expr ctx env false idx call e2 in
      let name = "S_arr_" ^ string_of_int (get_idx_arr idx) in
      let init = if init then Boolean.mk_true ctx else Boolean.mk_false ctx in
      let bool_s = Boolean.mk_sort ctx in
      let next =
        Boolean.mk_ite ctx
          (Boolean.mk_const_s ctx name)
          (Boolean.mk_false ctx)
          (Boolean.mk_const_s ctx (name ^ "_unknown"))
      in
      let state_var = { name; sort = bool_s; init = Some init; next } in
      env.state_vars <- state_var :: env.state_vars;
      Common.compile_if ctx (expr_of_state_var ctx state_var) einit egen
  | TE_tuple es ->
      let e = List.map (compile_expr ctx env init idx call) es in
      List.flatten e
  | TE_ident x ->
      let name = Common.ident_to_str_call x call in
      let sort = Hashtbl.find env.sort_from_ids x in
      [ Expr.mk_const_s ctx name sort ]
  | TE_app (f, args) ->
      let eargs = List.map (compile_expr ctx env init idx call) args in
      let args = Common.extract_simple_args eargs in
      let node = Hashtbl.find env.node_from_ids f in
      let outs = compile_node ctx env idx node args in
      outs

and compile_expr ctx env init idx call (e : t_expr) =
  compile_expr_desc ctx env init idx call e.texpr_desc

and compile_eq ctx env idx call (eq : t_equation) =
  let exprs = compile_expr ctx env true idx call eq.teq_expr in
  let def_eq (x, expr) =
    let name = Common.ident_to_str_call x call in
    let sort = Hashtbl.find env.sort_from_ids x in
    let var = { name; sort; def = expr } in
    env.vars <- var :: env.vars
  in
  List.iter def_eq (List.combine eq.teq_patt.tpatt_desc exprs)

and compile_node ctx env idx node args =
  let call = Hashtbl.find env.node_calls node + 1 in
  Hashtbl.replace env.node_calls node call;

  (* Plumbing args in inputs *)
  let register_plumb ((x, ty), arg) =
    let var =
      {
        name = Common.ident_to_str_call x call;
        sort = Common.base_ty_to_sort ctx ty;
        def = arg;
      }
    in
    env.vars <- var :: env.vars
  in
  List.iter register_plumb (List.combine node.tn_input args);

  (* Compiling equations *)
  List.iter (compile_eq ctx env idx call) node.tn_equs;

  (* Returning expressions of outputs *)
  let outputs = List.map (var_to_expr ctx env call) node.tn_output in
  outputs

let init_sort_from_ids ctx f =
  let sort_from_ids = Hashtbl.create 50 in

  let register_sort ctx (v : typed_var) =
    let x, ty = v in
    let sort = Common.base_ty_to_sort ctx ty in
    Hashtbl.replace sort_from_ids x sort
  in

  let register_sort_node node =
    List.iter (register_sort ctx) node.tn_input;
    List.iter (register_sort ctx) node.tn_local;
    List.iter (register_sort ctx) node.tn_output
  in

  List.iter register_sort_node f;
  sort_from_ids

let compile_file ctx (f : t_file) (main : t_node) =
  (* Create a new env and idx *)
  let env =
    {
      vars = [];
      state_vars = [];
      sort_from_ids = init_sort_from_ids ctx f;
      node_from_ids = Common.init_node_from_ids f;
      node_calls = Common.init_node_calls f;
    }
  in
  let idx = { pre = 0; arr = 0 } in

  (* Creating symbols for top level arguments *)
  let args = List.map (var_to_expr ctx env 0) main.tn_input in

  (* Compiling the node, evaluating and conjuncting outputs to form the validity property *)
  let outputs = compile_node ctx env idx main args in
  let prop = Boolean.mk_and ctx outputs in
  (env, prop)
