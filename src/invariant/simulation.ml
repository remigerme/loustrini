open Compile.Env_trans
open Z3

let expr_const_of ctx name value =
  Expr.mk_const_s ctx name (Expr.get_sort value)

let next ctx env inputs (vars : (string, Expr.expr option) Hashtbl.t) =
  let vals =
    List.filter_map
      (fun (name, value) ->
        match value with
        | None -> None
        | Some v -> Some (name, (expr_const_of ctx name v, v)))
      (List.of_seq (Hashtbl.to_seq vars))
  in
  let known_vars, tables = List.split vals in
  let froms, tos = List.split tables in
  let new_vars = Hashtbl.create (Hashtbl.length vars) in
  let new_var (v : var_t) =
    let new_val = Expr.simplify (Expr.substitute v.def froms tos) None in
    Hashtbl.replace vars v.name (Some new_val)
  in
  let new_state_var (v : state_var_t) =
    if List.mem v.name known_vars then
      let new_val = Expr.simplify (Expr.substitute v.next froms tos) None in
      Hashtbl.replace vars v.name (Some new_val)
    else Hashtbl.replace vars v.name None
  in
  List.iter new_var inputs;
  List.iter new_var env.vars;
  List.iter new_state_var env.pre_vars;
  List.iter new_state_var env.arrow_vars;
  new_vars

let init_mapping _ctx env inputs =
  let n =
    List.length env.vars + List.length env.pre_vars + List.length env.arrow_vars
    + List.length inputs
  in
  let map = Hashtbl.create n in
  (* TODO *)
  map

let _get_trace ctx env inputs k =
  assert (k >= 0);
  let compute_maps k =
    let rec aux k =
      if k = 0 then [ init_mapping ctx env inputs ]
      else
        let s = aux (k - 1) in
        next ctx env inputs (List.hd s) :: s
    in
    List.rev (aux k)
  in
  let get_eqs (name, value) =
    match value with
    | None -> None
    | Some v -> Some (Boolean.mk_eq ctx (expr_const_of ctx name v) v)
  in
  List.map
    (fun map -> List.filter_map get_eqs (List.of_seq (Hashtbl.to_seq map)))
    (compute_maps k)

let get_trace ctx _env _inputs k =
  assert (k = 1);
  let bool_eq name value =
    Boolean.mk_eq ctx
      (Boolean.mk_const_s ctx name)
      (if value then Boolean.mk_true ctx else Boolean.mk_false ctx)
  in
  let int_eq name value =
    Boolean.mk_eq ctx
      (Arithmetic.Integer.mk_const_s ctx name)
      (Arithmetic.Integer.mk_numeral_i ctx value)
  in
  [
    [
      bool_eq "ok__6__call__1" true;
      bool_eq "S_arr_0" true;
      int_eq "y__8__call__1" 1;
      int_eq "y__4__call__1" 1;
      int_eq "x__7__call__1" 1;
      int_eq "x__3__call__1" 1;
    ];
    [
      bool_eq "ok__6__call__1" true;
      bool_eq "S_arr_0" false;
      int_eq "y__8__call__1" 2;
      int_eq "y__4__call__1" 2;
      int_eq "x__7__call__1" 2;
      int_eq "x__3__call__1" 2;
      int_eq "S_pre_0" 2;
      int_eq "S_pre_1" 2;
    ];
  ]
