open Compile.Env_trans
open Z3

type error = NoValue | BoolUnknown | InvalidSort

exception Error of error

type val_t = Int of int | Bool of bool | Real of float
type valued_var_t = { name : string; value : val_t option }

let sort_of_valued_var ctx v =
  match v.value with
  | None -> raise (Error NoValue)
  | Some v -> (
      match v with
      | Int _ -> Arithmetic.Integer.mk_sort ctx
      | Bool _ -> Boolean.mk_sort ctx
      | Real _ -> Arithmetic.Real.mk_sort ctx)

let expr_of_valued_var ctx v =
  Expr.mk_const_s ctx v.name (sort_of_valued_var ctx v)

let body_of_valued_var ctx v =
  match v.value with
  | None -> None
  | Some value ->
      Some
        (match value with
        | Int i -> Arithmetic.Integer.mk_numeral_i ctx i
        | Bool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
        | Real r -> Arithmetic.Real.mk_numeral_s ctx (string_of_float r))

let extract_int (e : Expr.expr) =
  Big_int_Z.int_of_big_int (Arithmetic.Integer.get_big_int e)

let extract_bool (e : Expr.expr) =
  match Boolean.get_bool_value e with
  | L_FALSE -> false
  | L_TRUE -> true
  | L_UNDEF -> raise (Error BoolUnknown)

let extract_real (e : Expr.expr) = Q.to_float (Arithmetic.Real.get_ratio e)
let valued_init ctx env = get_eqs ctx env @ init ctx env

let next ctx env (vars : valued_var_t list) =
  let vals =
    List.filter_map
      (fun v ->
        match body_of_valued_var ctx v with
        | None -> None
        | Some x -> Some (expr_of_valued_var ctx v, x))
      vars
  in
  let froms, tos = List.split vals in
  let next_var (v : var_t) =
    let new_expr = Expr.simplify (Expr.substitute v.def froms tos) None in
    let new_val =
      match Sort.get_sort_kind v.sort with
      | INT_SORT -> Int (extract_int new_expr)
      | BOOL_SORT -> Bool (extract_bool new_expr)
      | REAL_SORT -> Real (extract_real new_expr)
      | _ -> raise (Error InvalidSort)
    in
    { name = v.name; value = Some new_val }
  in
  []

let get_trace ctx env k =
  assert (k >= 0);
  let rec aux k =
    if k = 0 then []
    else
      let s = aux (k - 1) in
      next ctx env (List.hd s) :: s
  in
  let get_eqs (v : valued_var_t) =
    match body_of_valued_var ctx v with
    | None -> None
    | Some def -> Some (Boolean.mk_eq ctx (expr_of_valued_var ctx v) def)
  in
  List.map (List.filter_map get_eqs) (aux k)
