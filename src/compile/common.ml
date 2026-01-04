open Z3
open Ast
open Ast.Asttypes
open Ast.Typed_ast

type error =
  | TooFewArguments
  | TooManyArguments
  | UnknownPrim
  | InvalidOpArguments
  | ExpectedValueGotTuple
  | InvalidTupleArityIf
  | InvalidTupleArityEq

exception Error of error

type toplevel_arg_t = { name : string; sort : Sort.sort }

(*********)
(* Utils *)
(*********)

let rec concat_no_dup l l' =
  match l' with
  | [] -> l
  | hd :: tl ->
      if List.mem hd l then concat_no_dup l tl else concat_no_dup (hd :: l) tl

(** Concatenate [l'] to [l] without adding duplicated elements.
    If [l] contains duplicates, the final results will also contain duplicates. *)
let ( @! ) = concat_no_dup

let add_if_missing x l = if List.mem x l then l else x :: l
let flatten_no_dup l = List.fold_left (fun acc l -> acc @! l) [] l

(** Retrieve string identifier of a node. For streams, use [ident_to_str_call] instead. *)
let ident_to_str (x : Ident.t) = Printf.sprintf "%s__%i" x.name x.id

(** Retrieve string identifier of a stream. *)
let ident_to_str_call (x : Ident.t) (call : int) =
  Printf.sprintf "%s__call__%i" (ident_to_str x) call

(** Flatten a list of expressions assuming each expression is simple (not a tuple).
    Else it cannot be flattened and an error is emitted. *)
let rec extract_simple_args (r : (Expr.expr * string list) list list) =
  match r with
  | [] -> []
  | [ (e, deps) ] :: t -> (e, deps) :: extract_simple_args t
  | _ -> raise (Error ExpectedValueGotTuple)

let base_ty_to_sort ctx ty =
  match ty with
  | Tbool -> Boolean.mk_sort ctx
  | Tint -> Arithmetic.Integer.mk_sort ctx
  | Treal -> Arithmetic.Real.mk_sort ctx

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
    We emit one [Expr.expr * string list] per member of the tuple. *)
let rec compile_if ctx ((eb, db) : Expr.expr * string list)
    (e1s : (Expr.expr * string list) list)
    (e2s : (Expr.expr * string list) list) =
  match (e1s, e2s) with
  | [], [] -> []
  | (e1, d1) :: t1, (e2, d2) :: t2 ->
      (Boolean.mk_ite ctx eb e1 e2, db @! d1 @! d2)
      :: compile_if ctx (eb, db) t1 t2
  | _, _ -> raise (Error InvalidTupleArityIf)

(* [res] contains the compiled arguments given to the operator and their dependencies.
    Each argument is (potentially) a tuple, although in practice, only the `if` operator is polymorphic and supports tuples.
    Note: this comment is not a docstring as it exposes an ocamlformat bug and this is way above my paygrade. *)
let compile_op ctx op (res : (Expr.expr * string list) list list) = (
  match (op, res) with
  | Op_eq, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Boolean.mk_eq ctx e1 e2, d1 @! d2) ]
  | Op_neq, [ [ (e1, d1) ]; [ (e2, d2) ] ] -> [ (Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2), d1 @! d2) ]
  | Op_lt, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Arithmetic.mk_lt ctx e1 e2, d1 @! d2) ]
  | Op_le, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Arithmetic.mk_le ctx e1 e2, d1 @! d2) ]
  | Op_gt, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Arithmetic.mk_gt ctx e1 e2, d1 @! d2) ]
  | Op_ge, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Arithmetic.mk_ge ctx e1 e2, d1 @! d2) ]
  | (Op_add | Op_add_f), r                 -> let args, deps = List.split (extract_simple_args r) in 
                                              [ Arithmetic.mk_add ctx args, flatten_no_dup deps ]
  | (Op_sub | Op_sub_f), [ [ (e, d) ] ]    -> [ (Arithmetic.mk_unary_minus ctx e, d) ]
  | (Op_sub | Op_sub_f), r                 -> let args, deps = List.split (extract_simple_args r) in
                                              [ Arithmetic.mk_sub ctx args, flatten_no_dup deps ]
  | (Op_mul | Op_mul_f), r                 -> let args, deps = List.split (extract_simple_args r) in 
                                              [ Arithmetic.mk_mul ctx args, flatten_no_dup deps ]
  | (Op_div | Op_div_f), [ [ (e1, d1) ]; [ (e2, d2) ] ] -> [ (Arithmetic.mk_div ctx e1 e2, d1 @! d2) ]
  | Op_mod, [ [ (e1, d1) ]; [ (e2, d2) ] ]  -> [ (Arithmetic.Integer.mk_mod ctx e1 e2, d1 @! d2) ]
  | Op_not, [ [ (e, d) ] ]                  -> [ (Boolean.mk_not ctx e, d) ]
  | Op_and, r                               -> let args, deps = List.split (extract_simple_args r) in
                                               [ Boolean.mk_and ctx args, flatten_no_dup deps ]
  | Op_or, r                                -> let args, deps = List.split (extract_simple_args r) in 
                                               [ Boolean.mk_or ctx args, flatten_no_dup deps ]
  | Op_impl, [ [ (e1, d1) ]; [ (e2, d2) ] ] -> [ (Boolean.mk_implies ctx e1 e2, d1 @! d2) ]
  (* Here e1 and e2 can be tuples! We generate an expression for each member of the tuple. *)
  | Op_if, [ [ (eb, db) ]; e1; e2 ]         -> compile_if ctx (eb, db) e1 e2
  | _                                       -> raise (Error InvalidOpArguments)
) [@@ocamlformat "disable"]

(****************)
(* Compile prim *)
(****************)

let compile_prim ctx (f : Ident.t) (arg : Expr.expr) =
  match f.name with
  | "real_of_int" -> Arithmetic.Integer.mk_int2real ctx arg
  | "int_of_real" -> Arithmetic.Real.mk_real2int ctx arg
  | _ -> raise (Error UnknownPrim)

(********************)
(* Creating new env *)
(********************)

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

let init_sort_from_ids ctx f =
  let sort_from_ids = Hashtbl.create 50 in

  let register_sort ctx (v : typed_var) =
    let x, ty = v in
    let sort = base_ty_to_sort ctx ty in
    Hashtbl.replace sort_from_ids x sort
  in

  let register_sort_node node =
    List.iter (register_sort ctx) node.tn_input;
    List.iter (register_sort ctx) node.tn_local;
    List.iter (register_sort ctx) node.tn_output
  in

  List.iter register_sort_node f;
  sort_from_ids

let init_toplevel_args ctx (main : t_node) =
  List.map
    (fun (x, ty) ->
      let name = ident_to_str x in
      let sort = base_ty_to_sort ctx ty in
      { name; sort })
    main.tn_input
