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

(*********)
(* Utils *)
(*********)

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
