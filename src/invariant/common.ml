open Z3

let maybe_empty_and ctx (e : Expr.expr list) =
  match e with [] -> Boolean.mk_true ctx | e -> Boolean.mk_and ctx e

(** Helper as [Boolean.mk_implies] do not support lists of expressions. *)
let mk_implies ctx (p : Expr.expr list) (q : Expr.expr list) =
  let p_and = maybe_empty_and ctx p in
  let q_and = maybe_empty_and ctx q in
  Boolean.mk_and ctx [ p_and; Boolean.mk_not ctx q_and ]
