open Z3

(** Helper as [Boolean.mk_implies] do not support lists of expressions. *)
let mk_implies ctx (p : Expr.expr list) (q : Expr.expr list) =
  let nq = List.map (fun e -> Boolean.mk_not ctx e) q in
  Boolean.mk_and ctx (p @ nq)
