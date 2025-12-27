open Compile.Env_kind
open Z3

(** Return the equations of the system for the first [d] steps (we must have [d] > 0). *)
let get_trace ctx env inputs d =
  if d <= 0 then raise (Error "Trace size must be > 0.");
  let eqs_inputs k =
    let defs = List.map (def_of_var ctx) inputs in
    List.map (fun def -> eval_expr_at ctx def k) defs
  in
  let range_k = List.init d (fun x -> x) in
  let vars_k = List.map (Arithmetic.Integer.mk_numeral_i ctx) range_k in
  List.flatten (List.map (fun k -> eqs ctx env k @ eqs_inputs k) vars_k)
