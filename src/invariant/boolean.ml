open Z3
open Compile.Env_trans

let gen_inv_true ctx name =
  Boolean.mk_eq ctx (Boolean.mk_const_s ctx name) (Boolean.mk_true ctx)

let gen_inv_false ctx name =
  Boolean.mk_eq ctx (Boolean.mk_const_s ctx name) (Boolean.mk_false ctx)

let gen_inv_eq ctx name_1 name_2 =
  Boolean.mk_eq ctx
    (Boolean.mk_const_s ctx name_1)
    (Boolean.mk_const_s ctx name_2)

let gen_inv_eq_not ctx name_1 name_2 =
  Boolean.mk_eq ctx
    (Boolean.mk_const_s ctx name_1)
    (Boolean.mk_not ctx (Boolean.mk_const_s ctx name_2))

(** [names] is the list of all names of boolean variables:
    - (primed) boolean variables
    - (primed) arrow variables
    - (primed) pre boolean variables *)
let gen_inv_for_names ctx (names : string list) =
  let trues = List.map (gen_inv_true ctx) names in
  let falses = List.map (gen_inv_false ctx) names in
  let lower_triangle l =
    let rec aux = function
      | [] -> []
      | hd :: tl -> List.map (fun e -> (e, hd)) tl @ aux tl
    in
    aux l
  in
  let paired_names = lower_triangle names in
  let eqs = List.map (fun (n1, n2) -> gen_inv_eq ctx n1 n2) paired_names in
  let neqs = List.map (fun (n1, n2) -> gen_inv_eq_not ctx n1 n2) paired_names in
  trues @ falses @ eqs @ neqs

(** Instantiate invariants using the following template:
    ib ::= b = true | b = false | b1 = b2 | b1 = not(b2)
    where b, b1, b2 denote boolean (state) (primed) variables. *)
let gen_inv ctx env =
  let is_bool s = Sort.equal s (Boolean.mk_sort ctx) in
  let boolean_vars =
    List.filter_map
      (fun (v : var_t) -> if is_bool v.sort then Some v.name else None)
      env.vars
  in
  let boolean_pre_vars =
    List.filter_map
      (fun v -> if is_bool v.sort then Some v.name else None)
      env.pre_vars
  in
  let arrow_vars = List.map (fun v -> v.name) env.arrow_vars in
  let names = boolean_vars @ boolean_pre_vars @ arrow_vars in
  let names_prime = List.map name_prime names in
  gen_inv_for_names ctx (names @ names_prime)
