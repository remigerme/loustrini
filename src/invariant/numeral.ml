open Z3
open Compile.Env_trans

type mode_t = Mint | Mreal

let constants ctx env mode =
  let add_if_not_present_val x l = if not (List.mem x l) then x :: l else l in
  let rec add_if_not_present s l =
    match s with
    | [] -> l
    | hd :: tl -> add_if_not_present tl (add_if_not_present_val hd l)
  in
  let filter_int num = match num with Int i -> Some i | Real _ -> None in
  let filter_real num = match num with Int _ -> None | Real f -> Some f in
  match mode with
  | Mint ->
      let ints = List.filter_map filter_int env.hardcoded_numerals in
      let ints = add_if_not_present [ -1; 0; 1 ] ints in
      List.map (Arithmetic.Integer.mk_numeral_i ctx) ints
  | Mreal ->
      let reals = List.filter_map filter_real env.hardcoded_numerals in
      let reals = add_if_not_present [ -1.0; 0.0; 1.0 ] reals in
      List.map
        (fun f -> Arithmetic.Real.mk_numeral_s ctx (string_of_float f))
        reals

let comparison_operators ctx =
  [
    Boolean.mk_eq ctx;
    (fun e1 e2 -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2));
    Arithmetic.mk_ge ctx;
    Arithmetic.mk_gt ctx;
    Arithmetic.mk_le ctx;
    Arithmetic.mk_lt ctx;
  ]

let gen_inv_comp_cst ctx env mode name =
  let ops = comparison_operators ctx in
  let constants = constants ctx env mode in
  let e = Arithmetic.Integer.mk_const_s ctx name in
  let handle_op op = List.map (op e) constants in
  List.flatten (List.map handle_op ops)

let gen_inv_comp_other ctx mode name_1 name_2 =
  let ops = comparison_operators ctx in
  let make_const name =
    match mode with
    | Mint -> Arithmetic.Integer.mk_const_s ctx name
    | Mreal -> Arithmetic.Real.mk_const_s ctx name
  in
  let e1 = make_const name_1 in
  let e2 = make_const name_2 in
  List.map (fun op -> op e1 e2) ops

(** [names] is the list of all names of integer (resp. real) variables:
    - (primed) integer (resp. real) variables
    - (primed) pre integer (resp. real) variables *)
let gen_inv_for_names ctx env mode (names : string list) =
  let consts = List.flatten (List.map (gen_inv_comp_cst ctx env mode) names) in
  let cartesian l =
    List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l) l)
  in
  let paired_names = cartesian names in
  let pairs =
    List.flatten
      (List.map
         (fun (n1, n2) -> gen_inv_comp_other ctx mode n1 n2)
         paired_names)
  in
  consts @ pairs

(** Instantiate invariants using the following template:
    ii ::= i op c | i1 op i2
    where i, i1, i2 denote integer (resp. real) (state) (primed) variables,
    and op ::= >= | > | <= | < | = | !=
    and c ::= -1 | 0 | 1 | {any hardcoded constant in the program}. *)
let gen_inv ctx env mode =
  let is_int s = Sort.equal s (Arithmetic.Integer.mk_sort ctx) in
  let is_real s = Sort.equal s (Arithmetic.Real.mk_sort ctx) in
  let filter = match mode with Mint -> is_int | Mreal -> is_real in
  let vars =
    List.filter_map
      (fun (v : var_t) -> if filter v.sort then Some v.name else None)
      env.vars
  in
  let pre_vars =
    List.filter_map
      (fun v -> if filter v.sort then Some v.name else None)
      env.pre_vars
  in
  let names = vars @ pre_vars in
  let names_prime = List.map name_prime names in
  gen_inv_for_names ctx env mode (names @ names_prime)
