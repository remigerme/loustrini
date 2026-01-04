open Compile.Env_kind

(** Main generation of candidate invariants for Houdini. *)
let gen_inv ctx env =
  Boolean.gen_inv ctx env
  @ Numeral.gen_inv ctx env Numeral.Mint
  @ Numeral.gen_inv ctx env Numeral.Mreal

(** Mining oracle for H-Houdini, where [names] was obtained using slice oracle. *)
let mine ctx env v_slice =
  let is_bool_s v = Z3.Sort.equal (bool_s ctx) v.sort in
  let is_int_s v = Z3.Sort.equal (int_s ctx) v.sort in
  let is_real_s v = Z3.Sort.equal (real_s ctx) v.sort in
  let bools = List.filter is_bool_s v_slice in
  let ints = List.filter is_int_s v_slice in
  let reals = List.filter is_real_s v_slice in
  Boolean.gen_inv_for_vars ctx bools
  @ Numeral.gen_inv_for_vars ctx env Mint ints
  @ Numeral.gen_inv_for_vars ctx env Mreal reals
