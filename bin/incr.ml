(* From https://www.di.ens.fr/~pouzet/cours/mpri/projet/incr_proof.ml *)

open Aez
open Smt

let declare_symbol name t_in t_out =
  (* création d'un symbole *)
  let x = Hstring.make name in
  (* déclaration de son type *)
  Symbol.declare x t_in t_out;
  x

let tic = declare_symbol "tic" [ Type.type_int ] Type.type_bool
let ok = declare_symbol "ok" [ Type.type_int ] Type.type_bool
let cpt = declare_symbol "cpt" [ Type.type_int ] Type.type_int
let aux = declare_symbol "aux" [ Type.type_int ] Type.type_bool
let zero = Term.make_int (Num.Int 0) (* constante 0 *)
let one = Term.make_int (Num.Int 1) (* constante 1 *)

let def_cpt n =
  (* cpt(n) = ite(n = 0, 0, cpt(n-1)) + ite(tic(n), 1, 0) *)
  let ite1 =
    (* ite(n = 0, 0, cpt(n-1)) *)
    Term.make_ite
      (Formula.make_lit Formula.Eq [ n; zero ])
      zero
      (Term.make_app cpt [ Term.make_arith Term.Minus n one ])
  in
  let ite2 =
    (* ite(tic(n), 1, 0) *)
    Term.make_ite
      (Formula.make_lit Formula.Eq [ Term.make_app tic [ n ]; Term.t_true ])
      one zero
  in
  (* cpt(n) = ite1 + ite2 *)
  Formula.make_lit Formula.Eq
    [ Term.make_app cpt [ n ]; Term.make_arith Term.Plus ite1 ite2 ]

let def_ok n =
  (* ok(n) = ite(n = 0, true, aux(n)) *)
  Formula.make_lit Formula.Eq
    [
      Term.make_app ok [ n ];
      Term.make_ite
        (Formula.make_lit Formula.Eq [ n; zero ])
        Term.t_true (Term.make_app aux [ n ]);
    ]

let def_aux n =
  let aux_n =
    (* aux(n) = true *)
    Formula.make_lit Formula.Eq [ Term.make_app aux [ n ]; Term.t_true ]
  in
  let pre_cpt_le_cpt =
    (* cpt(n-1) <= cpt(n) *)
    Formula.make_lit Formula.Le
      [
        Term.make_app cpt [ Term.make_arith Term.Minus n one ];
        Term.make_app cpt [ n ];
      ]
  in
  Formula.make Formula.And
    [
      Formula.make Formula.Imp [ aux_n; pre_cpt_le_cpt ];
      Formula.make Formula.Imp [ pre_cpt_le_cpt; aux_n ];
    ]

let delta_incr n = Formula.make Formula.And [ def_cpt n; def_ok n; def_aux n ]

let p_incr n =
  Formula.make_lit Formula.Eq [ Term.make_app ok [ n ]; Term.t_true ]

module BMC_solver = Smt.Make (struct end)
module IND_solver = Smt.Make (struct end)

let base =
  BMC_solver.assume ~id:0 (delta_incr zero);
  BMC_solver.assume ~id:0 (delta_incr one);
  BMC_solver.check ();
  BMC_solver.entails ~id:0
    (Formula.make Formula.And [ p_incr zero; p_incr one ])

let ind =
  let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
  let n_plus_one = Term.make_arith Term.Plus n one in
  IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [ zero; n ]);
  IND_solver.assume ~id:0 (delta_incr n);
  IND_solver.assume ~id:0 (delta_incr n_plus_one);
  IND_solver.assume ~id:0 (p_incr n);
  IND_solver.check ();
  IND_solver.entails ~id:0 (p_incr n_plus_one)

let () =
  if not base then Format.printf "FALSE PROPERTY"
  else if ind then Format.printf "TRUE PROPERTY"
  else Format.printf "Don't know"
