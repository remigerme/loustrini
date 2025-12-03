open Z3

type z3_env_t = {
  func_decls : (string, FuncDecl.func_decl) Hashtbl.t;
  func_defs : (string, Expr.expr -> Expr.expr) Hashtbl.t;
}

let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nFunction Declarations (%d):\n"
    (Hashtbl.length env.func_decls);
  Hashtbl.iter
    (fun name decl -> Printf.printf "- %s: %s\n" name (FuncDecl.to_string decl))
    env.func_decls;
  Printf.printf "\nFunction Definitions (%d):\n" (Hashtbl.length env.func_defs);
  Hashtbl.iter
    (fun name _def -> Printf.printf "- %s: <function>\n" name)
    env.func_defs;
  Printf.printf "=======================\n"
