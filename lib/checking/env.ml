open Z3
open Ast
open Ast.Typed_ast

type z3_env_t = {
  func_decls : (string, FuncDecl.func_decl) Hashtbl.t;
  mutable func_defs : Expr.expr list;
  (* Storing node info *)
  node_from_ids : (Ident.t, t_node) Hashtbl.t;
  node_calls : (t_node, int) Hashtbl.t;
}

let print_env env =
  Printf.printf "=== Z3 Environment ===\n";
  Printf.printf "\nFunction Declarations (%d):\n"
    (Hashtbl.length env.func_decls);
  Hashtbl.iter
    (fun name decl -> Printf.printf "- %s: %s\n" name (FuncDecl.to_string decl))
    env.func_decls;
  Printf.printf "\nFunction Definitions (%d):\n" (List.length env.func_defs);
  List.iter (fun e -> print_endline (Expr.to_string e)) env.func_defs;
  Printf.printf "=======================\n"
