open Ast.Typed_ast

(** Unimplemented for now, we require that the user defines the equations
    already in topological order for now. *)
let topological_sort (eqs : t_equation list) = eqs
