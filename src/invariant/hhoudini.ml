exception EmptyAbduct
exception Break

(** https://stackoverflow.com/questions/22132458/library-function-to-find-difference-between-two-lists-ocaml *)
let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

(** TODO *)
let abduct _ctx _env _p_target _p_v = None

let rec h_houdini ctx env p_target p_fail positive =
  (* TODO: implement memoization *)
  let valid_solution = ref false in
  let h = ref [ p_target ] in
  let v_slice = Slice.slice ctx env p_target in
  let p_v = Generation.mine ctx env v_slice in
  while not !valid_solution do
    h := [ p_target ];
    let p_v = diff p_v !p_fail in
    let a = abduct ctx env p_target p_v in
    if Option.is_none a then raise EmptyAbduct;
    let a = Option.get a in
    valid_solution := true;
    let handle_p p =
      try
        let h_sol = h_houdini ctx env p p_fail positive in
        h := h_sol @ !h
      with EmptyAbduct ->
        valid_solution := false;
        p_fail := p :: !p_fail;
        raise Break
    in
    try List.iter handle_p a with Break -> ()
  done;
  !h

let learn ctx env _inputs prop =
  let positive =
    []
    (*TODO*)
  in
  try Some (h_houdini ctx env prop (ref []) positive) with EmptyAbduct -> None
