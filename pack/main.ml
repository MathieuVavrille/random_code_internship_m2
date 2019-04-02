open Solver
  
let _ = Random.init 0

let main width = 
  let in_file = open_in "examples/ex1round3.txt" in
  let lexbuf_file = Lexing.from_channel in_file in
  let parse () = Parser.main Lexer.token lexbuf_file in
  let cstrset, sbox_vars, cstr_bound = parse () in
  close_in in_file;
  let complete_store, cstr_of_var = init_domain cstrset width in
  let res = backtrack cstrset complete_store [] 0 None (cstr_of_var, sbox_vars, cstr_bound) in
  res

let _ = main 1
                
    (*let _ = print_string (generate_program 3)*)

(*let _ = for i=0 to 255 do
          for j = i+1 to 255 do
            if probaS i j = -6 then print_endline (string_of_int i^" "^(string_of_int j))
          done
        done*)
