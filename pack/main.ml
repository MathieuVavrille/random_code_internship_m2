open Solver
   
let _ = Random.init 0

let main width = 
  let in_file = open_in "examples/ex1round3.txt" in
  let lexbuf_file = Lexing.from_channel in_file in
  let parse () = Parser.main Lexer.token lexbuf_file in
  let cstrset, sbox_vars, cstr_bound = parse () in
  close_in in_file;
  let complete_store, cstr_of_var = init_domain cstrset width in
  let reduced_cstrset, reduced_store = propag_of_unary_cstr complete_store cstrset in
  let res = backtrack reduced_cstrset reduced_store [] 0 None (cstr_of_var, sbox_vars, cstr_bound, ref 0) in
  res
(*
open Cstrbdd
open Useful
open Crypto

let complete16 = complete_bdd 16

let cst_low = concatenate_bdd (complete_bdd 8) (bdd_of_int 171 8 8)

let cst_high = concatenate_bdd (bdd_of_int 171 8 8) (complete_bdd 8)
             
let _ = dot_file (improved_consistency cst_high input_output_sbox 2 random_heuristic_improved_consistency) "output/test.dot"
 *)  
let _ = main 1

let _ = print_endline (string_of_float (!time_active_sb))
          
    (*let _ = print_string (generate_program 3)*)

(*let _ = for i=0 to 255 do
          for j = i+1 to 255 do
            if probaS i j = -6 then print_endline (string_of_int i^" "^(string_of_int j))
          done
        done*)
