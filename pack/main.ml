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
  let best_store, best_prob = backtrack reduced_cstrset reduced_store (Store.empty, 0) 0 None (cstr_of_var, sbox_vars, cstr_bound, ref 0) in
  Store.iter (fun key value -> if value != 0 then print_endline (string_of_var key^" : "^(string_of_int value))) best_store;
  print_endline ("Best Solution with Proba "^(string_of_int best_prob))

let res = main 10000
        
let _ = print_endline ("Time in propagator_mc: "^(string_of_float (!time_mc)))
let _ = print_endline ("->Time in function MC: "^(string_of_float (!time_fun_mc)))
let _ = print_endline ("Time in propagator_xor: "^(string_of_float (!time_xor)))
let _ = print_endline ("Time in propagator_active_sb: "^(string_of_float (!time_active_sb)))
(*
open Cstrbdd
open Useful
open Crypto

let complete16 = complete_bdd 16

let cst_low = concatenate_bdd (complete_bdd 8) (bdd_of_int 171 8 8)

let cst_high = concatenate_bdd (bdd_of_int 171 8 8) (complete_bdd 8)
             
let _ = dot_file (improved_consistency cst_high input_output_sbox 2 random_heuristic_improved_consistency) "output/test.dot"
 *)
          
    (*let _ = print_string (generate_program 3)*)

(*let _ = for i=0 to 255 do
          for j = i+1 to 255 do
            if probaS i j = -6 then print_endline (string_of_int i^" "^(string_of_int j))
          done
        done*)
