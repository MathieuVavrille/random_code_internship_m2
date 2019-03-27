open Bdd
open Useful
open Cstrbdd
open Crypto
open Solver

   
let _ = Random.init 0

let main width = 
  let in_file = open_in "examples/ex1round3.txt" in
  let lexbuf_file = Lexing.from_channel in_file in
  let parse () = Parser.main Lexer.token lexbuf_file in
  let cstrset, sbox_vars = parse () in
  close_in in_file;
  let complete_store, cstr_of_var = init_domain cstrset width in
  let res = backtrack cstrset complete_store [] 0 None (cstr_of_var, sbox_vars) in
  res

let _ = main 2
                
(*let _ = print_string (generate_program 4)*)


