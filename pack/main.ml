open Solver
   
let _ = Random.init 0
      
let preprocessing_time = ref 0.
let main width =
  let t = Sys.time () in
  let in_file = open_in "examples/ex3round4.txt" in
  let lexbuf_file = Lexing.from_channel in_file in
  let parse () = Parser.main Lexer.token lexbuf_file in
  let cstrset, sbox_vars, cstr_bound = parse () in
  close_in in_file;
  let complete_store, cstr_of_var = init_domain cstrset width in
  let reduced_cstrset, reduced_store = propag_of_unary_cstr complete_store cstrset in
  preprocessing_time := Sys.time () -. t;
  let best_store, best_prob = backtrack reduced_cstrset reduced_store (Store.empty, 0) 0 None (cstr_of_var, sbox_vars, cstr_bound, ref 0) in
  Store.iter (fun key value -> if value != 0 then print_endline (string_of_var key^" : "^(string_of_int value))) best_store;
  print_endline ("Best Solution with Proba "^(string_of_int best_prob))

let res = main 10000
        
let _ = print_endline ("Time in initialization: "^(string_of_float (!preprocessing_time)))
let _ = print_endline ("Time in propagator_mc: "^(string_of_float (!time_mc)))
let _ = print_endline (" |Time in function MC: "^(string_of_float (!time_fun_mc)))
let _ = print_endline (" | |Time in function MC normal: "^(string_of_float (!time_fun_mc_normal)))
let _ = print_endline (" | |Time in function MC inverse: "^(string_of_float (!time_fun_mc_inverse)))
let _ = print_endline (" |Time in MC consistency: "^(string_of_float (!time_mc_consistency)))
let _ = print_endline ("Time in propagator_xor: "^(string_of_float (!time_xor)))
let _ = print_endline ("Time in propagator_active_sb: "^(string_of_float (!time_active_sb)))
