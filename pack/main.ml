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
  let cstrset = parse () in
  close_in in_file;
  let complete_store, cstr_of_var = init_domain cstrset width in
  let res = backtrack cstrset complete_store cstr_of_var [] 0 None in
  res

(*let _ = main 3*)

let _ = save_to_file (complete_bdd 8) "output/complete_save.txt"
  
let res = get_from_file "output/complete_save.txt"

let _ = print_endline (string_of_int (width res)); print_endline (string_of_int (cardinal res))
    
(*let _ = let count = ref 0 in
        for i=0 to 255 do
          for j=0 to 255 do
            match probaS i j with
            | -6 -> print_endline (string_of_int i^" "^(string_of_int j)); incr count; print_endline (string_of_int !count);
            | _ -> ()
          done
        done*)
                
             (*             let _ = print_string (generate_program 3)*)

(* let _ =
  for i=252 to 255 do
    print_endline ("i == "^(string_of_int i));
    for j=0 to 4 do
      print_endline ("j = "^(string_of_int j));
      for k=0 to 4 do
        print_endline (string_of_int k);
        for l=100 to 104 do
          print_endline (string_of_int l);
          for m=54 to 58 do
            for n=0 to 4 do
              for o=252 to 255 do
                for p=136 to 139 do
                  let bi,bj,bk,bl,bm,bn,bo,bp = bdd_of_int i 8 8,bdd_of_int j 8 8,bdd_of_int k 8 8,bdd_of_int l 8 8,bdd_of_int m 8 8,bdd_of_int n 8 8,bdd_of_int o 8 8,bdd_of_int p 8 8 in
                  let r1,r2,r3,r4 = mix_column bi bj bk bl in
                  let s1,s2,s3,s4 = mix_column bm bn bo bp in
                  let t1,t2,t3,t4 = mix_column (bdd_xor bi bm) (bdd_xor bj bn) (bdd_xor bk bo) (bdd_xor bl bp) in
                  if (t1 != bdd_xor r1 s1) || (t2 != bdd_xor r2 s2) || (t3 != bdd_xor r3 s3) || (t4 != bdd_xor r4 s4) then failwith "test"
                done
              done
            done
          done
        done
      done
    done
  done*)
   
    
    
(*let _ = let rec aux n bdd1 bdd2 = match n with
          | 0 -> ()
          | _ -> 
             print_string ((string_of_int n)^" ");
             let limited = limit bdd1 n bdd_first_come_heuristic in
             print_string ((string_of_int (cardinal limited - 32383))^" ");
             let limited_mv = limit bdd2 n bdd_merge_value_first_bdd_heuristic in
             print_endline (string_of_int (cardinal limited_mv - 32383));
             aux (n-1) limited limited_mv
        in
        aux 3969 t t*)
          
(*let _ = for j=5 to 15 do
          print_endline ("Size "^(string_of_int j));
          let random_bdd = limit (bdd_of_bitvectset (random_set j)) 6 bdd_merge_value_heuristic in
          for i=1 to depth random_bdd do
            let a,b = split_backtrack_at_depth random_bdd i in
            print_string (string_of_int (Array.fold_left (fun acc elt -> acc + elt) (Array.fold_left (fun acc elt -> acc + elt) 0 (array_width a)) (array_width b))^" ");
          done;
          print_newline ();
          let a,b = split_backtrack_optimal_width random_bdd in
          let c,d = split_backtrack_optimal_next_width random_bdd in
          print_endline (string_of_int (Array.fold_left (fun acc elt -> acc + elt) (Array.fold_left (fun acc elt -> acc + elt) 0 (array_width a)) (array_width b)));
          print_endline (string_of_int (Array.fold_left (fun acc elt -> acc + elt) (Array.fold_left (fun acc elt -> acc + elt) 0 (array_width c)) (array_width d)));
        done *)
