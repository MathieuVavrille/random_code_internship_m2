open Bdd
open Useful
open Cstrbdd
open Crypto
   
let _ = Random.init 0
      
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
