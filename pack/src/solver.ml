open Crypto
open Useful
open Bdd
open Cstrbdd
   
type cstr = Xor of string * string * string
          | Mc of  string * string * string * string * string * string * string * string
          | Sb of  string * string
          | Zero of string
          | Not_zero of string

let string_of_cstr c = match c with
  | Xor(a,b,c) -> "XOR("^a^","^b^","^c^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^a^","^b^","^c^","^d^","^e^","^f^","^g^","^h^")"
  | Sb(a,b) -> "SB("^a^","^b^")"
  | Zero(a) -> "ZERO("^a^")"
  | Not_zero(a) -> "NOT_ZERO("^a^")"

let propagator_xor a b c store =
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let bddc,wc = Strmap.find c store in
  let res_a = improved_consistency bdda (bdd_xor bddb bddc) wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bddb (bdd_xor bdda bddc) wb random_heuristic_improved_consistency in
  let res_c = improved_consistency bddc (bdd_xor bdda bddb) wc random_heuristic_improved_consistency in                               
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) (Strmap.add c (res_c,wc) store))

let propagator_mc a b c d e f g h store =
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let bddc,wc = Strmap.find c store in
  let bddd,wd = Strmap.find d store in
  let bdde,we = Strmap.find e store in
  let bddf,wf = Strmap.find f store in
  let bddg,wg = Strmap.find g store in
  let bddh,wh = Strmap.find h store in
  let cons_e, cons_f, cons_g, cons_h = mix_column_bdd bdda bddb bddc bddd in
  let res_e = improved_consistency bdde cons_e we random_heuristic_improved_consistency in
  let res_f = improved_consistency bdde cons_f wf random_heuristic_improved_consistency in
  let res_g = improved_consistency bdde cons_g wg random_heuristic_improved_consistency in
  let res_h = improved_consistency bdde cons_h wh random_heuristic_improved_consistency in
  let cons_a, cons_b, cons_c, cons_d = inverse_mix_column_bdd res_e res_f res_g res_h in
  let res_a = improved_consistency bdde cons_a wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bdde cons_b wb random_heuristic_improved_consistency in
  let res_c = improved_consistency bdde cons_c wc random_heuristic_improved_consistency in
  let res_d = improved_consistency bdde cons_d wd random_heuristic_improved_consistency in
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) (Strmap.add c (res_c,wc) (Strmap.add d (res_d,wd) (Strmap.add e (res_e,we) (Strmap.add f (res_f,wf) (Strmap.add g (res_g,wg) (Strmap.add h (res_h,wh) store)))))))

let propagator_sb a b store = 
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let res_b = improved_consistency_multiple bddb (possible_outputs bdda input_output_sbox) wb random_heuristic_improved_consistency in
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb input_output_inverse_sbox) wa random_heuristic_improved_consistency in
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) store)

let propagator_zero =
  let zerocst = bdd_of_int 0 8 8 in
  let aux a store =
    if subset zerocst (fst (Strmap.find a store)) then Strmap.add a (zerocst,1) store else Strmap.add a (F, 1) store
  in aux
   
let propagator_not_zero =
  let not_zero = diff (complete_bdd 8) (bdd_of_int 0 8 8) in
  let aux a store =
    let bdda,wa = Strmap.find a store in
    Strmap.add a (improved_consistency bdda not_zero wa random_heuristic_improved_consistency,wa) store
  in aux
  
let propagate cstr store =
  match cstr with
  | Xor(a,b,c) -> propagator_xor a b c store
  | Mc(a,b,c,d,e,f,g,h) -> propagator_mc a b c d e f g h store
  | Sb(a,b) -> propagator_sb a b store
  | Zero(a) -> propagator_zero a store
  | Not_zero(a) -> propagator_not_zero a store
             
let init_domain cstrlist width =
  let complete = complete_bdd 8 in
  List.fold_left (fun acc cstr ->
      match cstr with
      | Xor(a,b,c) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) acc)) 
      | Mc(a,b,c,d,e,f,g,h) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) (Strmap.add d (complete,width) (Strmap.add e (complete,width) (Strmap.add f (complete,width) (Strmap.add g (complete,width) (Strmap.add h (complete,width) acc)))))))
      | Sb(a,b) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) acc)
      | Zero(a) | Not_zero(a) -> Strmap.add a (complete,width) acc
    ) Strmap.empty cstrlist

let store_size store =
  Strmap.fold (fun k (v,w) acc -> cardinal v + acc) store 0

let split_store store =
  let (_,chosen_key) = Strmap.fold (fun k (v,w) (card,key) -> if cardinal v > card then (cardinal v,k) else (card,key)) store (0,"") in
  let (chosen_bdd,chosen_width) = Strmap.find chosen_key store in
  let (bdd1,bdd2) = split_backtrack_first chosen_bdd in
  [ Strmap.add chosen_key (bdd1,chosen_width) store; Strmap.add chosen_key (bdd2,chosen_width) store]


let is_solution_xor a b c cststore =
  let ca = Strmap.find a cststore in
  let cb = Strmap.find b cststore in
  let cc = Strmap.find c cststore in
  ca lxor cb = cc

let is_solution_mc a b c d e f g h cststore =
  let ca = Strmap.find a cststore in
  let cb = Strmap.find b cststore in
  let cc = Strmap.find c cststore in
  let cd = Strmap.find d cststore in
  let ce = Strmap.find e cststore in
  let cf = Strmap.find f cststore in
  let cg = Strmap.find g cststore in
  let ch = Strmap.find h cststore in
  let re,rf,rg,rh = mix_column_int ca cb cc cd in
  re = ce && rf = cf && rg = cg && rh = ch

let is_solution_sb a b cststore =
  Intset.mem (Strmap.find b cststore) array_diff_sbox_outputs.(Strmap.find a cststore)
  
let is_solution_cstr cstr cststore =
  match cstr with
  | Xor(a,b,c) -> is_solution_xor a b c cststore
  | Mc(a,b,c,d,e,f,g,h) -> is_solution_mc a b c d e f g h cststore
  | Sb(a,b) -> is_solution_sb a b cststore
  | Zero(a) -> Strmap.find a cststore = 0
  | Not_zero(a) -> Strmap.find a cststore <> 0


    
let is_solution cstrlist cststore =
  List.for_all (fun cstr -> is_solution_cstr cstr cststore) cstrlist
  

  
let rec backtrack cstrlist store acc =
  print_endline "backtrack";
  let propagated_store = List.fold_left (fun acc cstr -> propagate cstr acc) store cstrlist in
  match store_size propagated_store with
  | n when n = Strmap.cardinal propagated_store -> print_endline "one solution";print_endline (string_of_int (List.length acc + 1));
                                                   let cststore = Strmap.fold (fun key (bdd,w) acc -> Strmap.add key (int_of_bdd bdd) acc) propagated_store Strmap.empty in
                                                   if is_solution cstrlist cststore then cststore::acc else acc
  | 0 -> acc
  | _ -> List.fold_left (fun new_acc backtrack_store -> backtrack cstrlist backtrack_store new_acc) acc (split_store propagated_store)
     
  















          
