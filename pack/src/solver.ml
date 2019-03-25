open Crypto
open Useful
open Bdd
open Cstrbdd
   
type cstr = Xor of string * string * string
          | Mc of  string * string * string * string * string * string * string * string
          | Sb of  string * string
          | Psb of  string * string
          | Zero of string
          | Not_zero of string

let cstr_compare c1 c2 = match c1, c2 with
  | Xor(a1,b1,c1), Xor(a2,b2,c2) -> list_compare String.compare [a1;b1;c1] [a2;b2;c2]
  | Mc(a1,b1,c1,d1,e1,f1,g1,h1) , Mc(a2,b2,c2,d2,e2,f2,g2,h2) -> list_compare String.compare [a1;b1;c1;d1;e1;f1;g1;h1] [a2;b2;c2;d2;e2;f2;g2;h2]
  | Sb(a1,b1), Sb(a2,b2) | Psb(a1,b1), Psb(a2,b2) -> list_compare String.compare [a1;b1] [a2;b2]
  | Zero(a1), Zero(a2) | Not_zero(a1), Not_zero(a2) -> String.compare a1 a2
  | Xor _, _ -> 1
  | _, Xor _ -> -1
  | Mc _, _ -> 1
  | _, Mc _ -> -1
  | Sb _, _ -> 1
  | _, Sb _ -> -1
  | Psb _, _ -> 1
  | _, Psb _ -> -1 
  | Zero _, _ -> 1
  | _, Zero _ -> -1

module Cstrset = Set.Make(struct type t = cstr let compare = cstr_compare end)
                                         
let string_of_cstr c = match c with
  | Xor(a,b,c) -> "XOR("^a^","^b^","^c^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^a^","^b^","^c^","^d^","^e^","^f^","^g^","^h^")"
  | Sb(a,b) -> "SB("^a^","^b^")"
  | Psb(a,b) -> "PSB("^a^","^b^")"
  | Zero(a) -> "ZERO("^a^")"
  | Not_zero(a) -> "NOT_ZERO("^a^")"

let rec get_modified vars initial result = match vars, initial, result with
  | [], [], [] -> []
  | x::q, y::r, z::s -> if y == z then get_modified q r s else x::get_modified q r s
  | _ -> failwith "get_modified: the lists don't have the same length"
                 
let propagator_xor a b c store =
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let bddc,wc = Strmap.find c store in
  let res_a = improved_consistency bdda (bdd_xor bddb bddc) wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bddb (bdd_xor bdda bddc) wb random_heuristic_improved_consistency in
  let res_c = improved_consistency bddc (bdd_xor bdda bddb) wc random_heuristic_improved_consistency in                               
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) (Strmap.add c (res_c,wc) store)), get_modified [a;b;c] [bdda;bddb;bddc] [res_a;res_b;res_c]

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
  let res_f = improved_consistency bddf cons_f wf random_heuristic_improved_consistency in
  let res_g = improved_consistency bddg cons_g wg random_heuristic_improved_consistency in
  let res_h = improved_consistency bddh cons_h wh random_heuristic_improved_consistency in
  let cons_a, cons_b, cons_c, cons_d = inverse_mix_column_bdd bdde bddf bddg bddh in (* I use the original bdds instead of the better ones because of the possibility of an empty bdd *)
  let res_a = improved_consistency bdda cons_a wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bddb cons_b wb random_heuristic_improved_consistency in
  let res_c = improved_consistency bddc cons_c wc random_heuristic_improved_consistency in
  let res_d = improved_consistency bddd cons_d wd random_heuristic_improved_consistency in
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) (Strmap.add c (res_c,wc) (Strmap.add d (res_d,wd) (Strmap.add e (res_e,we) (Strmap.add f (res_f,wf) (Strmap.add g (res_g,wg) (Strmap.add h (res_h,wh) store))))))), get_modified [a;b;c;d;e;f;g;h] [bdda;bddb;bddc;bddd;bdde;bddf;bddg;bddh] [res_a;res_b;res_c;res_d;res_e;res_f;res_g;res_h]

let propagator_sb a b store = 
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let res_b = improved_consistency_multiple bddb (possible_outputs bdda input_output_sbox) wb random_heuristic_improved_consistency in
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb input_output_inverse_sbox) wa random_heuristic_improved_consistency in
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) store), get_modified [a;b] [bdda;bddb] [res_a;res_b]

let propagator_psb a b store = 
  let bdda,wa = Strmap.find a store in
  let bddb,wb = Strmap.find b store in
  let res_b = improved_consistency_multiple bddb (possible_outputs bdda input_output_sbox_proba) wb random_heuristic_improved_consistency in
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb input_output_inverse_sbox_proba) wa random_heuristic_improved_consistency in
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) store), get_modified [a;b] [bdda;bddb] [res_a;res_b]

let propagator_zero =
  let zerocst = bdd_of_int 0 8 8 in
  let aux a store =
    let bdda = fst (Strmap.find a store) in
    match bdda == zerocst, subset zerocst bdda with
    | true, _ -> store, []
    | _, false -> Strmap.add a (F,1) store, [a]
    | _, true -> Strmap.add a (zerocst,1) store, [a]
  in aux
   
let propagator_not_zero =
  let not_zero = diff (complete_bdd 8) (bdd_of_int 0 8 8) in
  let aux a store =
    let bdda,wa = Strmap.find a store in
    let res_a = improved_consistency bdda not_zero wa random_heuristic_improved_consistency in
    if res_a == bdda then store, [] else Strmap.add a (res_a,wa) store, [a]
  in aux
  
let propagate cstr store =
  match cstr with
  | Xor(a,b,c) -> propagator_xor a b c store
  | Mc(a,b,c,d,e,f,g,h) -> propagator_mc a b c d e f g h store
  | Sb(a,b) -> propagator_sb a b store
  | Psb(a,b) -> propagator_psb a b store
  | Zero(a) -> propagator_zero a store
  | Not_zero(a) -> propagator_not_zero a store

let vars_of_cstr cstr = match cstr with
  | Xor(a,b,c) -> Strset.add a (Strset.add b (Strset.add c Strset.empty))
  | Mc(a,b,c,d,e,f,g,h) -> Strset.add a (Strset.add b (Strset.add c (Strset.add d (Strset.add e (Strset.add f (Strset.add g (Strset.add h Strset.empty)))))))
  | Sb(a,b) | Psb(a,b) -> Strset.add a (Strset.add b Strset.empty)
  | Zero(a) | Not_zero(a) -> Strset.add a Strset.empty

let rec full_propagation cstrset store cstr_of_var =
  match Cstrset.is_empty cstrset with
  | true -> store
  | false -> let cstr = Cstrset.choose cstrset in
             let new_store, modified_vars = propagate cstr store in
             print_endline "out";
             (*print_endline (string_of_cstr cstr);
             Strmap.iter (fun key (elt,w) -> let previous = fst (Strmap.find key store) in
                                         if elt != previous then print_endline (key^" previous: "^(string_of_int (cardinal previous)^" new: "^(string_of_int (cardinal elt))))) new_store;*)
             if Strmap.cardinal new_store <> Strmap.cardinal store then print_endline (string_of_cstr cstr);
             if List.exists (fun elt -> is_empty (fst (Strmap.find elt new_store))) modified_vars then Strmap.empty else full_propagation (Cstrset.remove cstr (List.fold_left (fun acc elt -> Cstrset.union acc (Strmap.find elt cstr_of_var)) cstrset modified_vars)) new_store cstr_of_var


                           
let add_or_create var store cstr =
  try Cstrset.add cstr (Strmap.find var store)
  with Not_found -> Cstrset.singleton cstr
                 
let init_domain cstrset width =
  let complete = complete_bdd 8 in
  Cstrset.fold (fun cstr (store_acc,cstr_acc) ->
      match cstr with
      | Xor(a,b,c) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) store_acc)), Strmap.add a (add_or_create a cstr_acc cstr) (Strmap.add b (add_or_create b cstr_acc cstr) (Strmap.add c (add_or_create c cstr_acc cstr) cstr_acc)) 
      | Mc(a,b,c,d,e,f,g,h) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) (Strmap.add d (complete,width) (Strmap.add e (complete,width) (Strmap.add f (complete,width) (Strmap.add g (complete,width) (Strmap.add h (complete,width) store_acc))))))), Strmap.add a (add_or_create a cstr_acc cstr) (Strmap.add b (add_or_create b cstr_acc cstr) (Strmap.add c (add_or_create c cstr_acc cstr) (Strmap.add d (add_or_create d cstr_acc cstr) (Strmap.add e (add_or_create e cstr_acc cstr) (Strmap.add f (add_or_create f cstr_acc cstr) (Strmap.add g (add_or_create g cstr_acc cstr) (Strmap.add h (add_or_create h cstr_acc cstr) cstr_acc)))))))
      | Sb(a,b) | Psb(a,b) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) store_acc), Strmap.add a (add_or_create a cstr_acc cstr) (Strmap.add b (add_or_create b cstr_acc cstr) cstr_acc)
      | Zero(a) | Not_zero(a) -> Strmap.add a (complete,width) store_acc, Strmap.add a (add_or_create a cstr_acc cstr) cstr_acc
    ) cstrset (Strmap.empty, Strmap.empty)
  

            
let store_size store =
  Strmap.fold (fun k (v,w) acc -> cardinal v + acc) store 0

let split_store store =
  let (_,chosen_key) = Strmap.fold (fun k (v,w) (card,key) -> if cardinal v > card then (cardinal v,k) else (card,key)) store (0,"") in
  let (chosen_bdd,chosen_width) = Strmap.find chosen_key store in
  let (bdd1,bdd2) = split_backtrack_first chosen_bdd in
  [ Strmap.add chosen_key (bdd1,chosen_width) store; Strmap.add chosen_key (bdd2,chosen_width) store], chosen_key


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
  let csta = Strmap.find a cststore in
  let cstb = Strmap.find b cststore in
  if csta = 0 && cstb = 0 then true, 0 else begin
      let outputs = array_diff_sbox_outputs.(csta) in
      Intset.mem (Strmap.find b cststore) outputs, probaS csta cstb
      
    end
  
let is_solution_cstr cstr cststore =
  match cstr with
  | Xor(a,b,c) -> is_solution_xor a b c cststore, 0
  | Mc(a,b,c,d,e,f,g,h) -> is_solution_mc a b c d e f g h cststore, 0
  | Sb(a,b) -> is_solution_sb a b cststore 
  | Psb(a,b) -> is_solution_sb a b cststore 
  | Zero(a) -> Strmap.find a cststore = 0, 0
  | Not_zero(a) -> Strmap.find a cststore <> 0, 0
    
let is_solution cstrset cststore =
  Cstrset.fold (fun cstr (b_acc, prob_acc) -> if b_acc then let b, prob = is_solution_cstr cstr cststore in b, prob + prob_acc else b_acc, 0) cstrset (true, 0)
  
let rec backtrack cstrset store cstr_of_var acc depth modified_var =
  print_endline ("backtrack"^(string_of_int depth));
  let propagated_store = full_propagation 
                           (match modified_var with
                            | Some a -> (Strmap.find a cstr_of_var)
                            | None -> cstrset)
                           store cstr_of_var in
  print_endline "passed";
  match Strmap.is_empty propagated_store, store_size propagated_store with
  | true, _ -> acc
  | _, n when n = Strmap.cardinal propagated_store -> let cststore = Strmap.fold (fun key (bdd,w) acc -> Strmap.add key (int_of_bdd bdd) acc) propagated_store Strmap.empty in
                                                      let is_sol, prob = is_solution cstrset cststore in
                                                      if is_sol then (print_endline ("one_solution"^(string_of_int (List.length acc + 1))); print_endline ("proba = "^(string_of_int prob));(cststore, prob)::acc) else acc
  | _ -> let split_stores, split_var = split_store propagated_store in
     List.fold_left (fun new_acc backtrack_store -> backtrack cstrset backtrack_store cstr_of_var new_acc (depth+1) (Some split_var)) acc split_stores
     
  















          
