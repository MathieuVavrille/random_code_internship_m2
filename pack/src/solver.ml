open Crypto
open Useful
open Bdd
open Cstrbdd

(* The constraint type: all the active S-boxes are represented in Active SB (the other ones are equal to zero) *)
type cstr = Xor of string * string * string
          | Mc of  string * string * string * string * string * string * string * string
          | Zero of string
          | Not_zero of string
          | ActiveSB of (string * string) list * int ref
          | Iscst of string * int

let cstr_compare c1 c2 = match c1, c2 with
  (* When the constraint have the same type, we compare the arguments *)
  | Xor(a1,b1,c1), Xor(a2,b2,c2) -> list_compare String.compare [a1;b1;c1] [a2;b2;c2]
  | Mc(a1,b1,c1,d1,e1,f1,g1,h1) , Mc(a2,b2,c2,d2,e2,f2,g2,h2) -> list_compare String.compare [a1;b1;c1;d1;e1;f1;g1;h1] [a2;b2;c2;d2;e2;f2;g2;h2]
  | Zero(a1), Zero(a2) | Not_zero(a1), Not_zero(a2) -> String.compare a1 a2
  | ActiveSB(l1,b1), ActiveSB(l2,b2) -> begin match list_compare (fun (a1,b1) (a2,b2) -> match String.compare a1 a2 with
                                                                                         | 0 -> String.compare b1 b2
                                                                                         | n -> n) l1 l2 with
                                        | 0 -> Pervasives.compare !b1 !b2
                                        | n -> n
                                        end
  | Iscst(s1,i1), Iscst(s2,i2) -> begin match Pervasives.compare s1 s2 with
                                  | 0 -> Pervasives.compare i1 i2
                                  | n -> n
                                  end
  (* Here we order when the constraints have different types *)
  | Zero _, _ -> 1
  | _, Zero _ -> -1
  | Iscst _, _ -> 1
  | _, Iscst _ -> -1
  | Not_zero _, _ -> 1
  | _, Not_zero _ -> -1
  | Xor _, _ -> 1
  | _, Xor _ -> -1
  | Mc _, _ -> 1
  | _, Mc _ -> -1

module Cstrset = Set.Make(struct type t = cstr let compare = cstr_compare end)
                                         
let string_of_cstr c = match c with
  (* A conversion function *)
  | Xor(a,b,c) -> "XOR("^a^","^b^","^c^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^a^","^b^","^c^","^d^","^e^","^f^","^g^","^h^")"
  | Zero(a) -> "ZERO("^a^")"
  | Not_zero(a) -> "NOT_ZERO("^a^")"
  | ActiveSB(l, b) -> "ACTIVESB("^(string_of_list (fun (x,y) -> x^","^y) l)^","^(string_of_int !b)^")"
  | Iscst(s,i) -> "Is_cst("^s^","^(string_of_int i)^")"  

let rec get_modified vars initial result = match vars, initial, result with
  (* Returns all the variables that have been modified *)
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
  let cons_a, cons_b, cons_c, cons_d = inverse_mix_column_bdd bdde bddf bddg bddh in (* I use the original bdds instead of the propagated ones because of the possibility of an empty bdd *)
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
  if width res_b > wb then (print_endline (string_of_bddset (possible_outputs bdda input_output_sbox_proba)); print_endline (string_of_bdd bddb);failwith "bug b");
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb input_output_inverse_sbox_proba) wa random_heuristic_improved_consistency in
  if width res_b > wa then failwith "bug a";
  Strmap.add a (res_a,wa) (Strmap.add b (res_b,wb) store), get_modified [a;b] [bdda;bddb] [res_a;res_b]

let propagator_cst i =
  let zerocst = bdd_of_int i 8 8 in
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

let propagator_active_sb l b store =
  let not_fixed, rest_bound =
    List.fold_left
      (fun (not_fixed_acc, rest_bound_acc) (var_in, var_out) -> try let cst_in, cst_out = int_of_bdd (fst (Strmap.find var_in store)), int_of_bdd (fst (Strmap.find var_out store)) in (not_fixed_acc, rest_bound_acc - probaS cst_in cst_out)
                                                                with Failure _ -> ((var_in, var_out)::not_fixed_acc, rest_bound_acc)
      ) ([], b) l in
  let current_bound = List.length not_fixed * -6 in
  let propag = if current_bound = rest_bound then propagator_psb else propagator_sb in
  if current_bound >= rest_bound then
    List.fold_left
      (fun (new_store, modified_vars) (var_in, var_out) ->
        let propag_store, propag_vars = propag var_in var_out new_store in
        propag_store, List.append propag_vars modified_vars
      ) (store, []) not_fixed
  else
    (print_endline "cut";Strmap.add "" (F,1) store, [""])
   
let propagate cstr store =
  match cstr with
  | Xor(a,b,c) -> propagator_xor a b c store
  | Mc(a,b,c,d,e,f,g,h) -> propagator_mc a b c d e f g h store
  | Zero(a) -> propagator_cst 0 a store
  | Not_zero(a) -> propagator_not_zero a store
  | ActiveSB(l,b) -> propagator_active_sb l !b store
  | Iscst(a,i) -> propagator_cst i a store

let vars_of_cstr cstr = match cstr with
  (* return a set of strings that are the variables that appear in the given constraint *)
  | Xor(a,b,c) -> Strset.add a (Strset.add b (Strset.add c Strset.empty))
  | Mc(a,b,c,d,e,f,g,h) -> Strset.add a (Strset.add b (Strset.add c (Strset.add d (Strset.add e (Strset.add f (Strset.add g (Strset.add h Strset.empty)))))))
  | Zero(a) | Not_zero(a) | Iscst(a,_) -> Strset.add a Strset.empty
  | ActiveSB(l, _) -> List.fold_left (fun acc (var_in, var_out) -> Strset.add var_in (Strset.add var_out acc)) Strset.empty l

let rec full_propagation cstrset store cstr_of_var =
  match Cstrset.is_empty cstrset with
  | true -> store
  | false -> let cstr = Cstrset.max_elt cstrset in
             let new_store, modified_vars = propagate cstr store in
             (*print_endline (string_of_cstr cstr);
             Strmap.iter (fun key (elt,w) -> let previous = fst (Strmap.find key store) in
                                         if elt != previous then print_endline (key^" previous: "^(string_of_int (cardinal previous)^" new: "^(string_of_int (cardinal elt))))) new_store;*)
             if List.exists (fun elt -> is_empty (fst (Strmap.find elt new_store))) modified_vars then Strmap.empty else full_propagation (Cstrset.remove cstr (List.fold_left (fun acc elt -> Cstrset.union acc (Strmap.find elt cstr_of_var)) cstrset modified_vars)) new_store cstr_of_var


                           
let add_or_create var store cstr =
  try Cstrset.add cstr (Strmap.find var store)
  with Not_found -> Cstrset.singleton cstr
                 
let init_domain cstrset width =
  (* return a couple of (a couple containing the complete store and the map from vars to constraints) and the variables that are in an S-box *)
  let complete = complete_bdd 8 in
  Cstrset.fold (fun cstr (store_acc,cstr_acc) ->
      match cstr with
      | Xor(a,b,c) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) store_acc)), Strmap.add a (add_or_create a cstr_acc cstr) (Strmap.add b (add_or_create b cstr_acc cstr) (Strmap.add c (add_or_create c cstr_acc cstr) cstr_acc)) 
      | Mc(a,b,c,d,e,f,g,h) -> Strmap.add a (complete,width) (Strmap.add b (complete,width) (Strmap.add c (complete,width) (Strmap.add d (complete,width) (Strmap.add e (complete,width) (Strmap.add f (complete,width) (Strmap.add g (complete,width) (Strmap.add h (complete,width) store_acc))))))), Strmap.add a (add_or_create a cstr_acc cstr) (Strmap.add b (add_or_create b cstr_acc cstr) (Strmap.add c (add_or_create c cstr_acc cstr) (Strmap.add d (add_or_create d cstr_acc cstr) (Strmap.add e (add_or_create e cstr_acc cstr) (Strmap.add f (add_or_create f cstr_acc cstr) (Strmap.add g (add_or_create g cstr_acc cstr) (Strmap.add h (add_or_create h cstr_acc cstr) cstr_acc)))))))
      | Zero(a) | Not_zero(a) | Iscst(a,_) -> Strmap.add a (complete,width) store_acc, Strmap.add a (add_or_create a cstr_acc cstr) cstr_acc
      | ActiveSB(l,_) -> List.fold_left (fun (complete_acc, cstr_to_var_acc) (var_in,var_out) -> Strmap.add var_in (complete, width) (Strmap.add var_out (complete, width) complete_acc), Strmap.add var_in (add_or_create var_in cstr_to_var_acc cstr) (Strmap.add var_out (add_or_create var_out cstr_to_var_acc cstr) cstr_to_var_acc)) (store_acc, cstr_acc) l
    ) cstrset (Strmap.empty, Strmap.empty)
  

            
let store_size store =
  Strmap.fold (fun _ (v,_) acc -> B.mult_big_int (cardinal v) acc) store B.unit_big_int

let split_store store sbox_vars =
  let _,chosen_sbox_var = List.fold_left (fun (card,key) elt -> let bdd_elt, _ = Strmap.find elt store in if cardinal bdd_elt > card then (cardinal bdd_elt,elt) else (card,key)) (B.unit_big_int,"") sbox_vars in
  let (_,chosen_key) = if chosen_sbox_var = "" then Strmap.fold (fun k (v,_) (card,key) -> if cardinal v > card then (cardinal v,k) else (card,key)) store (B.unit_big_int,"") else (B.zero_big_int, chosen_sbox_var) in
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
  print_endline (string_of_int csta^" "^(string_of_int cstb));
  if csta = 0 && cstb = 0 then true, 0 else begin
      let outputs = array_diff_sbox_outputs.(csta) in
      print_endline (string_of_int (Intset.cardinal outputs));
      Intset.mem (Strmap.find b cststore) outputs, let r = probaS csta cstb in print_endline (string_of_int r);r
    end

let is_solution_active_sb l b cststore =
  let is_sol, proba =
    List.fold_left (fun (sol_acc, proba_acc) (var_in, var_out) -> print_endline var_in;let cstr_sol, cstr_proba = is_solution_sb var_in var_out cststore in
                                                                  sol_acc && cstr_sol, proba_acc + cstr_proba) (true, 0) l
  in if proba < b then false,0  else (is_sol, proba)
  
let is_solution_cstr cstr cststore =
  match cstr with
  | Xor(a,b,c) -> is_solution_xor a b c cststore, 0
  | Mc(a,b,c,d,e,f,g,h) -> is_solution_mc a b c d e f g h cststore, 0
  | Zero(a) -> Strmap.find a cststore = 0, 0
  | Not_zero(a) -> Strmap.find a cststore <> 0, 0
  | ActiveSB(l,b) -> is_solution_active_sb l !b cststore
  | Iscst(a,i) -> Strmap.find a cststore = i, 0
    
let is_solution cstrset cststore =
  Cstrset.fold (fun cstr (b_acc, prob_acc) -> if b_acc then (let b, prob = is_solution_cstr cstr cststore in b, prob + prob_acc) else b_acc, 0) cstrset (true, 0)
  
let rec backtrack cstrset store acc depth modified_var (cstr_of_var, sbox_vars, cstr_bound) =
  if depth < 50 then print_endline ("backtrack"^(string_of_int depth));
  print_endline (B.string_of_big_int (store_size store));
  let propagated_store = full_propagation 
                           (match modified_var with
                            | Some a when cardinal (fst (Strmap.find a store)) = B.unit_big_int -> Cstrset.empty
                            | Some a -> Strmap.find a cstr_of_var
                            | None -> cstrset)
                           store cstr_of_var in
  print_endline (B.string_of_big_int (store_size propagated_store));
  let _ = if depth = 50 then failwith "test" in
  (* Strmap.iter (fun k (elt,w) -> if cardinal elt > 1 then (print_endline k;print_endline (string_of_int (cardinal elt)))) propagated_store;*)
  match Strmap.is_empty propagated_store, store_size propagated_store with
  | true, _ -> acc
  | _, n when n = B.unit_big_int -> let cststore = Strmap.fold (fun key (bdd,_) acc -> Strmap.add key (int_of_bdd bdd) acc) propagated_store Strmap.empty in
                                                      let is_sol, prob = is_solution cstrset cststore in
                                                      if is_sol then (print_endline ("one_solution"^(string_of_int (List.length acc + 1))); print_endline ("proba = "^(string_of_int prob));cstr_bound := prob + 1;(cststore, prob)::acc) else acc
  | _ -> let split_stores, split_var = split_store propagated_store sbox_vars in
         List.fold_left (fun new_acc backtrack_store -> backtrack cstrset backtrack_store new_acc (depth+1) (Some split_var) (cstr_of_var, sbox_vars, cstr_bound)) acc split_stores
     
  















          
