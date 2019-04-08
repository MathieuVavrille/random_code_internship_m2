open Crypto
open Useful
open Bdd
open Cstrbdd

type var = X of int * int * int
         | SX of int * int * int
         | K of int * int * int
         | SK of int * int (* It is always on the third column *)
         | Z of int * int * int

let improved_consistency a b _ _ = intersection a b

let improved_consistency_multiple a b _ _ = inter_of_union a b
              
(* A comparison function between variables, simply to have a total order between them *)
let compare_var v1 v2 = match v1, v2 with
  | X(i1,i2,i3), X(j1,j2,j3)
    | SX(i1,i2,i3), SX(j1,j2,j3)
    | K(i1,i2,i3), K(j1,j2,j3)
    | Z(i1,i2,i3), Z(j1,j2,j3) -> list_compare Pervasives.compare [i1;i2;i3] [j1;j2;j3]
  | SK(i1,i2), SK(j1,j2) -> list_compare Pervasives.compare [i1;i2] [j1;j2]
  | X _, _ -> 1
  | _, X _ -> -1
  | SX _, _ -> 1
  | _, SX _ -> -1
  | K _, _ -> 1
  | _, K _ -> -1
  | SK _, _ -> 1
  | _, SK _ -> -1

module Store = Map.Make(struct type t = var let compare = compare_var end)

             module Varset = Set.Make(struct type t = var let compare = compare_var end)

let string_of_var v = match v with
  | X(a,b,c) -> "x_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | SX(a,b,c) -> "sx_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | K(a,b,c) -> "k_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | SK(a,b) -> "sk_"^(string_of_int a)^"_"^(string_of_int b)^"_3"
  | Z(a,b,c) -> "z_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
             
(* The constraint type: all the active S-boxes are represented in Active SB (the other ones are equal to zero) *)
type cstr = Xor of var * var * var
          | Mc of var * var * var * var * var * var * var * var
          | Not_zero of var
          | ActiveSB of (var * var) list * int ref
          | Iscst of var * int

let cstr_compare c1 c2 = match c1, c2 with
  (* When the constraint have the same type, we compare the arguments *)
  | Xor(a1,b1,c1), Xor(a2,b2,c2) -> list_compare compare_var [a1;b1;c1] [a2;b2;c2]
  | Mc(a1,b1,c1,d1,e1,f1,g1,h1) , Mc(a2,b2,c2,d2,e2,f2,g2,h2) -> list_compare compare_var [a1;b1;c1;d1;e1;f1;g1;h1] [a2;b2;c2;d2;e2;f2;g2;h2]
  | Not_zero(a1), Not_zero(a2) -> compare_var a1 a2
  | ActiveSB(l1,b1), ActiveSB(l2,b2) -> begin match list_compare (fun (a1,b1) (a2,b2) -> match compare_var a1 a2 with
                                                                                         | 0 -> compare_var b1 b2
                                                                                         | n -> n) l1 l2 with
                                        | 0 -> Pervasives.compare !b1 !b2
                                        | n -> n
                                        end
  | Iscst(s1,i1), Iscst(s2,i2) -> begin match Pervasives.compare s1 s2 with
                                  | 0 -> Pervasives.compare i1 i2
                                  | n -> n
                                  end
  (* Here we order when the constraints have different types *)
  | Iscst _, _ -> 1
  | _, Iscst _ -> -1
  | Not_zero _, _ -> 1
  | _, Not_zero _ -> -1
  | Xor _, _ -> 1
  | _, Xor _ -> -1
  | Mc _, _ -> 1
  | _, Mc _ -> -1

module Cstrset = Set.Make(struct type t = cstr let compare = cstr_compare end)
                                     
(* A conversion function *)    
let string_of_cstr c = match c with
  | Xor(a,b,c) -> "XOR("^(string_of_var a)^","^(string_of_var b)^","^(string_of_var c)^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^(string_of_var a)^","^(string_of_var b)^","^(string_of_var c)^","^(string_of_var d)^","^(string_of_var e)^","^(string_of_var f)^","^(string_of_var g)^","^(string_of_var h)^")"
  | Not_zero(a) -> "NOT_ZERO("^(string_of_var a)^")"
  | ActiveSB(l, b) -> "ACTIVESB("^(string_of_list (fun (x,y) -> (string_of_var x)^","^(string_of_var y)) l)^","^(string_of_int !b)^")"
  | Iscst(s,i) -> "Is_cst("^(string_of_var s)^","^(string_of_int i)^")"  
                
(* Returns all the variables that have been modified *)
let get_modified = List.fold_left (fun acc (x,bdd,res) -> if bdd == res then acc else x::acc) []

let time_xor = ref 0.
let propagator_xor a b c store =
  let t = Sys.time() in
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let bddc,wc = Store.find c store in
  let deptha, depthb, depthc = depth bdda, depth bddb, depth bddc in
  let res_a = improved_consistency bdda (bdd_xor (give_depth deptha bddb) (give_depth deptha bddc)) wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bddb (bdd_xor (give_depth depthb bdda) (give_depth depthb bddc)) wb random_heuristic_improved_consistency in
  let res_c = improved_consistency bddc (bdd_xor (give_depth depthc bdda) (give_depth depthc bddb)) wc random_heuristic_improved_consistency in
  time_xor := !time_xor +. Sys.time () -. t;
  Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) store)), get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c]

let time_mc = ref 0.
let time_fun_mc = ref 0.
let propagator_mc a b c d e f g h store =
  let t = Sys.time() in
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let bddc,wc = Store.find c store in
  let bddd,wd = Store.find d store in
  let bdde,we = Store.find e store in
  let bddf,wf = Store.find f store in
  let bddg,wg = Store.find g store in
  let bddh,wh = Store.find h store in
  let t2 = Sys.time() in
  let cons_e, cons_f, cons_g, cons_h = mix_column_bdd (cutted_bdd 8 bdda) (cutted_bdd 8 bddb) (cutted_bdd 8 bddc) (cutted_bdd 8 bddd) in
  time_fun_mc := !time_fun_mc +. Sys.time () -. t2;
  let res_e = improved_consistency bdde cons_e we random_heuristic_improved_consistency in
  let res_f = improved_consistency bddf cons_f wf random_heuristic_improved_consistency in
  let res_g = improved_consistency bddg cons_g wg random_heuristic_improved_consistency in
  let res_h = improved_consistency bddh cons_h wh random_heuristic_improved_consistency in
  if res_e == F || res_f == F || res_g == F || res_h == F then Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]
  else begin
      let t2 = Sys.time() in
      let cons_a, cons_b, cons_c, cons_d = inverse_mix_column_bdd res_e res_f res_g res_h in (* I use the original bdds instead of the propagated ones because of the possibility of an empty bdd *)
      time_fun_mc := !time_fun_mc +. Sys.time () -. t2;
      let res_a = improved_consistency bdda (give_depth (depth bdda) cons_a) wa random_heuristic_improved_consistency in
      let res_b = improved_consistency bddb (give_depth (depth bddb) cons_b) wb random_heuristic_improved_consistency in
      let res_c = improved_consistency bddc (give_depth (depth bddc) cons_c) wc random_heuristic_improved_consistency in
      let res_d = improved_consistency bddd (give_depth (depth bddd) cons_d) wd random_heuristic_improved_consistency in
      time_mc := !time_mc +. Sys.time () -. t;
      Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) (Store.add d (res_d,wd) (Store.add e (res_e,we) (Store.add f (res_f,wf) (Store.add g (res_g,wg) (Store.add h (res_h,wh) store))))))), get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c;d,bddd,res_d;e,bdde,res_e;f,bddf,res_f;g,bddg,res_g;h,bddh,res_h] end

let full_propagator_function inverse a b store =
  let bdda, wa = Store.find a store in
  let bddb, wb = Store.find b store in
  let new_out = improved_consistency bddb (concatenate_bdd (complete_bdd 8) bdda) wb random_heuristic_improved_consistency in
  if new_out != F then begin
      let res_b = if not (subset new_out inverse) then improved_consistency new_out inverse wb random_heuristic_improved_consistency else new_out in
      if res_b != F then begin
          let res_a = improved_consistency_multiple bdda (possible_outputs (complete_bdd 8) res_b) wa random_heuristic_improved_consistency in
          Store.add a (res_a,wa) (Store.add b (res_b,wb) store), get_modified [a,bdda,res_a;b,bddb,res_b]
        end
      else
        Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]
    end
  else
    Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]

let full_propagator_sb = full_propagator_function input_output_inverse_sbox

let full_propagator_psb = full_propagator_function input_output_inverse_sbox_proba
  
let propagator_function f inverse a b store =
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let res_b = improved_consistency_multiple bddb (possible_outputs bdda f) wb random_heuristic_improved_consistency in
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb inverse) wa random_heuristic_improved_consistency in
  Store.add a (res_a,wa) (Store.add b (res_b,wb) store), get_modified [a,bdda,res_a;b,bddb,res_b]
  
(*let propagator_sb = propagator_function input_output_sbox input_output_inverse_sbox *)
                  
(*let propagator_psb = propagator_function input_output_sbox_proba input_output_inverse_sbox_proba*)

                   
(* The constants are defined on one byte, this propagator is called only once in the initialization of the variable *)
let propagator_cst i a store =
  let bdda, wa = Store.find a store in
  let bddcst = bdd_of_int i 8 8 in
  try Store.add a (concatenate_bdd bddcst (Bddset.choose (possible_outputs bddcst bdda)), wa) store, [a]
  with Not_found -> (* the input bdd does not contain the constant *)
    Store.add a (F,wa) store, [a]
       
let propagator_not_zero a store =
  let bdda,wa = Store.find a store in
  let depth_a = depth bdda in
  let not_zero = give_depth depth_a (diff (complete_bdd 8) (bdd_of_int 0 8 8)) in
  let res_a = improved_consistency bdda not_zero wa random_heuristic_improved_consistency in
  if res_a == bdda then store, [] else Store.add a (res_a,wa) store, [a]

let time_active_sb = ref 0.
let propagator_active_sb l b store =
  let t = Sys.time () in
  let not_fixed, rest_bound =
    List.fold_left
      (fun (not_fixed_acc, rest_bound_acc) (var_in, var_out) -> try let cst_in, cst_out = int_of_bdd (cutted_bdd 8 (fst (Store.find var_in store))), int_of_bdd (cutted_bdd 8 (fst (Store.find var_out store))) in (not_fixed_acc, rest_bound_acc - probaS cst_in cst_out)
                                                                                                           with Failure _ -> ((var_in, var_out)::not_fixed_acc, rest_bound_acc)
      ) ([], b) l in
  let current_bound = List.length not_fixed * -6 in
  let propag = if current_bound = rest_bound then full_propagator_psb else full_propagator_sb in
  let res = if current_bound >= rest_bound then
    List.fold_left
      (fun (new_store, modified_vars) (var_in, var_out) -> 
        let propag_store, propag_vars = propag var_in var_out new_store in   
        propag_store, List.append propag_vars modified_vars
      ) (store, []) not_fixed
  else
    Store.add (X(-1,-1,-1)) (F,1) store, [X(-1,-1,-1)] in
  time_active_sb := !time_active_sb +. Sys.time () -. t;
  res

let propagate cstr store =
  match cstr with
  | Xor(a,b,c) -> propagator_xor a b c store
  | Mc(a,b,c,d,e,f,g,h) -> propagator_mc a b c d e f g h store
  | Not_zero(a) -> propagator_not_zero a store
  | ActiveSB(l,b) -> propagator_active_sb l !b store
  | Iscst(a,i) -> propagator_cst i a store

let vars_of_cstr cstr = match cstr with
  (* return a set of strings that are the variables that appear in the given constraint *)
  | Xor(a,b,c) -> Varset.add a (Varset.add b (Varset.add c Varset.empty))
  | Mc(a,b,c,d,e,f,g,h) -> Varset.add a (Varset.add b (Varset.add c (Varset.add d (Varset.add e (Varset.add f (Varset.add g (Varset.add h Varset.empty)))))))
  | Not_zero(a) | Iscst(a,_) -> Varset.add a Varset.empty
  | ActiveSB(l, _) -> List.fold_left (fun acc (var_in, var_out) -> Varset.add var_in (Varset.add var_out acc)) Varset.empty l


                    
let rec full_propagation cstrset store cstr_of_var =
  let res = 
  match Cstrset.is_empty cstrset with
  | true -> store
  | false -> let cstr = Cstrset.max_elt cstrset in
             let new_store, modified_vars = propagate cstr store in
             let dcn = bdd_of_int 209 8 8 in
             if subset (complete_end 8 (bdd_of_int 93 8 8) ) (fst (Store.find (SX(0,3,3)) store)) && subset dcn (fst (Store.find (X(0,3,3)) store)) && not (subset dcn (fst (Store.find (X(0,3,3)) new_store))) then failwith "error here";
             (*Store.iter (fun key (elt,_) -> let previous = if key = X(-1,-1,-1) then F else fst (Store.find key store) in
                                            if elt != previous then print_endline ((string_of_var key)^" previous: "^(B.string_of_big_int (cardinal previous))^" new: "^(B.string_of_big_int (cardinal elt))^" depth: "^(string_of_int (depth elt)))) new_store;*)
             if List.exists (fun elt -> is_empty (fst (Store.find elt new_store))) modified_vars then Store.empty else full_propagation (Cstrset.remove cstr (List.fold_left (fun acc elt -> Cstrset.union acc (Store.find elt cstr_of_var)) cstrset modified_vars)) new_store cstr_of_var in
  res


                           
let add_or_create var store cstr =
  try Cstrset.add cstr (Store.find var store)
  with Not_found -> Cstrset.singleton cstr

                  
(****************************)
(* Initialization functions *)

(* This function adds the bdd to the store only if it is not already present with a bigger depth *)
let add_list_to_store l store =
  List.fold_left (fun store_acc (key, bdd, width) -> try let current_bdd, _ = Store.find key store_acc in
                                                         if depth current_bdd < depth bdd then Store.add key (bdd,width) store_acc
                                                         else store_acc
                                                     with Not_found -> Store.add key (bdd, width) store_acc) store l
                  
let init_domain cstrset width =
  (* return a couple of (a couple containing the complete store and the map from vars to constraints) and the variables that are in an S-box *)
  let complete = complete_bdd 8 in
  Cstrset.fold (fun cstr (store_acc,cstr_acc) ->
      match cstr with
      | Xor(a,b,c) -> add_list_to_store [a,complete,width;b,complete,width;c,complete,width] store_acc,
                      Store.add a (add_or_create a cstr_acc cstr) (Store.add b (add_or_create b cstr_acc cstr) (Store.add c (add_or_create c cstr_acc cstr) cstr_acc)) 
      | Mc(a,b,c,d,e,f,g,h) -> add_list_to_store [a,complete,width;b,complete,width;c,complete,width;d,complete,width;e,complete,width;f,complete,width;g,complete,width;h,complete,width] store_acc,
                               Store.add a (add_or_create a cstr_acc cstr) (Store.add b (add_or_create b cstr_acc cstr) (Store.add c (add_or_create c cstr_acc cstr) (Store.add d (add_or_create d cstr_acc cstr) (Store.add e (add_or_create e cstr_acc cstr) (Store.add f (add_or_create f cstr_acc cstr) (Store.add g (add_or_create g cstr_acc cstr) (Store.add h (add_or_create h cstr_acc cstr) cstr_acc)))))))
      | Not_zero(a) -> add_list_to_store [a,complete,width] store_acc, 
                                    Store.add a (add_or_create a cstr_acc cstr) cstr_acc
      | Iscst(a,_) -> add_list_to_store [a,complete,width] store_acc, cstr_acc
      | ActiveSB(l,_) -> let ws, winverse = Bdd.width input_output_sbox, Bdd.width input_output_inverse_sbox in
                         List.fold_left (fun (complete_acc, cstr_to_var_acc) (var_in,var_out) -> Store.add var_in (complete, ws) (Store.add var_out (input_output_inverse_sbox, winverse) complete_acc), Store.add var_in (add_or_create var_in cstr_to_var_acc cstr) (Store.add var_out (add_or_create var_out cstr_to_var_acc cstr) cstr_to_var_acc)) (store_acc, cstr_acc) l
    ) cstrset (Store.empty, Store.empty)

(* A function that applies the unary constraints, and return a new store and a new constraint set that are not enforces *)
let propag_of_unary_cstr store cstrset =
  Cstrset.fold (fun cstr (cstr_acc, store_acc) -> match cstr with
                                                  | Iscst(a,i) -> (cstr_acc, fst (propagator_cst i a store_acc))
                                                  | Not_zero(a) -> let new_store, modified_vars = propagator_not_zero a store in
                                                                   begin match modified_vars with
                                                                   | [] -> (Cstrset.add cstr cstr_acc, store)
                                                                   | _ -> (cstr_acc, new_store) end
                                                  | _ -> (Cstrset.add cstr cstr_acc, store_acc)
    ) cstrset (Cstrset.empty, store)
  
(*******************)
(* Split functions *)
            
let store_size store =
  Store.fold (fun _ (v,_) acc -> B.mult_big_int (cardinal v) acc) store B.unit_big_int

let split_store store _ =
  let _,chosen_sbox_var = List.fold_left
                            (fun (card,key) elt -> let bdd_elt, _ = Store.find elt store in if cardinal bdd_elt > B.unit_big_int then (cardinal bdd_elt,elt) else (card,key)
                            ) (B.minus_big_int B.unit_big_int,X(-1,-1,-1)) [SX(0,0,1);X(1,0,0);SX(1,0,0)] in
  let (_,chosen_key) = if compare_var chosen_sbox_var (X(-1,-1,-1)) = 0 then Store.fold (fun k (bdd,_) (card,key) -> if cardinal bdd > card then (cardinal bdd,k) else (card,key)) store (B.unit_big_int,X(-1,-1,-1)) else (B.zero_big_int, chosen_sbox_var) in
  let (chosen_bdd,chosen_width) = Store.find chosen_key store in
  let (bdd1,bdd2) = split_backtrack_first chosen_bdd in
  [ Store.add chosen_key (bdd1,chosen_width) store; Store.add chosen_key (bdd2,chosen_width) store], chosen_key


(******************)
(* Solution Check *)
  
let is_solution_xor a b c cststore =
  let ca = Store.find a cststore in
  let cb = Store.find b cststore in
  let cc = Store.find c cststore in
  ca lxor cb = cc

let is_solution_mc a b c d e f g h cststore =
  let ca = Store.find a cststore in
  let cb = Store.find b cststore in
  let cc = Store.find c cststore in
  let cd = Store.find d cststore in
  let ce = Store.find e cststore in
  let cf = Store.find f cststore in
  let cg = Store.find g cststore in
  let ch = Store.find h cststore in
  let re,rf,rg,rh = mix_column_int ca cb cc cd in
  re = ce && rf = cf && rg = cg && rh = ch

let is_solution_sb a b cststore =
  let csta = Store.find a cststore in
  let cstb = Store.find b cststore in
  if csta = 0 && cstb = 0 then true, 0 else begin
      let outputs = array_diff_sbox_outputs.(csta) in
      Intset.mem (Store.find b cststore) outputs, let r = probaS csta cstb in r
    end

let is_solution_active_sb l b cststore =
  let is_sol, proba =
    List.fold_left (fun (sol_acc, proba_acc) (var_in, var_out) -> let cstr_sol, cstr_proba = is_solution_sb var_in var_out cststore in
                                                                  sol_acc && cstr_sol, proba_acc + cstr_proba) (true, 0) l
  in if proba < b then false,0  else (is_sol, proba)
  
let is_solution_cstr cstr cststore =
  match cstr with
  | Xor(a,b,c) -> is_solution_xor a b c cststore, 0
  | Mc(a,b,c,d,e,f,g,h) -> is_solution_mc a b c d e f g h cststore, 0
  | Not_zero(a) -> Store.find a cststore <> 0, 0
  | ActiveSB(l,b) -> is_solution_active_sb l !b cststore
  | Iscst(a,i) -> Store.find a cststore = i, 0
    
let is_solution cstrset cststore =
  Cstrset.fold (fun cstr (b_acc, prob_acc) -> if b_acc then (let b, prob = is_solution_cstr cstr cststore in b, prob + prob_acc) else b_acc, 0) cstrset (true, 0)
  
let rec backtrack cstrset store acc depth modified_var (cstr_of_var, sbox_vars, cstr_bound, one_cst) =
  if depth < 10 then print_endline ("backtrack"^(string_of_int depth));
  let propagated_store = full_propagation 
                           (match modified_var with
                            | None -> cstrset
                            | Some _ when depth mod 2 = 1 -> Cstrset.empty
                            | Some a -> if cardinal (fst (Store.find a store)) = B.unit_big_int then ();Store.find a cstr_of_var)
                           store cstr_of_var in
  (*print_endline (B.string_of_big_int (store_size store));
  print_endline (B.string_of_big_int (store_size propagated_store));
  Store.iter (fun k (elt,_) -> if cardinal elt > B.unit_big_int then (print_endline (string_of_var k);print_endline (B.string_of_big_int (cardinal elt)))) propagated_store;
  let _ = if depth = 0 then failwith "test" in*)
  match Store.is_empty propagated_store, store_size propagated_store with
  | true, _ -> (*incr one_cst; print_endline (string_of_int !one_cst)*)acc
  | _, n when n = B.unit_big_int -> let cststore = Store.fold (fun key (bdd,_) acc -> Store.add key (int_of_bdd (cutted_bdd 8 bdd)) acc) propagated_store Store.empty in
                                    let is_sol, prob = is_solution cstrset cststore in
                                      if is_sol then (print_endline "one_solution"; print_endline ("proba = "^(string_of_int prob));cstr_bound := prob + 1;(cststore, prob)) else acc
  | _ -> let split_stores, split_var = split_store propagated_store sbox_vars in
         List.fold_left (fun new_acc backtrack_store -> backtrack cstrset backtrack_store new_acc (depth+1) (Some split_var) (cstr_of_var, sbox_vars, cstr_bound, one_cst)) acc split_stores
     
  















          
