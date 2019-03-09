open Bdd

(* Some useful string conversions *)
let string_of_array f a =
  "["^(Array.fold_left (fun acc x -> acc^(f x)^";") "" a)^"]" 

let print_bool b = match b with
  | true -> print_string "true"
  | false -> print_string "false"

let multiple_mdd_consistency m bdds = (* I am almost sure that there is a bug *)
  (* ensures MDD consistency on m wrt m' and returns m *)
  let zero = Hashtbl.create 101 in (* all the nodes whose 0-edge is consistent *)
  let one = Hashtbl.create 101 in (* all the nodes whose 1-edge is consistent *)
  let inter = Hashtbl.create 101 in (* just a set, but faster by using hashtbl *)
  let rec aux m m' =
    try Hashtbl.find inter (ref m,ref m')
    with Not_found -> 
          match m, m' with
          | F, _ | _, F -> F
          | T, _ -> m'
          | N(a,b), T -> failwith "mdd_consistency: the bdds do not have the same size"
          | N(a,b), N(c,d) ->
             let e,f = aux a c, aux b d in
             let new_bdd = bdd_of e f in
             Hashtbl.add inter (ref m,ref m') new_bdd;
             begin
               match e, f with
               | F, F -> new_bdd
               | F, _ -> Hashtbl.add one (ref m) (); new_bdd
               | _, F -> Hashtbl.add zero (ref m) (); new_bdd
               | _ -> Hashtbl.add zero (ref m) (); Hashtbl.add one (ref m) (); new_bdd
             end
  in
  Bddset.iter (fun m' -> let _ = aux m m' in ()) bdds;
  let visited = Hashtbl.create 101 in
  let rec aux2 m =
    try Hashtbl.find visited (ref m)
    with Not_found -> 
          match m with
          | F -> F
          | T -> T
          | N(a,b) ->
             let res = 
               match Hashtbl.find_opt zero (ref m), Hashtbl.find_opt one (ref m) with
               | None, None -> F
               | None, Some _ -> bdd_of F (aux2 b)
               | Some _, None -> bdd_of (aux2 a) F
               | Some _, Some _ -> bdd_of (aux2 a) (aux2 b)
             in
             Hashtbl.add visited (ref m) res;
             res
  in aux2 m

let mdd_consistency m m' = multiple_mdd_consistency m (Bddset.singleton m')




  

  

let draw_dot m =
  (* Outputs a string that can be processed with graphviz dot *)
  let s = ref "graph g {\n" in
  let counter = let x = ref (-1) in fun () -> incr x; !x in
  let indices = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find indices (ref m)
    with Not_found -> 
          let c = counter() in
          Hashtbl.add indices (ref m) c;
          match m with
          | T -> s := !s^""^(string_of_int c)^" [label=\"\",shape=plaintext,width=.1,height=0];\n";c
          | F -> c
          | N(F,b) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let cb = aux b in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int cb)^";\n";
                      c
          | N(a,F) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let ca = aux a in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int ca)^" [style=dotted];\n";
                      c
          | N(a,b) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let cb, ca = aux b, aux a in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int cb)^";\n";
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int ca)^" [style=dotted];\n";
                      c
  in
  let _ = aux m in
  s := !s^"}";
  !s^"\n"
        
let rec split_backtrack m =
  (* Split the bdd into two bdds such that the union of them is the original bdd *)
  match m with
  | T | F -> failwith "split_backtrack: Can't split leaves"
  | N(b,a) when is_leaf b -> let c,d = split_backtrack a in
                             bdd_of b c, bdd_of b d
  | N(a,b) when is_leaf b -> let c,d = split_backtrack a in
                             bdd_of c b, bdd_of d b
  | N(a,b) -> bdd_of a F, bdd_of F b

let string_of_bddset b = 
  "{"^(Bddset.fold (fun elt acc -> string_of_bdd elt^" ; "^acc) b "")^"}"
  
let increase_value hash key value =
    Hashtbl.add hash key (value + try Hashtbl.find hash key with Not_found -> 0)
  
let rec replace_chain hash start reference =
  (* I have a hashtable that changes bdds into others, and I have to do it many times *)
  try let x = Hashtbl.find hash (reference start) in
      match Pervasives.compare x start with
      | 0 -> start
      | _ -> replace_chain hash x reference
  with Not_found -> start
        
let limit m width heuristic = (* suppose that width >= 1 *)
  (* This function takes as input a bdd, and returns a limited-width bdd overapproximating the previous one *)
  let nb_paths_to = Hashtbl.create 101 in
  Hashtbl.add nb_paths_to (ref m) 1;
  let replace = Hashtbl.create 101 in
  let rec reduce layer = match Bddset.cardinal layer with
    | n when n <= width -> layer
    | n -> let (m1, m2) = heuristic layer nb_paths_to in
           let uni = union m1 m2 in
           if uni != m1 then begin increase_value nb_paths_to (ref uni) (Hashtbl.find nb_paths_to (ref m1));
                                   Hashtbl.add replace (ref m1) uni end;
           if uni != m2 then begin increase_value nb_paths_to (ref uni) (Hashtbl.find nb_paths_to (ref m1));
                                   Hashtbl.add replace (ref m2) uni end;
           reduce (Bddset.add uni (Bddset.remove m1 (Bddset.remove m2 layer)))
  in
  let rec aux layer = match Bddset.cardinal layer with
    | 0 -> ()
    | _ -> aux (Bddset.fold (
                    fun elt acc -> match elt with
                                   | T | F | N(T,T) | N(T,F) | N(F,T) | N(F,F) -> acc
                                   | N(T, a) | N(F,a) | N(a,T) | N(a,F) -> increase_value nb_paths_to (ref a) (Hashtbl.find nb_paths_to (ref elt));
                                                                           Bddset.add a acc
                                   | N(a,b) -> increase_value nb_paths_to (ref a) (Hashtbl.find nb_paths_to (ref elt));
                                               increase_value nb_paths_to (ref b) (Hashtbl.find nb_paths_to (ref elt));
                                               Bddset.add a (Bddset.add b acc)
                  )(reduce layer) Bddset.empty)
  in
  aux (Bddset.singleton m);
  let visited = Hashtbl.create 101 in
  let rec replace_bdd m =
    try Hashtbl.find visited (ref m)
    with Not_found ->
          match replace_chain replace m ref with
          | T -> T
          | F -> F
          | N(a,b) -> let res = bdd_of (replace_bdd a) (replace_bdd b)
                      in
                      Hashtbl.add visited (ref m) res;
                      res
  in
  replace_bdd m

let bdd_first_come_heuristic bdds paths =
  Bddset.fold (fun e a -> begin match e, a with
      | elt, (F, _) -> (elt, F)
      | elt, (a, F) -> (a, elt)
      | elt, acc -> acc end
    ) bdds (F,F)

let cardinal_inter m m' =
  (* computes the cardinal of m\m' *)
  let visited = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find visited (ref m,ref m')
    with Not_found -> 
      let res = match m, m' with
        | T,T -> 1
        | F,_ | _,F -> 0
        | a,T | T, a -> aux a T (* should not happen *)
        | N(a,b), N(c,d) -> (aux a b) + (aux b d)
      in
      Hashtbl.add visited (ref m,ref m') res;
      res
  in
  aux m m'
  
let bdd_merge_value_heuristic bdds nb_paths_to =
  let rec aux bdds acc =
    (* the try is here to say that when the set is empty, stop searching *)
    try let elt = Bddset.choose bdds in
        let nb_paths_to_elt = Hashtbl.find nb_paths_to (ref elt) in
        let card_elt = cardinal elt in
        let new_blss = Bddset.remove elt bdds in
        aux new_blss (Bddset.fold (fun elt2 (best, best_value) ->
                          (* We compute the merge value as defined in my report *)
                          let cardinal_two = cardinal_inter elt elt2 in
                          let current_value = nb_paths_to_elt*(cardinal elt2 - cardinal_two) + (Hashtbl.find nb_paths_to (ref elt2))*(card_elt - cardinal_two) in
                          if (current_value < best_value || best_value = max_int) then ((elt, elt2), current_value) else (best, best_value)
                        ) new_blss acc)
    with Not_found -> acc
  in
  fst (aux bdds ((F, F),max_int))
  
  
let limited_bdd_of_bitlistset bls width heuristic =
  (* TODO BUG This function returns bdds that have bigger width... *)
  let nb_paths_to = Hashtbl.create 101 in
  Hashtbl.add nb_paths_to bls 1;
  let replacement = Hashtbl.create 101 in
  let hash_split = Hashtbl.create 101 in
  let rec reduce layer =
         match Blsetset.cardinal layer > width with
         | false -> layer
         | true -> let s1, s2 = heuristic layer nb_paths_to in
                   let s = Blset.union s1 s2 in
                   if Blset.compare s s1 != 0 then (increase_value nb_paths_to s (Hashtbl.find nb_paths_to s1);
                                                    Hashtbl.add replacement s1 s);
                   if Blset.compare s s2 != 0 then (increase_value nb_paths_to s (Hashtbl.find nb_paths_to s2);
                                                    Hashtbl.add replacement s2 s);
                   reduce (Blsetset.add s (Blsetset.remove s1 (Blsetset.remove s2 layer)))
       in
  let rec compute_layer blsset = match Blsetset.is_empty blsset, Blsetset.exists (fun x -> Blset.exists (fun y -> y != []) x) blsset with
    | true, _ | _, false -> ()
    | _ ->
       let new_layer = Blsetset.fold (fun t acc ->
                           let (zero, one) = split_zero_one t in
                           Hashtbl.add hash_split t (zero, one);
                           match Blset.is_empty zero, Blset.is_empty one with
                           | true, true -> acc
                           | true, false -> increase_value nb_paths_to one (Hashtbl.find nb_paths_to t);
                                            Blsetset.add one acc
                           | false, true -> increase_value nb_paths_to zero (Hashtbl.find nb_paths_to t);
                                            Blsetset.add zero acc
                           | false, false -> increase_value nb_paths_to one (Hashtbl.find nb_paths_to t);
                                             increase_value nb_paths_to zero (Hashtbl.find nb_paths_to t);
                                             Blsetset.add zero (Blsetset.add one acc)
                         ) blsset Blsetset.empty in
       compute_layer (reduce new_layer)
  in
  compute_layer (Blsetset.add bls (Blsetset.empty));
  let already_computed = Hashtbl.create 101 in
  let rec generate_bdd blset =
    try Hashtbl.find already_computed blset
    with Not_found -> 
          match Blset.is_empty blset with
          | true -> Hashtbl.add already_computed blset F;F
          | false ->
             match Blset.exists (fun x -> x != []) blset with
             | true ->
                let (zero, one) = Hashtbl.find hash_split blset in (*split_zero_one blset in *)
                let nextone = bdd_of (generate_bdd (replace_chain replacement zero (fun x -> x))) (generate_bdd (replace_chain replacement one (fun x -> x))) in
                Hashtbl.add already_computed blset nextone;
                nextone
             | false -> Hashtbl.add already_computed blset T;T
  in
  generate_bdd bls

let first_come_heuristic blss nb_paths_to =
  Blsetset.fold (fun e a -> begin match e, a with
      | elt, acc when Blset.is_empty elt-> acc
      | elt, (a, _) when Blset.is_empty a -> (elt, Blset.empty)
      | elt, (a, b) when Blset.is_empty b -> (a, elt)
      | elt, acc -> acc end
    ) blss (Blset.empty, Blset.empty)

let find hash key =
  Hashtbl.fold (fun k v acc ->
      if Blset.compare k key = 0 then v else acc
    ) hash (-1)
  
let merge_value_heuristic blss nb_paths_to =
  let rec aux blss acc =
    try let elt = Blsetset.choose blss in
        let nb_paths_to_elt = find nb_paths_to elt in
        let new_blss = Blsetset.remove elt blss in
        aux new_blss (Blsetset.fold (fun elt2 (best, best_value) ->
                          (* We compute the merge value as defined in my report *)
                          let current_value = nb_paths_to_elt*(Blset.cardinal (Blset.diff elt2 elt)) + (find nb_paths_to elt2)*(Blset.cardinal (Blset.diff elt elt2)) in
                          if current_value < best_value then ((elt, elt2), current_value) else (best, best_value)
                        ) new_blss acc)
    with Not_found -> acc
  in
  fst (aux blss ((Blset.empty, Blset.empty),max_int))

(*let rec a_lot_of_tests size =
  match size < 12 with
  | false -> ()
  | true -> print_string ("BDD OF SIZE "^(string_of_int size));print_newline();
            let randomset = bdd_of_bitlistset (random_set size) in
            let rec aux width_max =
              match width_max with
              | 1 -> ()
              | _ -> let random_bdd = limit randomset width_max bdd_first_come_heuristic in
                     let improved_bdd = limit randomset width_max bdd_merge_value_heuristic in
                     print_string ("Width "^(string_of_int width_max)^"  --  Random "^(string_of_int (cardinal random_bdd))^"  --  Improved "^(string_of_int (cardinal improved_bdd))); print_newline();
                     if fst (width random_bdd) > width_max then print_string "fail random\n";
                     if fst (width improved_bdd) > width_max then print_string "fail improved\n";
                     aux (width_max - 1)
            in
            aux (4*size);
            print_newline();
            a_lot_of_tests (size + 1)*)

let extract_depth_k m wanted_depth =
  (* give the bddset of all the bdds at depth k in m, that are now a chain of N(a,a), and the bdd (to have it of the good depth *)
  let visited = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find visited (ref m);
    with Not_found -> 
      let res = 
        match depth m = wanted_depth, m with
        | true, _ -> Bddset.singleton m
        | false, T | false, F -> failwith "extract_depth_k: The wanted depth has not been found in the bdd"
        | false, N(a,b) -> Bddset.map (fun x -> bdd_of x x) (Bddset.union (aux a) (aux b))
      in 
      Hashtbl.add visited (ref m) res;
      res
  in
  aux m

let same_mod_propagator x x' k =
  (* Propagator for constraint x \congr x' [2^k] *)
  (multiple_mdd_consistency x (extract_depth_k x' k), multiple_mdd_consistency x' (extract_depth_k x k))

let cst_mod_propagator x c k =
  (* Propagator for constraint x mod 2^k = c with c a constant *)
  mdd_consistency x (bdd_of_int c k (depth x))

(* Binary operations: increase the width, should be used for propagators *)
  
let bdd_not =
  let hash_and = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find hash_and (ref m)
    with Not_found ->
          let res =
            match m with
            | T -> F
            | F -> T
            | N(a,b) -> bdd_of (aux b) (aux a)
          in
          Hashtbl.add hash_and (ref m) res;
          res
  in aux
  
let bdd_and =
  let hash_and = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_and (ref_repr m m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> T
            | F,_ | _,F -> F
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (union (aux a d) (aux b c))) (aux b d)
          in
          Hashtbl.add hash_and (ref_repr m m') res;
          res
  in aux
  
let bdd_or =
  let hash_or = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_or (ref_repr m m')
    with Not_found ->
          let res =
            match m, m' with
            | F,x | x,F -> x
            | T,T -> T
            | T,_ | _,T -> failwith "bdd_or: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (aux a c) (union (aux a d) (union (aux b c) (aux b d)))
          in
          Hashtbl.add hash_or (ref_repr m m') res;
           res
  in aux
  
let bdd_xor =
  let hash_xor = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_xor (ref_repr m m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> F
            | F,a | a,F -> bdd_not a
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (aux b d)) (union (aux a d) (aux b c))
          in
          Hashtbl.add hash_xor (ref_repr m m') res;
          res
  in aux

let rec inter_with_union bdd bdds =
  match bdd with
  | F -> F
  | T -> if Bddset.is_empty bdds then F else T
  | N(a,b) ->
     let zero, one = Bddset.fold (fun elt (zeroacc, oneacc) ->
                         match elt with
                         | F -> (zeroacc, oneacc)
                         | T -> failwith "inter_with_union : not the same size"
                         | N(F,F) -> failwith "inter_with_union : N(F,F) should be equal to F"
                         | N(F,a) -> (zeroacc, Bddset.add a oneacc)
                         | N(a,F) -> (Bddset.add a zeroacc, oneacc)
                         | N(a,b) -> (Bddset.add a zeroacc, Bddset.add b oneacc)
                       ) bdds (Bddset.empty, Bddset.empty) in
     bdd_of (inter_with_union a zero) (inter_with_union b one)

let rec list_compare elt_compare l1 l2 =
  match l1,l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x::q, y::r -> begin match elt_compare x y with
                  | 0 -> list_compare elt_compare q r
                  | a -> a end

let bdd_compare m1 m2 = Pervasives.compare (ref m1) (ref m2)
                
module Orderedbddbddlist =
  struct
    type t = bdd * Bddset.t
    let compare (m1,m2) (m1', m2') =
      match Pervasives.compare (ref m1) (ref m1') with
      | 0 -> Bddset.compare m2 m2'
      | a -> a
  end
  
module Bddbddsset = Set.Make(Orderedbddbddlist)

module Bddsmap = Map.Make(Bddset)
                 
let improved_consistency m m' width choice =
  let replacement = Hashtbl.create 101 in
  let add_to_hash hash bdd set new_set =
    (* useful function to add a set to a hashtbl in a hashtbl *)
    Hashtbl.add hash (ref bdd) (try Bddsmap.add set new_set (Hashtbl.find hash (ref bdd))
                                with Not_found -> Bddsmap.singleton set new_set)
  in
  let split_zero_one bdds =
    Bddset.fold (fun elt (zeroacc, oneacc) ->
        match elt with
        | T -> failwith "test_change_name: not the same size"
        | F -> (zeroacc, oneacc)
        | N(F,F) -> failwith "inter_with_union : N(F,F) should be equal to F"
        | N(F,c) -> (zeroacc, Bddset.add c oneacc)
        | N(c,F) -> (Bddset.add c zeroacc, oneacc)
        | N(c,d) -> (Bddset.add c zeroacc, Bddset.add d oneacc)
      ) bdds (Bddset.empty, Bddset.empty)
  in
  let rec reduce bddbsset =
    (*print_endline "reduce";
    print_string "{"; Bddbddsset.iter (fun (bdd, bdds) -> print_string ((string_of_bdd bdd)^(string_of_bddset bdds)^"\n")) bddbsset; print_string "}";*)
    match Bddbddsset.cardinal bddbsset > width with
    (* take a layer as input, and return a reduced layer (with width smaller than said), and update the replacement hashtbl *)
    | false -> bddbsset
    | true -> let s1, s2 = choice bddbsset in
              (*print_endline (string_of_bdd (fst s1));
              print_endline (string_of_bddset (snd s1));
              print_endline (string_of_bdd (fst s1));
              print_endline (string_of_bddset (snd s1));
              let _ = read_line() in*)
              if fst s1 != fst s2 then failwith "the choice returned two nodes that don't come from the same node";
              let merge_union = Bddset.union (snd s1) (snd s2) in
              add_to_hash replacement (fst s1) (snd s1) merge_union;
              add_to_hash replacement (fst s2) (snd s2) merge_union;
              reduce (Bddbddsset.add (fst s1, merge_union) (Bddbddsset.remove s1 (Bddbddsset.remove s2 bddbsset)))
  in
  let rec compute_layer bddbss =
    (*print_endline "compute_layer";*)
    let new_layer = Bddbddsset.fold (fun (m, bdds) acc ->
                        match m with
                        | T | F -> acc
                        | N(F,F) -> failwith "NFF should not happen because it is reduced"
                        | N(F,a) ->
                           let zero, one = split_zero_one bdds in
                           Bddbddsset.add (a, one) acc
                        | N(a,F) -> 
                           let zero, one = split_zero_one bdds in
                           Bddbddsset.add (a, zero) acc
                        | N(a,b) ->
                           let zero, one =  split_zero_one bdds in
                           Bddbddsset.add (a,zero) (Bddbddsset.add (b,one) acc)
                      ) bddbss Bddbddsset.empty
    in
    if Bddbddsset.is_empty new_layer then () else compute_layer (reduce new_layer)
  in
  let rec replace_chain_set (bdd, bdds) =
    (* Find the new bdd to use (aux function *)
    try let bdd_map = Hashtbl.find replacement (ref bdd) in
        (*let next_one = Hashtbl.fold (fun k v acc -> match Bddset.is_empty acc with
                                     | false -> acc
                                     | true -> if Bddset.compare k bdds = 0 then v else acc
                         ) bdd_hash Bddset.empty in
        if Bddset.is_empty next_one then failwith "the bddset is not present" else (replace_chain_set (bdd, next_one))*)
        try (bdd, Bddsmap.find bdds bdd_map)
        with Not_found -> (bdd, bdds)
    with Not_found -> (bdd, bdds)
  in
  let count = ref 0 in
  let rec generate_new_bdd bdd bdds =
    incr count;
    (*print_endline (string_of_int (!count));*)
    (* Will generate the new bdd *)
    let (new_bdd, new_bdds) = replace_chain_set (bdd, bdds) in
    match new_bdd, Bddset.is_empty bdds with
    | F, _ | _, true -> F
    | T, false -> T (*if Bddset.compare (Bddset.singleton T) new_bdds = 0 then T else (print_endline ("test");failwith ("not the same depth while generating new bdd"^(string_of_bddset bdds)))*)
    | N(a,b), false -> 
       let zero, one = split_zero_one new_bdds in
       bdd_of (generate_new_bdd a zero) (generate_new_bdd b one)
  in
  compute_layer (Bddbddsset.singleton (m, Bddset.singleton m'));
  generate_new_bdd m (Bddset.singleton (m'))


let random_heuristic_improved_consistency bddbss =
  let bdd_exists = Hashtbl.create 101 in
  Bddbddsset.fold (fun (bdd, bdds) ((bddacc, bddsacc), acc) ->
      match Bddset.is_empty bddsacc with
      | false -> (bddacc, bddsacc), acc
      | true -> try (bdd,Hashtbl.find bdd_exists (ref bdd)), (bdd, bdds)
                 with Not_found -> Hashtbl.add bdd_exists (ref bdd) bdds; (bddacc, bddsacc), acc
    ) bddbss ((F, Bddset.empty), (F, Bddset.empty))

let _ = Random.init 0
  
let starting = limit (bdd_of_bitlistset (random_set 6)) 2 bdd_merge_value_heuristic

let _ = Random.init 1
             
let wrt = bdd_of_bitlistset (random_set 6)

let result = improved_consistency starting wrt 4 random_heuristic_improved_consistency
           
let _ = print_endline (draw_dot result)











    