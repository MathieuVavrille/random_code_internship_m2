(* BDDs are trees and nodes have a 0-edge (first of the couple) and a 1-edge (second element of the couple) *)
type bdd = T | F | N of bdd * bdd

(* The hashtable that will contain all the trees *)
let main_hash = Hashtbl.create 101

(* Ensures that N(F,F) = F *)
let _ = Hashtbl.add main_hash (ref F,ref F) F

(* One should never use the N constructor but this one instead (to ensure maximal sharing) *)
let bdd_of a b =
  try Hashtbl.find main_hash (ref a,ref b)
  with Not_found -> let t = N(a,b) in Hashtbl.add main_hash (ref a,ref b) t; t

let is_leaf m = match m with
  | T | F -> true
  | _ -> false

(* Conversion function *)
let rec string_of_bdd t = match t with
  | T -> "T"
  | F -> "F"
  | N(a,b) -> "N("^(string_of_bdd a)^","^(string_of_bdd b)^")"
       
let depth_card  =
  (* Returns the depth of the bdd and the cardinality of the set it represents (bounded by max_int, bigger than this will return max_int *) 
  let data = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find data (ref m)
    with Not_found ->
      match m with
      | T -> Hashtbl.add data (ref T) (0,1); (0,1)
      | F -> Hashtbl.add data (ref F) (0,0); (0,0)
      | N(a,b) -> let (d1,c1),(d2,c2) = aux a, aux b in
                  let res = (max d1 d2+1, match c1+c2 < 0 with (* With this I deal with overflows *)
                                        | true -> max_int
                                        | false -> c1+c2) in
                  Hashtbl.add data (ref m) res; res
  in aux
   
(* These two functions return in constant time amortized (I think, if there is a lot of accesses) *)   
let depth m = fst (depth_card m)

let cardinal m = snd (depth_card m)

let width m =
  (* Give the width of a bdd *)
  let visited = Hashtbl.create 101 in
  let widths = Array.make (depth m + 1) 0 in
  let rec aux m =
    try Hashtbl.find visited (ref m)
    with Not_found ->
          Hashtbl.add visited (ref m) ();
          widths.(depth m) <- widths.(depth m) + 1;
          match m with
          | T | F -> ()
          | N(a,b) -> let _ = aux a, aux b in ()
  in
  aux m;
  Array.fold_left (fun acc elt ->
      max acc elt
    ) 0 widths, widths





(********************************)
(* Set theoretics, uses caching *)
  
let intersection =
  (* The intersection of two bdds. Can increase the width. Don't ensure that the bdd have same depth *)
  let inter_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find inter_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | F, _ | _, F-> F
        | T, _ -> m'
        | _, T -> m
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add inter_hash (ref m,ref m') t;
      t
  in aux

let union =
  (* The union of two bdds. Can increase the width *)
  let union_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find union_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | _, T | T, _ -> T
        | F, _ -> m'
        | _, F -> m
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add union_hash (ref m,ref m') t;
      t
  in aux

let diff =
  (* The difference of two bdds. Can increase the width *)
  let diff_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find diff_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | _, T | F, _ -> F
        | _, F -> m
        | T, N _ -> failwith "diff: the bdds does not have the same size"
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add diff_hash (ref m,ref m') t;
      t
  in aux

   
(**********************)
(* Bitwise operations *)   

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
    try Hashtbl.find hash_and (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> T
            | F,_ | _,F -> F
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (union (aux a d) (aux b c))) (aux b d)
          in
          Hashtbl.add hash_and (ref m,ref m') res;
          res
  in aux
  
let bdd_or =
  let hash_or = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_or (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | F,x | x,F -> x
            | T,T -> T
            | T,_ | _,T -> failwith "bdd_or: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (aux a c) (union (aux a d) (union (aux b c) (aux b d)))
          in
          Hashtbl.add hash_or (ref m,ref m') res;
           res
  in aux
  
let bdd_xor =
  let hash_xor = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_xor (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> F
            | F,a | a,F -> bdd_not a
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (aux b d)) (union (aux a d) (aux b c))
          in
          Hashtbl.add hash_xor (ref m,ref m') res;
          res
  in aux



(* Module definitions *)
module Orderedbdd =
  struct
    type t = bdd
    let compare m m' = Pervasives.compare (ref m) (ref m')
  end

module Bddset = Set.Make(Orderedbdd)
