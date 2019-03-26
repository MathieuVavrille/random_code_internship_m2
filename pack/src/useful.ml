open Bdd
   
(**********************************)
(* Some useful string conversions *)

let string_of_array f a =
  "["^(Array.fold_left (fun acc x -> acc^(f x)^";") "" a)^"]" 
              
let string_of_list f l = "["^(List.fold_left (fun acc elt -> acc^(f elt)^";") "" l)^"]"

                       
(**********************)
(* Module definitions *)

(* Set of BDD using the structural equality/comparison *)
module Orderedbdd =
  struct
    type t = bdd
    let compare = bdd_compare
  end

module Bddset = Set.Make(Orderedbdd)

let string_of_bddset b = 
  "{"^(Bddset.fold (fun elt acc -> string_of_bdd elt^" ; "^acc) b "")^"}"

module Bddsmap = Map.Make(Bddset)

               
module OrderedBitVector =
  (* Actually a bit-list *)
  struct
    type t = bool list
    let rec compare l1 l2 = match l1, l2 with
      | [], [] -> 0
      | false::_, true::_ -> -1
      | true::_, false::_ -> 1
      | _::q1, _::q2 -> compare q1 q2
      | [], _ -> -1
      | _, [] -> 1
  end

(* Set of bit-vectors *)
module Bvset = Set.Make(OrderedBitVector)

let string_of_bvset b =
  "{"^(Bvset.fold (fun elt acc -> string_of_list string_of_bool elt^" ; "^acc) b "")^"}"

module Bvsetset = Set.Make(Bvset)

let string_of_bvsetset b = 
  "{"^(Bvsetset.fold (fun elt acc -> string_of_bvset elt^" ; "^acc) b "")^"}"

                
module Orderedbddbddlist =
  struct
    type t = bdd * Bddset.t
    let compare (m1,m2) (m1', m2') =
      match Pervasives.compare (ref m1) (ref m1') with
      | 0 -> Bddset.compare m2 m2'
      | a -> a
  end
  
module Bddbddsset = Set.Make(Orderedbddbddlist)

module Strmap = Map.Make(String)

module Strset = Set.Make(String)
              
module Intset = Set.Make(struct type t = int let compare = Pervasives.compare end)

module Intmap = Map.Make(struct type t = int let compare = Pervasives.compare end)
              
(* Functions to create or extract bdds *)
               
let bitvect_of_int integer size =
  (* Get the binary representation of an integer on size bits *)
  let rec aux acc integer size =
    match size with
    | 0 -> acc
    | _ -> aux ((integer mod 2 = 1)::acc) (integer/2) (size - 1)
  in aux [] integer size

let split_zero_one set =
  (* Splits a bit-list set into the ones that starts with zero and the ones that start with one *)
  Bvset.fold
    (fun elt (zero, one) -> match elt with
                            | [] -> (zero, one)
                            | true::q -> (zero, Bvset.add q one)
                            | false::q -> (Bvset.add q zero, one)
    ) set (Bvset.empty, Bvset.empty)
  
let rec bdd_of_bitvectset set =
  (* Returns the bdd representing the bitlistset *)
  match Bvset.is_empty set with
  | true -> F
  | false ->
     match Bvset.exists (fun x -> x != []) set with
     | true -> let (zero, one) = split_zero_one set in
               bdd_of (bdd_of_bitvectset zero) (bdd_of_bitvectset one)
     | false -> T

let bdd_of_intlist l size =
  (* Return the bdd representing the list of integers represented on -size- bits *)
  bdd_of_bitvectset (List.fold_left (fun acc elt ->
                     Bvset.add (bitvect_of_int elt size) acc) Bvset.empty l)

let bdd_of_int integer size depth =
  (* Return the bdd representing a single integer (on size bits) and the bdd have depth depth *)
  let rec aux acc integer size depth =
    match size, depth with
    | 0, 0 -> acc
    | 0, _ -> aux (bdd_of acc acc) 0 0 (depth - 1)
    | _, _ -> aux (if integer mod 2 = 0 then bdd_of acc F else bdd_of F acc) (integer/2) (size-1) (depth-1)
  in
  aux T integer size depth
   
let bitvectset_of_bdd =
  (* Returns the bitlistset represented by the bdd *)
  let computed = Hashtbl.create 101 in
  let rec aux t =
    try Hashtbl.find computed (ref t)
    with Not_found ->
          let res = match t with
            | F -> Bvset.empty
            | T -> Bvset.add [] Bvset.empty
            | N(a,b) -> Bvset.union (Bvset.map (fun l -> false::l) (aux a)) (Bvset.map (fun l -> true::l) (aux b))
          in
          Hashtbl.add computed (ref t) res;
          res
  in aux

let int_of_bdd m =
  let rec aux m acc = match m with
    | T -> acc
    | F -> failwith "int_of_bdd: Can't give int from empty set"
    | N(a,F) -> aux a (2*acc)
    | N(F,a) -> aux a (2*acc+1)
    | _ -> failwith "int_of_bdd: Can't give int from set with multiple values"
  in aux m 0

let rec pow a n =
  match n with
  | 0 -> 1
  | n -> a*(pow a (n-1))
       
let random_set max =
  (* This function generates bdds of mean cardinal 2^{max-1}, which may not be representative *)
  let rec aux acc current =
    match current with
    | -1 -> acc
    | n -> match Random.bool () with
           | true -> aux (Bvset.add (bitvect_of_int current max) acc) (current-1)
           | false -> aux acc (current-1)
  in
  aux Bvset.empty (pow 2 max)

let rec complete_bdd depth = match depth with
  | 0 -> T
  | _ -> let res = complete_bdd (depth-1) in
         bdd_of res res
  
    
let dot_file m filename =
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
  let open Printf in
  let oc = open_out filename in
  fprintf oc "%s\n" !s;
  close_out oc

let save_to_file m filename =
  let counter = let x = ref 1 in fun () -> incr x; !x in
  let index = Hashtbl.create 101 in
  Hashtbl.add index (ref T) 0;
  Hashtbl.add index (ref F) 1;
  let s = ref "" in
  let rec aux m =
    try Hashtbl.find index (ref m)
    with Not_found ->
          match m with
          | T -> 0
          | F -> 1
          | N(a,b) ->
             let current_count = counter () in
             Hashtbl.add index (ref m) current_count;
             let ai, bi = aux a, aux b in
             s := !s^(string_of_int current_count)^":"^(string_of_int ai)^","^(string_of_int bi)^";";
             current_count
  in
  let _ = aux m in
  let open Printf in
  let oc = open_out filename in
  fprintf oc "%s" !s;
  close_out oc

let get_from_file filename =
  let ic = open_in filename in
  let text = input_line ic in
  close_in ic;
  let full_map = List.fold_left (fun acc elt -> if elt = "" then acc else begin
                                     match String.split_on_char ':' elt with
                                     | x::[y] -> let a,b = match String.split_on_char ',' y with
                                                   | astr::[bstr] -> Strmap.find astr acc, Strmap.find bstr acc
                                                   | _ -> failwith "second error on the file"
                                                 in
                                                 Strmap.add x (bdd_of a b) acc
                                     | _ -> failwith "error on the file"
                                                  end ) (Strmap.add "0" T (Strmap.singleton "1" F)) (String.split_on_char ';' text) in
  Strmap.find "2" full_map
  
  (* Some other useful functions *)

let rec list_compare f l1 l2 = match l1, l2 with
  | [], [] -> 0
  | _, [] -> -1
  | [], _ -> 1
  | x::q, y::r -> match f x y with
                  | 0 -> list_compare f q r
                  | n -> n
