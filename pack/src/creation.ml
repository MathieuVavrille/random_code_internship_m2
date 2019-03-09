(* Some functions to create bdds *)

open Bdd

module OrderedBitList =
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

module Blset = Set.Make(OrderedBitList)

let string_of_list f l = "["^(List.fold_left (fun acc elt -> acc^(f elt)^";") "" l)^"]"
       
let string_of_blset b =
  "{"^(Blset.fold (fun elt acc -> string_of_list string_of_bool elt^" ; "^acc) b "")^"}"

let split_zero_one set =
  Blset.fold
    (fun elt (zero, one) -> match elt with
                            | [] -> (zero, one)
                            | true::q -> (zero, Blset.add q one)
                            | false::q -> (Blset.add q zero, one)
    ) set (Blset.empty, Blset.empty)
                  
let rec bdd_of_bitlistset set =
  (* Returns the bdd representing the bitlistset *)
  match Blset.is_empty set with
  | true -> F
  | false ->
     match Blset.exists (fun x -> x != []) set with
     | true -> let (zero, one) = split_zero_one set in
               bdd_of (bdd_of_bitlistset zero) (bdd_of_bitlistset one)
     | false -> T

let bitlist_from_int integer size =
  (* Get the binary representation of an integer on size bits *)
  let rec aux acc integer size =
    match size with
    | 0 -> acc
    | _ -> aux ((integer mod 2 = 1)::acc) (integer/2) (size - 1)
  in aux [] integer size

let bdd_of_int integer size depth =
  (* Return the bdd representing a single integer (on size bits) and the bdd have depth depth *)
  let rec aux acc integer size depth =
    match size, depth with
    | 0, 0 -> acc
    | 0, _ -> aux (bdd_of acc acc) 0 0 (depth - 1)
    | _, _ -> aux (if integer mod 2 = 0 then bdd_of acc F else bdd_of F acc) (integer/2) (size-1) (depth-1)
  in
  aux T integer size depth
  
let rec bdd_of_bitlistset set =
  match Blset.is_empty set with
  | true -> F
  | false ->
     match Blset.exists (fun x -> x != []) set with
     | true -> let (zero, one) = split_zero_one set in
               bdd_of (bdd_of_bitlistset zero) (bdd_of_bitlistset one)
     | false -> T
   
let rec bitlistset_from_bdd t = match t with
  (* Returns the bitlistset represented by the bdd *)
  | F -> Blset.empty
  | T -> Blset.add [] Blset.empty
  | N(a,b) -> Blset.union (Blset.map (fun l -> false::l) (bitlistset_from_bdd a)) (Blset.map (fun l -> true::l) (bitlistset_from_bdd b))

let bdd_of_intlist l size =
  (* Return the bdd representing the list of integers represented on -size- bits *)
  bdd_of_bitlistset (List.fold_left (fun acc elt ->
                     Blset.add (bitlist_from_int elt size) acc) Blset.empty l)



module Blsetset = Set.Make(Blset)

let string_of_blsetset b = 
  "{"^(Blsetset.fold (fun elt acc -> string_of_blset elt^" ; "^acc) b "")^"}"

let rec pow a n =
  match n with
  | 0 -> 1
  | n -> a*(pow a (n-1))

       
let random_set max =
  let rec aux acc current =
    match current with
    | -1 -> acc
    | n -> match Random.bool () with
           | true -> aux (Blset.add (bitlist_from_int current max) acc) (current-1)
           | false -> aux acc (current-1)
  in
  aux Blset.empty (pow 2 max)
