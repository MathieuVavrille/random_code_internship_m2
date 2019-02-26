type data = {depth:int; cardinality:int}
type bdd = T | F | N of bdd * bdd (* first part is for 0, second part is for 1*)

exception Not_same_depth
                      
let is_leaf m = match m with
  | T | F -> true
  | _ -> false
                      
let rec bdd_to_string t = match t with
  | T -> "T"
  | F -> "F"
  | N(a,b) -> "N("^(bdd_to_string a)^","^(bdd_to_string b)^")"

let main_hash = Hashtbl.create 101

let ref_repr a b = (ref a, ref b)

let _ = Hashtbl.add main_hash (ref_repr F F) F
      
let bdd_of a b =
  try Hashtbl.find main_hash (ref_repr a b)
  with Not_found -> let t = N(a,b) in Hashtbl.add main_hash (ref_repr a b) t; t

let rec reduce tree = match tree with
  | T | F -> tree
  | N(a,b) -> bdd_of (reduce a) (reduce b)

let print_bool b = match b with
  | true -> print_string "true"
  | false -> print_string "false"

let mdd_consistency m m' = (* I am almost sure that there is a bug *)
  (* ensures MDD consistency on m wrt m' and returns m *)
  let zero = Hashtbl.create 101 in (* all the nodes whose 0-edge is consistent *)
  let one = Hashtbl.create 101 in (* all the nodes whose 1-edge is consistent *)
  let inter = Hashtbl.create 101 in (* just a set, but faster by using hashtbl *)
  let rec aux m m' = match Hashtbl.find_opt inter (ref_repr m m') with
    | Some b -> b
    | None -> 
       match m, m' with
       | F, _ | _, F -> F
       | T, _ -> m'
       | N(a,b), T ->
          Hashtbl.add inter (ref_repr m m') m;
          begin
            match a,b with
            | F, F -> F (* should not happen because the bdd is reduced *)
            | F, _ -> Hashtbl.add one (ref m) (); aux b T
            | _, F -> Hashtbl.add zero (ref m) (); aux a T
            | _, _ -> Hashtbl.add zero (ref m) (); Hashtbl.add one (ref m) (); bdd_of (aux a T) (aux b T)
          end
       | N(a,b), N(c,d) ->
          let e,f = aux a c, aux b d in
          let new_bdd = bdd_of e f in
          Hashtbl.add inter (ref_repr m m') new_bdd;
          begin
            match e, f with
            | F, F -> new_bdd
            | F, _ -> Hashtbl.add one (ref m) (); new_bdd
            | _, F -> Hashtbl.add zero (ref m) (); new_bdd
            | _ -> Hashtbl.add zero (ref m) (); Hashtbl.add one (ref m) (); new_bdd
          end
  in
  let _ = aux m m' in
  let visited = Hashtbl.create 101 in
  let rec aux2 m = match m with
    | F -> F
    | T -> T
    | N(a,b) -> begin
        match Hashtbl.find_opt visited (ref m), Hashtbl.find_opt zero (ref m), Hashtbl.find_opt one (ref m) with
        | Some t, _, _ -> t
        | _, None, None -> Hashtbl.add visited (ref m) F;
                           F
        | _, None, Some _ -> let t = bdd_of F (aux2 b) in
                             Hashtbl.add visited (ref m) t;
                             t
        | _, Some _, None -> let t = bdd_of (aux2 a) F in
                             Hashtbl.add visited (ref m) t;
                             t
        | _, Some _, Some _ -> let t = bdd_of (aux2 a) (aux2 b) in
                               Hashtbl.add visited (ref m) t;
                               t
      end
  in aux2 m


(* Some functions to create bdds *)
   
exception Uncomparable of string
  
module OrderedBitList =
  struct
    type t = bool list
    let rec compare l1 l2 = match l1, l2 with
      | [], [] -> 0
      | false::_, true::_ -> -1
      | true::_, false::_ -> 1
      | _::q1, _::q2 -> compare q1 q2
      | _ -> raise (Uncomparable "Can't compare bitlists of different size")
  end

module Blset = Set.Make(OrderedBitList)

let split_zero_one set =
  Blset.fold
    (fun elt (zero, one) -> match elt with
                            | [] -> (zero, one)
                            | true::q -> (zero, Blset.add q one)
                            | false::q -> (Blset.add q zero, one)
    ) set (Blset.empty, Blset.empty)
                  
let rec bdd_of_bitlistset set =
  match Blset.is_empty set with
  | true -> F
  | false ->
     match Blset.exists (fun x -> x != []) set with
     | true -> let (zero, one) = split_zero_one set in
               bdd_of (bdd_of_bitlistset zero) (bdd_of_bitlistset one)
     | false -> T

let bitlist_from_int integer size =
  let rec aux acc integer size =
    match size with
    | 0 -> acc
    | _ -> aux ((integer mod 2 = 1)::acc) (integer/2) (size - 1)
  in aux [] integer size
   
let rec bitlistset_from_bdd t = match t with
  | F -> Blset.empty
  | T -> Blset.add [] Blset.empty
  | N(a,b) -> Blset.union (Blset.map (fun l -> false::l) (bitlistset_from_bdd a)) (Blset.map (fun l -> true::l) (bitlistset_from_bdd b))

let bdd_from_intlist l size =
  bdd_of_bitlistset (List.fold_left (fun acc elt ->
                     Blset.add (bitlist_from_int elt size) acc) Blset.empty l)



  

  
let intersection =
  (* The intersection of two bdds. Can increase the width *)
  (* This function (as well as the union) uses implicit caching: it returns a function using caching, the user does not touch it *)
  let inter_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find inter_hash (ref_repr m m')
    with Not_found ->
      let t = match m, m' with
        | F, _ | _, F-> F
        | T, _ -> m'
        | _, T -> m
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add inter_hash (ref_repr m m') t;
      t
  in aux

let union =
  (* The union of two bdds. Can increase the width. Uses caching like the intersection *)
  let union_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find union_hash (ref_repr m m')
    with Not_found ->
      let t = match m, m' with
        | T, _ | _, T -> T
        | F, _ -> m'
        | _, F -> m
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add union_hash (ref_repr m m') t;
      t
  in aux
   
let one_set, other_set =
  (* Some test examples *)
  let rec aux start acc = match start with
    | -1 -> acc
    | _ -> aux (start-1) (Blset.add (bitlist_from_int start 4) acc)
  in bdd_of_bitlistset (aux 14 Blset.empty), bdd_of_bitlistset (aux 13 Blset.empty) 


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
  !s

module Orderedbdd =
  struct
    type t = bdd
    let compare m m' = Pervasives.compare (ref m) (ref m')
  end

module Bddset = Set.Make(Orderedbdd)
  
let rec replace_chain hash start =
  (* I have a hashtable that changes bdds into others, and I have to do it many times *)
  try replace_chain hash (Hashtbl.find hash (ref start))
  with Not_found -> start
        
let limit m width choose = (* suppose that width >= 1 *)
  (* This function takes as input a bdd, and returns a limited-width bdd overapproximating the previous one *)
  let replace = Hashtbl.create 101 in
  let rec reduce layer = match Bddset.cardinal layer with
    | n when n <= width -> layer
    | n ->let (m1, m2) = choose layer in
          let uni = union m1 m2 in
          Hashtbl.add replace (ref m1) uni;
          Hashtbl.add replace (ref m2) uni;
          Bddset.add (union m1 m2) (Bddset.remove m1 (Bddset.remove m2 layer))
  in
  let rec aux layer = match Bddset.cardinal layer with
    | 0 -> ()
    | _ -> aux (Bddset.fold (
                    fun elt acc -> match elt with
                                   | T | F | N(T,T) | N(T,F) | N(F,T) | N(F,F) -> acc
                                   | N(T, a) | N(F,a) | N(a,T) | N(a,F) -> Bddset.add a acc
                                   | N(a,b) -> Bddset.add a (Bddset.add b acc)
                  )(reduce layer) Bddset.empty)
  in
  aux (Bddset.add m Bddset.empty);
  let rec replace_bdd m =
    match replace_chain replace m with
    | T -> T
    | F -> F
    | N(a,b) -> bdd_of (replace_bdd a) (replace_bdd b)
  in
  replace_bdd m

exception Unsplittable
        
let rec split_backtrack m =
  (* Split the bdd into two bdds such that the union of them is the original bdd *)
  match m with
  | T | F -> raise Unsplittable
  | N(b,a) when is_leaf b -> let c,d = split_backtrack a in
                             bdd_of b c, bdd_of b d
  | N(a,b) when is_leaf b -> let c,d = split_backtrack a in
                             bdd_of c b, bdd_of d b
  | N(a,b) -> bdd_of a F, bdd_of F b

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
                  let res = (max d1 d2, match c1+c2 < 0 with (* With this I deal with overflows *)
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
  
  
let starting = bdd_from_intlist [1;5;6;7;9;10;11;12] 4

let wrt = bdd_from_intlist [0;1;6;7;8;9;10;11;12;13] 4

let bool_couple_to_int (a,b) = (if a then 1 else 0) + 2*(if b then 1 else 0)
        
let choice a width =
  (* could be improved by using the number of each parent for each possibility *)
  Array.map (fun h ->
      let new_h = Hashtbl.create 101 in
      let counter = ref 0 in
      Hashtbl.iter (fun k v ->
          match !(v.(3)) > 0, !(v.(1)) > 0, !(v.(2)) > 0 with
          | true, _, _ | _, true, true -> incr counter; Hashtbl.add new_h k (Array.init 4 (fun i -> if i = 3 then true else false))
          | _, true, false -> incr counter; Hashtbl.add new_h k (Array.init 4 (fun i -> if i = 1 then true else false))
          | _, false, true -> incr counter; Hashtbl.add new_h k (Array.init 4 (fun i -> if i = 2 then true else false))
          | _ -> incr counter; Hashtbl.add new_h k (Array.init 4 (fun i -> if i = 0 then true else false))
        ) h;
      Hashtbl.iter (fun k v ->
          match !counter < width, !(v.(1)) > 0 && !(v.(2)) > 0 with
          | true, true -> let a = Hashtbl.find new_h k in
                          a.(3) <- false; a.(1) <- true; a.(2) <- true
          | _ -> ()) h;
      Hashtbl.iter (fun k v ->
          match !counter < width, !(v.(1)) > 0 with
          | true, true -> (Hashtbl.find new_h k).(1) <- true
          | _ -> ()) h;
      Hashtbl.iter (fun k v ->
          match !counter < width, !(v.(2)) > 0 with
          | true, true -> (Hashtbl.find new_h k).(2) <- true
          | _ -> ()) h;
      new_h
    ) a
  
let improved_consistency m m' choice width =
  (* returns the bdd that is the one after applying improved consistency on m wrt m' *)
  let layers = Array.init (depth m + 1) (fun i -> Hashtbl.create 101) in (* this hashtbl contains tuples representing the parents that link to the node with (only 0-edge, only 1-edge, two edges, no edge)*)
  let inter = Hashtbl.create 101 in
  let rec changes m m' parent =
    try Hashtbl.find inter (ref_repr m m')
    with Not_found ->
          let current = layers.(depth m)in
          let (has_zero, has_one) =
            let current_hash = try Hashtbl.find current (ref m)
                               with Not_found -> let h = Hashtbl.create 101 in Hashtbl.add current (ref m) h; h in
            try Hashtbl.find current_hash parent
            with Not_found -> Hashtbl.add current_hash parent (false,false); (false,false) in
          let res =
            match m with (* This big matching can be factorized by matching on m and m' TODO later *)
            | T | F -> m
                     
            | N(F,a) -> begin
                match m' with
                | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                | T -> Hashtbl.add (Hashtbl.find current (ref m)) parent (has_zero, true); T
                | N(_,F) -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                | N(_,c) -> begin
                    match changes a c (ref m) with
                    | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                    | _ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (has_zero, true); T
                  end
              end
                      
            | N(a,F) -> begin
                match m' with
                | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                | T -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, has_one); T
                | N(F,_) -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                | N(c,_) -> begin
                    match changes a c (ref m) with
                    | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                    | _ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, has_one); T
                  end
              end
                      
            | N(a,b) -> begin
                match m' with
                | T -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, true); T
                | F | N(F,F)-> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false);F 
                | N(F,c) -> begin
                    match changes b c (ref m) with
                    | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                    | _ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (has_zero, true); T
                  end
                | N(c,F) -> begin
                    match changes a c (ref m) with
                    | F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                    | _ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, has_one); T
                  end
                | N(c,d) -> begin
                    match changes a c (ref m), changes b d (ref m) with
                    | F,F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (false, false); F
                    | F,_ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (has_zero, true); T
                    | _,F -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, has_one); T
                    | _ -> Hashtbl.add (Hashtbl.find current (ref m)) parent (true, true); T
                  end
              end
          in 
          Hashtbl.add inter (ref_repr m m') res;
          res
  in
  let _ = changes m m' (ref m) in
  let inverted_layers = Array.map (fun h ->
                            let h' = Hashtbl.create 101 in
                            Hashtbl.iter (fun k v ->
                                Hashtbl.iter (fun k' v' ->
                                    let index = bool_couple_to_int v' in
                                    try incr (Hashtbl.find h' k).(index)
                                    with Not_found -> let a = Array.init 4 (fun x -> ref 0) in
                                                      incr a.(index);
                                                      Hashtbl.add h' k a
                                  ) v;
                              ) h; h'
                          ) layers in
  (* TODO: for each node in each layer, count the number of occurences of each pair of possibilities, this array will go in the function that will choose the nodes to split *)
  let new_layers = choice inverted_layers width in
  let visited = Hashtbl.create 101 in
  let rec apply m parent = print_string "enter\n";
    try Hashtbl.find visited (ref m, parent)
    with Not_found ->
          let res = match m with
            | T | F -> m
            | N(a,b) -> let pos = bool_couple_to_int (try Hashtbl.find (Hashtbl.find layers.(depth m) (ref m)) parent with _ -> print_string (bdd_to_string m); raise Not_found) in
                        let c = Hashtbl.find new_layers.(depth m) (ref m) in
                        match c.(pos), pos with
                        | _, 0 -> F
                        | false, _ | true, 3 -> bdd_of (apply a (ref m)) (apply b (ref m))
                        | true, 1 -> bdd_of (apply a (ref m)) F
                        | true, 2 -> bdd_of F (apply b (ref m))
                        | _ -> F (* Impossible to get here *)
          in
          Hashtbl.add visited (ref m, parent) res;
          res
  in
  apply m (ref m)
                                                  
(* Bug because I have not always filled the hashtable *)  







  
let _ = print_string (draw_dot (starting))

          
