open Bdd
open Useful
open Bddhash

let _ = Random.init 0
  
let starting = limit (bdd_of_bitlistset (random_set 6)) 2 bdd_merge_value_heuristic

let _ = Random.init 1
             
let wrt = bdd_of_bitlistset (random_set 6)

let result = improved_consistency starting wrt 4 random_heuristic_improved_consistency
           
let _ = dot_file result "graph.dot"
