open Useful
open Bdd
   
let sbox_hex =
  [|[| "6A"; "7C"; "77";"7B";"F2";"6B";"6F";"C5";"30";"01";"67";"2B";"FE";"D7";"AB";"76"|];
    [| "CA"; "82"; "C9";"7D";"FA";"59";"47";"F0";"AD";"D4";"A2";"AF";"9C";"A4";"72";"C0"|];
    [| "B7";"FD";"93";"26";"36";"3F";"F7";"CC";"34";"A5";"E5";"F1";"71";"D8";"31";"15"|];
    [| "04";"C7";"23";"C3";"18";"96";"05";"9A";"07";"12";"80";"E2";"EB";"27";"B2";"75"|];
    [| "09";"83";"2C";"1A";"1B";"6E";"5A";"A0";"52";"3B";"D6";"B3";"29";"E3";"2F";"84"|];
    [| "53";"D1";"00";"ED";"20";"FC";"B1";"5B";"6A";"CB";"BE";"39";"4A";"4C";"58";"CF"|];
    [| "D0";"EF";"AA";"FB";"43";"4D";"33";"85";"45";"F9";"02";"7F";"50";"3C";"9F";"A8"|];
    [| "51";"A3";"40";"8F";"92";"9D";"38";"F5";"BC";"B6";"DA";"21";"10";"FF";"F3";"D2"|];
    [| "CD";"0C";"13";"EC";"5F";"97";"44";"17";"C4";"A7";"73";"3D";"64";"5D";"19";"73"|];
    [| "60";"81";"4F";"DC";"22";"2A";"90";"88";"46";"EE";"B8";"14";"DE";"5E";"0B";"DB"|];
    [| "E0";"32";"3A";"0A";"49";"06";"24";"5C";"C2";"D3";"AC";"62";"91";"95";"E4";"79"|];
    [| "E7";"C8";"37";"6D";"8D";"D5";"4E";"A9";"6C";"56";"F4";"EA";"65";"7A";"AE";"08"|];
    [| "BA";"78";"25";"2E";"1C";"A6";"B4";"C6";"E8";"DD";"74";"1F";"4B";"BD";"8B";"8A"|];
    [| "70";"3E";"B5";"66";"48";"03";"F6";"0E";"61";"35";"57";"B9";"86";"C1";"1D";"9E"|];
    [| "E1";"F8";"98";"11";"69";"D9";"8E";"94";"9B";"1E";"87";"E9";"CE";"55";"28";"DF"|];
    [| "8C";"A1";"89";"0D";"BF";"E6";"42";"68";"41";"99";"2D";"0F";"B0";"54";"BB";"16"|]|]

module Smap = Map.Make(Char)

let int_of_hex =
  let conversion = Smap.add 'A' 10 (Smap.add 'B' 11 (Smap.add 'C' 12 (Smap.add 'D' 13 (Smap.add 'E' 14 (Smap.add 'F' 15 Smap.empty))))) in
  let rec aux n map = match n with
    | -1 -> map
    | _ -> aux (n-1) (Smap.add (string_of_int n).[0] n map)
  in aux 9 conversion

let int_of_hexstring s =
  let res = ref 0 in
  for i=0 to String.length s - 1 do
    res := try Smap.find s.[i] int_of_hex + 16 * !res with Not_found -> print_string (Char.escaped s.[i]); failwith "test";
  done;
  !res

let sbox =
  Array.init 256 (fun i -> int_of_hexstring sbox_hex.(i lsr 4).(i land 15))
  
let inverse_sbox =
  let inverse = Array.make 256 0 in
  Array.iteri (fun i elt -> inverse.(elt) <- i) sbox;
  inverse
      
let sbox_fun x =
  sbox.(x)

let input_output_diff_sbox =
  (* return a bdd where the values are \delta X \concat \delta Y *)
  let rec aux n set =
    let rec aux2 m set2 = match m with
      | -1 -> set2
      | _ -> let res = (((n lxor m) lsl 8) lor ((sbox_fun n) lxor (sbox_fun m))) in
             aux2 (m-1) (Bvset.add (bitvect_of_int res 16) set2)
    in
    match n with
    | -1 -> set
    | _ -> aux (n-1) (aux2 255 set)
  in
  bdd_of_bitvectset (aux 255 Bvset.empty)

let add_zero_end =
  let last = bdd_of T F in
  let computed = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find computed (ref m)
    with Not_found ->
          let res = match m with
            | T -> last
            | F -> F
            | N(a,b) -> bdd_of (aux a) (aux b)
          in
          Hashtbl.add computed (ref m) res;
          res
  in aux
               
let gl_double m =
  match m with
  | T | F -> failwith "lsl: the BDD is a leave"
  | N(a,b) -> union (add_zero_end a) (bdd_xor (add_zero_end b) (bdd_of_int 27 8 8))

let gl_triple m =
  bdd_xor (gl_double m) m
      
let mix_column x0 x1 x2 x3 =
  bdd_xor (gl_double x0) (bdd_xor (gl_triple x1) (bdd_xor x2 x3)),
  bdd_xor (gl_double x1) (bdd_xor (gl_triple x2) (bdd_xor x3 x0)),
  bdd_xor (gl_double x2) (bdd_xor (gl_triple x3) (bdd_xor x0 x1)),
  bdd_xor (gl_double x3) (bdd_xor (gl_triple x0) (bdd_xor x1 x2))

let gl_nine powers =
  bdd_xor powers.(0) powers.(3)

let gl_eleven powers =
  bdd_xor powers.(0) (bdd_xor powers.(1) powers.(3))

let gl_thirteen powers =
  bdd_xor powers.(0) (bdd_xor powers.(2) powers.(3))

let gl_fourteen powers =
  bdd_xor powers.(1) (bdd_xor powers.(2) powers.(3))
  
let inverse_mix_column y0 y1 y2 y3 =
  let powers_array = Array.make_matrix 4 4 F in
  powers_array.(0).(0) <- y0;
  powers_array.(1).(0) <- y1;
  powers_array.(2).(0) <- y2;
  powers_array.(3).(0) <- y3;
  for i=1 to 3 do
    for j=0 to 3 do
      powers_array.(j).(i) <- gl_double (powers_array.(j).(i-1));
    done
  done;
  bdd_xor (gl_fourteen powers_array.(0)) (bdd_xor (gl_eleven powers_array.(1)) (bdd_xor (gl_thirteen powers_array.(2)) (gl_nine powers_array.(3)))),
  bdd_xor (gl_fourteen powers_array.(1)) (bdd_xor (gl_eleven powers_array.(2)) (bdd_xor (gl_thirteen powers_array.(3)) (gl_nine powers_array.(0)))),
  bdd_xor (gl_fourteen powers_array.(2)) (bdd_xor (gl_eleven powers_array.(3)) (bdd_xor (gl_thirteen powers_array.(0)) (gl_nine powers_array.(1)))),
  bdd_xor (gl_fourteen powers_array.(3)) (bdd_xor (gl_eleven powers_array.(0)) (bdd_xor (gl_thirteen powers_array.(1)) (gl_nine powers_array.(2))))
  
