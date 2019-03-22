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

module Chmap = Map.Make(Char)
             
let int_of_hex =
  let conversion = Chmap.add 'A' 10 (Chmap.add 'B' 11 (Chmap.add 'C' 12 (Chmap.add 'D' 13 (Chmap.add 'E' 14 (Chmap.add 'F' 15 Chmap.empty))))) in
  let rec aux n map = match n with
    | -1 -> map
    | _ -> aux (n-1) (Chmap.add (string_of_int n).[0] n map)
  in aux 9 conversion

let int_of_hexstring s =
  let res = ref 0 in
  for i=0 to String.length s - 1 do
    res := try Chmap.find s.[i] int_of_hex + 16 * !res with Not_found -> print_string (Char.escaped s.[i]); failwith "test";
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

let array_diff_sbox_outputs =
  let res = Array.make 256 Intset.empty in
  for i=0 to 255 do
    for j=0 to 255 do
      res.(i lxor j) <- Intset.add (sbox.(i) lxor sbox.(j)) res.(i lxor j)
    done
  done;
  res
  
  
let input_output_bdd output_fun =
  (* return a bdd where the values are \delta X \concat \delta Y *)
  let rec aux n set =
    let rec aux2 m set2 = match m with
      | -1 -> set2
      | _ -> let res = (((n lxor m) lsl 8) lor ((output_fun.(n)) lxor (output_fun.(m)))) in
             aux2 (m-1) (Bvset.add (bitvect_of_int res 16) set2)
    in
    match n with
    | -1 -> set
    | _ -> aux (n-1) (aux2 255 set)
  in
  bdd_of_bitvectset (aux 255 Bvset.empty)

let input_output_sbox = input_output_bdd sbox

let input_output_inverse_sbox = input_output_bdd inverse_sbox

                              
let possible_outputs m bdd_fun =
  let rec aux m current_bdd_fun acc = match m,current_bdd_fun with
    | T,_ -> Bddset.add current_bdd_fun acc
    | F,_ | _, F -> acc
    | N(a,b), N(c,d) -> aux a c (aux b c acc)
    | N _, _ -> failwith "possible_outputs: the bdd_fun is not big enough"
  in
  aux m bdd_fun Bddset.empty
  
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
      
let mix_column_bdd x0 x1 x2 x3 =
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
  
let inverse_mix_column_bdd y0 y1 y2 y3 =
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

let gl_double_int x =
  if x land 128 = 0 then x lsl 1 else (x lsl 1) lxor 27

let gl_triple_int x =
  gl_double_int x lxor x
  
let mix_column_int x0 x1 x2 x3 =
  (gl_double_int x0) lxor (gl_triple_int x1) lxor x2 lxor x3,
  (gl_double_int x1) lxor (gl_triple_int x2) lxor x3 lxor x0,
  (gl_double_int x2) lxor (gl_triple_int x3) lxor x0 lxor x1,
  (gl_double_int x3) lxor (gl_triple_int x0) lxor x1 lxor x2
  
let generate_program r =
  let underscores a b c = string_of_int a^"_"^(string_of_int b)^"_"^(string_of_int c) in
  let s = ref "" in
  for j=0 to 3 do
    for k=0 to 3 do
      s := !s^"XOR(xinit_"^(string_of_int j)^"_"^(string_of_int k)^", k_"^(underscores 0 j k)^", x"^(underscores 0 j k)^");\n"
    done
  done;
  for i= 0 to r-1 do
    if i <> 0 then (* On first round the bytes of X are computed from the input *)
        for j=0 to 3 do
          for k=0 to 3 do
            s := !s^"XOR(z_"^(underscores (i-1) j k)^", k_"^(underscores i j k)^", x"^(underscores i j k)^");\n"
          done
        done;
    for j=0 to 3 do
      for k=0 to 3 do
        s := !s^"SB(x_"^(underscores i j k)^", sx_"^(underscores i j k)^");\n"
      done
    done;
    if i <> r-1 then (* No MC on last round *)
      for k=0 to 3 do
        s := !s^"MC(sx_"^(underscores i 0 k)^", sx_"^(underscores i 1 ((k+1) mod 4))^", sx_"^(underscores i 2 ((k+2) mod 4))^", sx_"^(underscores i 3 ((k+3) mod 4))^", z_"^(underscores i 0 k)^", z_"^(underscores i 1 k)^", z_"^(underscores i 2 k)^", z_"^(underscores i 3 k)^");\n"
      done;
    for j=0 to 3 do
      s := !s^"SB(k_"^(underscores i j 3)^", sk_"^(underscores i j 3)^");\n";
    done;
    if i <> 0 then begin
        for j=0 to 3 do
          s := !s^"XOR(k_"^(underscores i j 0)^",k_"^(underscores (i-1) j 0)^", sk_"^(underscores (i-1) ((j+1) mod 4) 3)^");\n"
        done;
        for j=0 to 3 do
          for k=1 to 3 do
            s := !s^"XOR(k_"^(underscores i j k)^", k_"^(underscores i j (k-1))^", k_"^(underscores (i-1) j k)^");\n"
          done
        done
      end;
    done;
    !s^"&"
              
