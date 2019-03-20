type cstr = Xor of string * string * string
          | Mc of  string * string * string * string * string * string * string * string
          | Sb of  string * string

let string_of_cstr c = match c with
  | Xor(a,b,c) -> "XOR("^a^","^b^","^c^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^a^","^b^","^c^","^d^","^e^","^f^","^g^","^h^")"
  | Sb(a,b) -> "SB("^a^","^b^")"
