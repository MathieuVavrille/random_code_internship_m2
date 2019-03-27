%{
    open Solver
    open Useful
    let sbox_active = ref []
    let sbox_inactive = ref Strset.empty
%}

/* description des lexèmes, ceux-ci sont décrits dans lexer.mll */

%token <string> VAR
%token XOR MC SB PSB
%token COMMA SEMIC
%token LPAREN RPAREN
%token ZERO NOTZERO
%token EOF END

%nonassoc LPAREN RPAREN


%start main
%type <Solver.Cstrset.t * string list> main
%%

main:
  | cstr           { let cstrset = $1 in
		     let active_sbox_list = List.fold_left (fun acc (x,y) -> if Strset.mem x !sbox_inactive then acc else (x,y)::acc) [] !sbox_active in
		     let cstr_bound = ref (-7 * List.length active_sbox_list) in
		     Cstrset.fold (fun cstr acc -> match cstr with
						   | Sb(a,b) -> if Strset.mem a !sbox_inactive then Cstrset.add (Zero(b)) acc else acc
						   | _ -> Cstrset.add cstr acc) cstrset (Cstrset.singleton (ActiveSB(active_sbox_list, cstr_bound))), List.rev (List.fold_left (fun acc (a,b) -> a::b::acc) [] !sbox_active) }

cstr:
  | END            { Cstrset.empty }
  | XOR LPAREN VAR COMMA VAR COMMA VAR RPAREN SEMIC cstr { Cstrset.add (Xor($3, $5, $7)) $10 }
  | MC LPAREN VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR RPAREN SEMIC cstr { Cstrset.add (Mc($3, $5, $7, $9, $11, $13, $15, $17)) $20 }
  | SB LPAREN VAR COMMA VAR RPAREN SEMIC cstr { sbox_active := ($3, $5)::(!sbox_active);Cstrset.add (Sb($3, $5)) $8 }
  | PSB LPAREN VAR COMMA VAR RPAREN SEMIC cstr { Cstrset.add (Psb($3, $5)) $8 }
  | ZERO LPAREN VAR RPAREN SEMIC cstr { sbox_inactive := Strset.add $3 !sbox_inactive;Cstrset.add (Zero($3)) $6 }
  | NOTZERO LPAREN VAR RPAREN SEMIC cstr { Cstrset.add (Not_zero($3)) $6 }
;
