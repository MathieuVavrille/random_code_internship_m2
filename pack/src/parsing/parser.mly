%{
    open Solver
    open Useful
    let all_sbox = ref []
    let sbox_inactive = ref Strset.empty
%}

/* description des lexèmes, ceux-ci sont décrits dans lexer.mll */

%token <string> VAR
%token <int> INT
%token XOR MC SB CST
%token COMMA SEMIC
%token LPAREN RPAREN
%token ZERO NOTZERO
%token EOF END

%nonassoc LPAREN RPAREN


%start main
%type <Solver.Cstrset.t * string list * int ref> main
%%

main:
  | cstr           { let cstrset = $1 in
		     let active_sbox_list = List.fold_left (fun acc (x,y) -> if Strset.mem x !sbox_inactive then acc else (x,y)::acc) [] !all_sbox in
		     let cstr_bound = ref (-7 * List.length active_sbox_list) in
		     List.fold_left (fun acc (x,y) -> if Strset.mem x !sbox_inactive then Cstrset.add (Zero(y)) acc else acc) (Cstrset.add (ActiveSB(active_sbox_list, cstr_bound)) cstrset) !all_sbox, List.rev (List.fold_left (fun acc (a,b) -> a::b::acc) [] !all_sbox), cstr_bound }

cstr:
  | END            { Cstrset.empty }
  | XOR LPAREN VAR COMMA VAR COMMA VAR RPAREN SEMIC cstr { Cstrset.add (Xor($3, $5, $7)) $10 }
  | MC LPAREN VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR RPAREN SEMIC cstr { Cstrset.add (Mc($3, $5, $7, $9, $11, $13, $15, $17)) $20 }
  | SB LPAREN VAR COMMA VAR RPAREN SEMIC cstr { all_sbox := ($3, $5)::(!all_sbox); $8 }
  | ZERO LPAREN VAR RPAREN SEMIC cstr { sbox_inactive := Strset.add $3 !sbox_inactive;Cstrset.add (Zero($3)) $6 }
  | NOTZERO LPAREN VAR RPAREN SEMIC cstr { Cstrset.add (Not_zero($3)) $6 }
  | CST LPAREN VAR COMMA INT RPAREN SEMIC cstr  { Cstrset.add (Iscst($3, $5)) $8 }
;
