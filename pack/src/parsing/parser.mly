%{
open Solver
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
%type <Solver.Cstrset.t> main
%%

main:
  | END               { Cstrset.empty }  /* on veut reconnaître un "instr" */
  | XOR LPAREN VAR COMMA VAR COMMA VAR RPAREN SEMIC main { Cstrset.add (Xor($3, $5, $7)) $10 }
  | MC LPAREN VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR RPAREN SEMIC main { Cstrset.add (Mc($3, $5, $7, $9, $11, $13, $15, $17)) $20 }
  | SB LPAREN VAR COMMA VAR RPAREN SEMIC main { Cstrset.add (Sb($3, $5)) $8 }
  | PSB LPAREN VAR COMMA VAR RPAREN SEMIC main { Cstrset.add (Psb($3, $5)) $8 }
  | ZERO LPAREN VAR RPAREN SEMIC main { Cstrset.add (Zero($3)) $6 }
  | NOTZERO LPAREN VAR RPAREN SEMIC main { Cstrset.add (Not_zero($3)) $6 }
;
