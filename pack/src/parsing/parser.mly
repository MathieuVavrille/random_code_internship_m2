%{
open Solver
%}

/* description des lexèmes, ceux-ci sont décrits dans lexer.mll */

%token <string> VAR
%token XOR MC SB
%token COMMA SEMIC
%token LPAREN RPAREN
%token ZERO NOTZERO
%token EOF END

%nonassoc LPAREN RPAREN


%start main
%type <Solver.cstr list> main
%%

main:
  | END               { [] }  /* on veut reconnaître un "instr" */
  | XOR LPAREN VAR COMMA VAR COMMA VAR RPAREN SEMIC main { Xor($3, $5, $7)::$10 }
  | MC LPAREN VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR COMMA VAR RPAREN SEMIC main { Mc($3, $5, $7, $9, $11, $13, $15, $17)::$20 }
  | SB LPAREN VAR COMMA VAR RPAREN SEMIC main { Sb($3, $5)::$8 }
  | ZERO LPAREN VAR RPAREN SEMIC main { Zero($3)::$6 }
  | NOTZERO LPAREN VAR RPAREN SEMIC main { Not_zero($3)::$6 }
;
