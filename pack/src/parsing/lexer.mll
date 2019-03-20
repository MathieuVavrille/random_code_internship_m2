{
open Parser;;        (* le type "token" est défini dans parser.mli *)

exception Eof;;
}

rule token = parse    (* la "fonction" aussi s'appelle token *)

  | '&'      	      	      { END }    
  | ';' 		      { SEMIC }
  | ',' 		      { COMMA }
  | '('                       { LPAREN }
  | ')'                       { RPAREN }

  | "XOR"		      { XOR }
  | "SB" 		      { SB }
  | "MC" 		      { MC }

  | (['a'-'z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s) {VAR (s) }
  | [' ' '\t' '\n']           { token lexbuf }  
  | "(*" ('*'[^')'] | [^'*'])* '*'? "*)"       { token lexbuf }  (* Comments *)
  | eof                       { EOF } 



