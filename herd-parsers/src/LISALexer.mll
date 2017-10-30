{
  open Lexing
  open LISAParser

  exception Error of string

  (* Utility function that takes an indentifier and tries to parse it as a register or variable name. *)
  let parse_identifier (name : string) : token = try
      let length = String.length name in
      let start = String.get name 0 in
      let id = String.sub name 1 (length - 1) in
      if start = 'r' then REGISTER (int_of_string id) else WORD name
    with _ -> WORD name
}

let whitespace = [' ' '\t' '\r']+
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let identifier = alpha (alpha | digit | '_' | '/' | '-')*
(* TODO: `digit` doesn't include 'a'-'f', so the 0x prefix is useless. Remove, fix, or issue warnings. *)
let number = '-'? "0x"? digit+

(* Entrypoint for scanning the header section, reutrns architecture name (which should be "LISA"). *)
rule header = parse
| identifier as name	{ header_ignored lexbuf; name}

(* Rules for scanning the rest of the header after the architecture. *)
and header_ignored = parse
| [^ '{' '\n']* '\n'	{ new_line lexbuf; header_ignored lexbuf }
| [^ '{' '\n']*			{ () }

(* Lexer for litmus tests written in LISA (Litmus Instruction Set Architecture). *)
(* Expects the header to be handled separately before being called. *)
and program = parse
| whitespace			{ program lexbuf }
| '\n'					{ new_line lexbuf; program lexbuf }
(* TODO: Ocaml comments are included in the Herd lexer, but are they actually useful for LISA? *)
| "(*"					{ comment 0 lexbuf; program lexbuf }
| number as value		{ INT (int_of_string value) }
| 'P' (number as id)	{ THREAD (int_of_string id) }
| ';'					{ SEMICOLON }
| '.'					{ DOT }
| ','					{ COMMA }
| '|'					{ PIPE }
| ':'					{ COLON }
| '+'					{ PLUS }
(* TODO: Remove.
| 'b'					{ BRANCH }
| 'r'					{ READ }
| 'w'					{ WRITE }
| 'f'					{ FENCE }
| "rmw"					{ RMW }
| "mov"					{ MOV }
| "add"					{ ADD }
| "and"					{ AND }
| "eq"					{ EQUAL }
| "ne"					{ NOT_EQUAL }
*)
| '('					{ ROUNDL }
| ')'					{ ROUNDR }
| '['					{ SQUAREL }
| ']'					{ SQUARER }
| '{'					{ CURLYL }
| '}'					{ CURLYR }
| identifier as value	{ parse_identifier value }
| eof					{ EOF }
| _						{ raise (Error ("unexpected " ^ Lexing.lexeme lexbuf)) }

(* Special lexer rules for nested Ocaml comments. *)
and comment depth = parse
| "(*"					{ comment (depth + 1) lexbuf }
| "*)"					{ if depth > 0 then comment (depth - 1) lexbuf }
| '\n'					{ new_line lexbuf; comment depth lexbuf }
| eof					{ raise (Error "unterminated comment") }
| _						{ comment depth lexbuf }

(* HACK. *)
{
  let string_of_token token = match token with
  | INT value -> Printf.sprintf "int %d" value
  | THREAD id -> Printf.sprintf "thread %d" id
  | SEMICOLON -> "semicolon"
  | DOT -> "dot"
  | COMMA -> "comma"
  | PIPE -> "pipe"
  | COLON -> "colon"
  | PLUS -> "plus"
  | ROUNDL -> "round left"
  | ROUNDR -> "round right"
  | SQUAREL -> "square left"
  | SQUARER -> "square right"
  | CURLYL -> "curly left"
  | CURLYR -> "curly right"
  | REGISTER name -> Printf.sprintf "register %d" name
  | WORD text -> Printf.sprintf "word %s" text
  | EOF -> "eof"

  let program lexbuf =
    let token = program lexbuf in
    Printf.printf "Token: \"%s\" => %s\n" (lexeme lexbuf) (string_of_token token);
    token
}
