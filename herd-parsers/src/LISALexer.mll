{
	open Lexing
	open LISAParser

	exception LexerError of string

	(* Utility function that takes an indentifier and tries to parse it as a register or variable name. *)
	let parse_identifier (name : string) : token option =
		try
			let length = String.length name in
			let start = String.get name 0 in
			let id = String.sub name 1 (length - 1) in
			if start = 'r' then REGISTER (int_of_string id) else VARIABLE name
		with _ -> VARIABLE name
}

let whitespace = [' ' '\t' '\r']*
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let identifier = alpha (alpha | digit | '_' | '/' | '-')*
(* TODO: `digit` doesn't include 'a'-'f', so the 0x prefix is useless. Remove, fix, or issue warnings. *)
let number = '-'? "0x"? digit+

(* Lexer for litmus tests written in LISA (Litmus Instruction Set Architecture). *)
(* This entry point actually just discards the header metadata before starting the real lexer. *)
rule lex = parse
| [^ '{']* '\n'			{ new_line lexbuf; parse lexbuf }
| [^ '{']* '{'			{ program lexbuf }
| eof					{ raise (LexerError "Found EOF but no program") }

(* The real lexer, triggered after the header is discarded. *)
and program = parse
| whitespace			{ program lexbuf }
| '\n'					{ new_line lexbuf; program lexbuf }
(* TODO: Ocaml comments are included in the original lexer, but are they actually useful for LISA? *)
| "(*"					{ comment 0 lexbuf }
| number as value		{ INT (int_of_string value) }
| 'P' (number as id)	{ THREAD (int_of_string id) }
| ';'					{ SEMICOLON }
| '.'					{ DOT }
| ','					{ COMMA }
| '|'					{ PIPE }
| ':'					{ COLON }
| '+'					{ PLUS }
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
| '('					{ ROUNDL }
| ')'					{ ROUNDR }
| '['					{ SQUAREL }
| ']'					{ SQUARER }
| '{'					{ CURLYL }
| '}'					{ CURLYR }
| identifier as value	{ parse_identifier value }
| eof					{ EOF }
| _						{ raise (LexerError ("Unexpected " ^ Lexing.lexeme lexbuf)) }

(* Special lexer rules for nested Ocaml comments. *)
and comment depth = parse
| "(*"					{ comment depth + 1 lexbuf }
| "*)"					{ if depth == 0 then program lexbuf else comment depth - 1 lexbuf }
| '\n'					{ new_line lexbuf; comment depth lexbuf; }
| eof					{ raise (LexerError "Unterminated comment") }
| _						{ comment depth lexbuf }
