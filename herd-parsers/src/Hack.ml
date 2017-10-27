open Lexing

exception LISAError of string

(* Raise an error with the given text and position information from lexbuf. *)
let raise_error (lexbuf : lexbuf) (text : string) : 'a =
  let at = lexbuf.lex_curr_p in
  let column = at.pos_cnum - at.pos_bol + 1 in
  raise (LISAError (Printf.sprintf "%s:%d:%d: %s" at.pos_fname at.pos_lnum column text))

(* Call the lexer/parser and return the result, raise LISAError on failure. *)
let lex_and_parse (input : string) : string =
  let lexbuf = from_string input in
  try LISAParser.parse LISALexer.lex lexbuf
  with
  | LISAParser.Error -> raise_error lexbuf "unexpected token"
  | LISALexer.Error text -> raise_error lexbuf text
;;

(* TODO: This doesn't produce remotely sensible output from either the lexer nor the parser, fix. *)
(* TODO: new_line seems to do nothing, check. *)
(* TODO: Check whether the parser can match on things like (WORD "keyword"), rewrite if not. *)
(* TODO: Replace tabs with spaces. *)
let input: string = "a{}\na" in
let output: string = lex_and_parse input in
Printf.printf "%s\n" output;
