open Lexing

(* TODO: Move LISA stuff to new module. *)

exception Error of string

(* Raise an error with the given text and position information from lexbuf. *)
let raise_error (lexbuf : lexbuf) (text : string) : 'a =
  let at = lexbuf.lex_curr_p in
  let column = at.pos_cnum - at.pos_bol + 1 in
  raise (Error (Printf.sprintf "%s:%d:%d: %s" at.pos_fname at.pos_lnum column text))

(* Check for LISA header and find start of actual program, raise Error on failure. *)
let find_header (lexbuf : lexbuf) : unit =
  let architecture = try LISALexer.header lexbuf
  with
  | LISALexer.Error text -> raise_error lexbuf text in
  if architecture <> "LISA" then
    raise_error lexbuf (Printf.sprintf "expected architecture \"LISA\", found \"%s\"" architecture)

(* Call the lexer/parser and return the result, raise Error on failure. *)
let lex_and_parse (input : string) : string =
  let lexbuf = from_string input in
  find_header lexbuf;
  try LISAParser.parse LISALexer.program lexbuf
  with
  | LISAParser.Error -> raise_error lexbuf "unexpected token"
  | LISALexer.Error text -> raise_error lexbuf text
;;

(* TODO: Check whether the parser can match on things like (WORD "keyword"), rewrite if not. *)
let input: string = "LISA\n{}\na" in
let output: string = lex_and_parse input in
Printf.printf "%s\n" output;
