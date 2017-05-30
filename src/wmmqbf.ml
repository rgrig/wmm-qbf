open Format
open WmmParser

exception Parsing_failed of string

let parse fn =
  let f = open_in fn in
  let lexbuf = Lexing.from_channel f in
  try
    let r = WmmParser.wmm WmmLexer.token lexbuf in
    close_in_noerr f;
    r
  with
    | WmmParser.Error ->
        (match Lexing.lexeme_start_p lexbuf with
        { Lexing.pos_lnum=line; Lexing.pos_bol=c0;
          Lexing.pos_fname=_; Lexing.pos_cnum=c1} ->
            let msg = sprintf "@[%s:%d:%d: parse error@]" fn line (c1-c0+1) in
            raise (Parsing_failed msg))

let do_one fn =
  let wmm = parse fn in
  ()

let () =
  Arg.parse [] do_one "wmmqbf <infile>"
