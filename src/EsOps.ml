let parse filename f =
  let lexbuf = Lexing.from_channel f in
  try
    let r = EsParser.top EsLexer.token lexbuf in
    close_in_noerr f;
    r
  with
  | EsParser.Error ->
    let {
      Lexing.pos_lnum=line;
      Lexing.pos_bol=c0;
      Lexing.pos_fname=_;
      Lexing.pos_cnum=c1
    } = Lexing.lexeme_start_p lexbuf
    in
    failwith (Printf.sprintf "%s:%d:%d: parse error" filename line (c1-c0+1))
