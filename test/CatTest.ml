open Printf
module T = ModelParser
module L = ModelLexer.Make(LexUtils.Default)

let use_stdin = ref false

let parse filename f  =
  let lexbuf = Lexing.from_channel f in
  try
    let r = T.main L.token lexbuf in
    close_in_noerr f;
    r
  with
    | T.Error ->
      let {
        Lexing.pos_lnum=line;
        Lexing.pos_bol=c0;
        Lexing.pos_fname=_;
        Lexing.pos_cnum=c1
      } = Lexing.lexeme_start_p lexbuf in
      let msg = sprintf "%s:%d:%d: parse error" filename line (c1-c0+1) in
      raise (Util.Parsing_failed msg)

let run filename =
  let file_chan = match !use_stdin with
      true -> stdin
    | false -> open_in filename
  in
  let _ = parse filename file_chan in
  ()

let cmd_spec =
  Arg.align [
      "-",  Arg.Unit (fun x -> use_stdin:= true; (run "stdin")), "  read from stdin"
  ]

let () =
  Arg.parse cmd_spec run (sprintf "%s <infiles>" (Sys.executable_name))

