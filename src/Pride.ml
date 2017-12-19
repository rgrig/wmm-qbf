(* NOTE: This cannot go in [Config] because of cyclic module dependencies. *)
let available_models =
  ("j+r", JR.do_decide) (* default *)
  ::
  [ "common-valid-conf", ValidConf.do_decide
(* TODO  ; "j+r-enum", JR.do_enum *)
  ; "j+r-so", JRSO.do_decide
  ; "j+r-so2", JRSO2.do_decide
  ; "pes", PES.do_decide
  ; "pes-certifies", PESCertifies.do_decide
  ; "pes-follows", PESFollows.do_decide
  ; "pes-make-promise", PESMakePromise.do_decide
  ; "pes-promise-read", PESPromiseRead.do_decide
  ; "pes-transitions", PESTransitions.do_decide ]

(* TODO: Move to EsOps *)
let parse filename f =
  let lexbuf = Lexing.from_channel f in
  try
    let r = EsParser.top EsLexer.token lexbuf in
    close_in_noerr f;
    r
  with
  | EsParser.Error ->
    begin
      match Lexing.lexeme_start_p lexbuf with
        { Lexing.pos_lnum=line; Lexing.pos_bol=c0;
          Lexing.pos_fname=_; Lexing.pos_cnum=c1} ->
        let msg = Printf.sprintf "%s:%d:%d: parse error" filename line (c1-c0+1) in
        failwith (msg)
    end

let run_on_es filename ch =
  Config.set_current_file filename;
  match parse filename ch with
  | _, None -> Printf.eprintf "W: no target execution: skipping %s" filename
  | es, Some target -> (Config.model ()) es target

let run_on_lisa filename ch =
  let source = Wrapper.read_to_eof ch in
  let ast = Wrapper.load_litmus source in
  if Config.dump_lisa () then Wrapper.print_litmus ast
      
let run_on_file run filename =
  (match Util.on_channel filename (run filename) with
  | None -> Printf.eprintf "E: could not open %s\n" filename
  | Some () -> ())

let () =
  Config.parse_args available_models;
  List.iter (run_on_file run_on_es) (Config.es_files ());
  List.iter (run_on_file run_on_lisa) (Config.lisa_files ())

