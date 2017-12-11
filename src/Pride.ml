open Printf
open SoOps
module E = EventStructure
module U = Util

let enums = [
  ("j+r", JR.do_enum)
  (* ; ("pes", PES.do_enum) *)
]

let decides = [
  ("j+r", JR.do_decide)
; ("j+r-so", JRSO.do_decide)
; ("j+r-so2", JRSO2.do_decide)
; ("pes", PES.do_decide)
; ("pes-certifies", PESCertifies.do_decide)
; ("pes-follows", PESFollows.do_decide)
; ("pes-make-promise", PESMakePromise.do_decide)
; ("pes-promise-read", PESPromiseRead.do_decide)
; ("pes-transitions", PESTransitions.do_decide)
; ("common-valid-conf", ValidConf.do_decide)
]

let enum_mode = ref false
let use_stdin = ref false
let default_model = List.hd decides
let model_name = ref (fst default_model)
let dump_qbf = ref false
let dump_query = ref false
let dump_lisa = ref false
let use_solver = ref true
let use_lisa = ref false

let pick_model m models =
  let rec p ms =
    match ms with
      (x, f)::ms when x = m -> f
    | _::ms -> p ms
    | [] ->
      eprintf "Could not find model `%s'. Executing with model `%s' instead.\n" m (fst (List.hd models));
      snd (List.hd models)
  in
  p models

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
        let msg = sprintf "%s:%d:%d: parse error" filename line (c1-c0+1) in
        failwith (msg)
    end


let run filename =
  let file_chan = match !use_stdin with
      true -> stdin
    | false -> open_in filename
  in
  if not !use_lisa
  then
    let es, target = parse filename file_chan in
    let fn = Filename.remove_extension filename in
    if !enum_mode
    then (pick_model !model_name enums) fn es target !dump_qbf
    else
      match target with
      | None -> eprintf "W: skipping %s: no target execution\n" fn
      | Some target -> (pick_model !model_name decides) es target (!dump_qbf, !dump_query, !use_solver)
  else
    let source = Wrapper.read_to_eof (open_in filename) in
    let ast = Wrapper.load_litmus source in
    if !dump_lisa then
      Wrapper.print_litmus ast;
    ()

let print_models ms () =
  ignore @@ List.map (fun x -> Printf.eprintf "%s\n" (fst x)) ms;
  exit 0

let cmd_spec =
  Arg.align [
    "-e", Arg.Set enum_mode, "  enumerate all executions"
  ; "--use-lisa", Arg.Set use_lisa, "  use LISA as input language for test"
  ; "--dump-lisa", Arg.Set dump_lisa, "  print the LISA AST"
  ; "--dump-qbf", Arg.Set dump_qbf, "  print QBF query before executing"
  ; "--dump-query", Arg.Set dump_query, "  print query before executing"
  ; "--model", Arg.Set_string model_name, (Format.sprintf "  pick a model. Default is %s" !model_name)
  ; "--list-models", Arg.Unit (print_models decides), "  print list of models"
  ; "--list-enum-models", Arg.Unit (print_models enums), "  print list of models which support enumeration with -e"
  ; "--no-exec", Arg.Clear use_solver, "  skip running the solver. Useful with --dump-query option"
  (* This is a bit of a hack, when we see a '-' argument we need to
     turn the switch and then execute `run' right away.  The Arg
     module is a bit limitting for doing this nicely, sadly. *)
  ; "-",  Arg.Unit (fun x -> use_stdin:= true; (run "stdin")), "  read from stdin"
  ]

let () =
  Arg.parse cmd_spec run (sprintf "%s <infiles>" (Sys.executable_name))

