open Printf
module U = Util
module T = ModelParser
module L = ModelLexer.Make(LexUtils.Default)
             
let use_stdin = ref false

let run filename =
  let file_chan = match !use_stdin with
      true -> stdin
    | false -> open_in filename
  in
  let _ = U.parse filename file_chan T.main L.token T.Error in
  ()

let cmd_spec =
  Arg.align [
      "-",  Arg.Unit (fun x -> use_stdin:= true; (run "stdin")), "  read from stdin"
  ]

let () =
  Arg.parse cmd_spec run (sprintf "%s <infiles>" (Sys.executable_name))

