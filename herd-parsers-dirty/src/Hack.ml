open Lexing

module L = BellLexer.Make(LexUtils.Default)
let lexbuf = from_channel (open_in "test.litmus")
let titles, instructions, misc = LISAParser.main L.token lexbuf
let _ = List.iter (fun n -> Printf.printf "%d\n" n) titles
