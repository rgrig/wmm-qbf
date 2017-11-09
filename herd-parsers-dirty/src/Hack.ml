open Lexing

module L = BellLexer.Make(LexUtils.Default)
let lexbuf = from_channel (open_in "test.litmus")
let titles, instructions, misc = LISAParser.main L.token lexbuf
let pp_int f = Format.fprintf f "%d"
             
(* insturctions : BellBase.parsedPseudo list list *)             
(* let _ = Format.printf "%a" (BellBase.pp_kpseudo (BellBase.pp_kinstruction pp_int)) instructions *)

let _ = List.iter (List.iter (Format.printf "%a\n" BellBase.pp_parsedPseudo)) instructions
             
let _ = List.iter (fun n -> Printf.printf "%d\n" n) titles
