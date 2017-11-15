open Lexing

module L = BellLexer.Make(LexUtils.Default)
(* TODO: Currently parsing only the LISA part of the file, add splitting a state parsing. *)
let lexbuf = from_channel (open_in "test.litmus")
let titles, instructions, misc = LISAParser.main L.token lexbuf
let pp_int f = Format.fprintf f "%d"

let _ = List.iteri (fun line instructions ->
  let by_process = List.combine titles instructions in
  List.iter (fun (process, instruction) ->
    Format.printf "Process %d: %a\n" process BellBase.pp_parsedPseudo instruction
  ) by_process
) instructions
