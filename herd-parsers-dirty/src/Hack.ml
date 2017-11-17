open Lexing
open LexUtils

let filename = "test.litmus"

(* Prints a range returned by Splitter. *)
let print_range (range : Pos.pos2) : unit =
  let (start, stop) = range in
  Format.printf "%d .. %d\n" start.pos_cnum stop.pos_cnum

(* Find the sections of the file and check it's the right architecture. *)
module S = Splitter.Make(Splitter.Default)
let split_result = S.split "TODO: Name?" (open_in filename)
let _ = assert split_result.is_lisa
let (init_range, program_range, condition_range, _) = split_result.locs

(* Parse the LISA program section of the input. *)
let _ = print_range program_range
module L = BellLexer.Make(LexUtils.Default)
module U = LexUtils.Make(LexUtils.Default)
let lexbuf = U.from_section program_range (open_in filename)
let titles, instructions, misc = LISAParser.main L.token lexbuf
(* TODO: Parse init. *)
(* TODO: Parse condition. *)

(* TODO
(*
  Transpose the instructions:
  a list of rows -> a list of columns (each being the program
  for a given processor
*)
    let transpose procs prog =
      try
	let prog = Misc.transpose prog in
	List.combine procs prog 
      with
      |  Misc.TransposeFailure | Invalid_argument _ ->
	  Warn.fatal "mismatch in instruction lines"
*)

(* Print the program AST. *)
let _ = List.iteri (fun line instructions ->
  let by_process = List.combine titles instructions in
  List.iter (fun (process, instruction) ->
    Format.printf "Process %d: %a\n" process BellBase.pp_parsedPseudo instruction
  ) by_process
) instructions
