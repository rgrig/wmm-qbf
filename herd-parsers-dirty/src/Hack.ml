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

module U = LexUtils.Make(LexUtils.Default)

(* Parse init. *)
let _ = print_range init_range
module STATE_LEXER = StateLexer.Make(LexUtils.Default)
let lexbuf = U.from_section init_range (open_in filename)
let init = StateParser.init STATE_LEXER.token lexbuf

(* Parse the LISA program section of the input. *)
let _ = print_range program_range
module LISA_LEXER = BellLexer.Make(LexUtils.Default)
let lexbuf = U.from_section program_range (open_in filename)
let titles, instructions, misc = LISAParser.main LISA_LEXER.token lexbuf

(* Parse condition. *)
let _ = print_range condition_range
let lexbuf = U.from_section condition_range (open_in filename)
let condition = StateParser.constraints STATE_LEXER.token lexbuf

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

(* Print inital state. *)
let _ = Format.printf "Init: %a\n" MiscParser.pp_state init

(* Print the program AST. *)
let _ = List.iteri (fun line instructions ->
  let by_process = List.combine titles instructions in
  List.iter (fun (process, instruction) ->
    Format.printf "Process %d: %a\n" process BellBase.pp_parsedPseudo instruction
  ) by_process
) instructions

(* Print condition. *)
let pp_locations (f : Format.formatter) (locations : (MiscParser.location * MiscParser.run_type) list) : unit =
  List.iter (fun (location, run_type) ->
    Format.fprintf f "%s %a" (MiscParser.dump_location location) MiscParser.pp_run_type run_type)
	locations
let show_atom (atom : (MiscParser.location, MiscParser.maybev) ConstrGen.atom) : string =
  match atom with
  | LL (a, b) -> Format.sprintf "LL %s, %s" (MiscParser.dump_location a) (MiscParser.dump_location b)
  | LV (location, value) -> Format.sprintf "LV %s, %s" (MiscParser.dump_location location) (SymbConstant.show_v value)
let pp_prop_option (f : Format.formatter) (value : MiscParser.prop option) : unit =
  match value with
  | Some prop -> Format.fprintf f "Some(%s)" (ConstrGen.prop_to_string show_atom prop)
  | None -> Format.fprintf f "None"
let pp_kinds (f : Format.formatter) (value : (string * MiscParser.quantifier) list) : unit =
  List.iter (fun (name, quantifier) -> Format.fprintf f "name,%s;" (ConstrGen.pp_kind quantifier)) value
let (locations, filter, final, kinds) = condition
let _ = Format.printf "Condition: location = %a, filter = %a, final = %s, kinds = %a\n"
  pp_locations locations
  pp_prop_option filter
  (ConstrGen.constraints_to_string show_atom final)
  pp_kinds kinds
