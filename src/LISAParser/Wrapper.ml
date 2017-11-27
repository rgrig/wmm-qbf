open Splitter
open ConstrGen

(* The types below wrap the parser's return types so the caller only has to worry about one parser module. *)
(* Initial state of the virtual machine. *)
type init = MiscParser.state
(* A list of program threads, each thread is a list of instructions. *)
type ast = BellBase.parsedPseudo list list
(* Constraints on result. *)
(* TODO: What does any of this mean? *)
type constraints = (MiscParser.location * MiscParser.run_type) list *
  MiscParser.prop option *
  MiscParser.constr *
  (string * MiscParser.quantifier) list

module SPLITTER = Splitter.Make(Splitter.Default)
module LEXUTILS = LexUtils.Make(LexUtils.Default)
module STATE_LEXER = StateLexer.Make(LexUtils.Default)
module LISA_LEXER = BellLexer.Make(LexUtils.Default)

(* Read a litmus test written in LISA fromt he given filename. *)
(* Returns the initial state of the virtual machine, a list of ids for the proces threads, *)
(* a list of single program threads (a list of instructions for each process), *)
(* and the constraint on the result. *)
let load_litmus (filename : string) : init * int list * ast * constraints =
  (* Find the sections of the file and check it's the right architecture. *)
  let split_result = SPLITTER.split "TODO: Name" (open_in filename) in
  let _ = assert split_result.is_lisa in
  let (init_range, program_range, condition_range, _) = split_result.locs in

  (* Parse initial state. *)
  let lexbuf = LEXUTILS.from_section init_range (open_in filename) in
  let init = StateParser.init STATE_LEXER.token lexbuf in

  (* Parse LISA program. *)
  let lexbuf = LEXUTILS.from_section program_range (open_in filename) in
  let titles, instructions, _ = LISAParser.main LISA_LEXER.token lexbuf in

  (* Transpose rows of instructions into columns of instructions. *)
  let processes = Misc.transpose instructions in

  (* Parse final condition. *)
  let lexbuf = LEXUTILS.from_section condition_range (open_in filename) in
  let condition = StateParser.constraints STATE_LEXER.token lexbuf in

  init, titles, processes, condition

(* Dump debugging representation of a loaded litmus test. *)
let print_litmus (litmus : init * int list * ast * constraints) : unit =
  Format.printf "\nDumping litmus test...\n\n";

  let init, titles, processes, condition = litmus in

  (* Print inital state. *)
  Format.printf "Init: %a\n" MiscParser.pp_state init;

  (* Print the program AST. *)
  List.iter (fun (title, instructions) ->
    Format.printf "Process %d:\n" title;
    List.iter (fun instruction -> Format.printf "\t%a\n" BellBase.pp_parsedPseudo instruction) instructions
  ) (List.combine titles processes);

  (* Print condition. *)
  let pp_locations (f : Format.formatter) (locations : (MiscParser.location * MiscParser.run_type) list) : unit =
    List.iter (fun (location, run_type) ->
      Format.fprintf f "%s %a" (MiscParser.dump_location location) MiscParser.pp_run_type run_type)
      locations
  in
  let show_atom (atom : (MiscParser.location, MiscParser.maybev) ConstrGen.atom) : string =
    match atom with
    | LL (a, b) -> Format.sprintf "LL %s, %s" (MiscParser.dump_location a) (MiscParser.dump_location b)
    | LV (location, value) -> Format.sprintf "LV %s, %s" (MiscParser.dump_location location) (SymbConstant.show_v value)
  in
  let pp_prop_option (f : Format.formatter) (value : MiscParser.prop option) : unit =
    match value with
    | Some prop -> Format.fprintf f "Some(%s)" (ConstrGen.prop_to_string show_atom prop)
    | None -> Format.fprintf f "None"
  in
  let pp_kinds (f : Format.formatter) (value : (string * MiscParser.quantifier) list) : unit =
    List.iter (fun (name, quantifier) -> Format.fprintf f "name,%s;" (ConstrGen.pp_kind quantifier)) value
  in
  let (locations, filter, final, kinds) = condition in
  Format.printf "Condition: location = %a, filter = %a, final = %s, kinds = %a\n"
    pp_locations locations
    pp_prop_option filter
    (ConstrGen.constraints_to_string show_atom final)
    pp_kinds kinds
