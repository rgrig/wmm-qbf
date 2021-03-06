exception BadInput of string

type state = MiscParser.state
type program = BellBase.parsedPseudo list list

(* TODO: What does any of this mean? *)
type constraints = (MiscParser.location * MiscParser.run_type) list *
  MiscParser.prop option *
  MiscParser.constr *
  (string * MiscParser.quantifier) list

type litmus =
  { init : state
  ; threads : int list
  ; program : program
  ; final : constraints }

module SPLITTER = Splitter.Make(Splitter.Default)
module LEXUTILS = LexUtils.Make(LexUtils.Default)
module STATE_LEXER = StateLexer.Make(LexUtils.Default)
module LISA_LEXER = BellLexer.Make(LexUtils.Default)

(* Return a file's contents as a string. *)
let read_to_eof (from : in_channel) : string =
  let rec do_read (accumulator : Buffer.t) (buffer : bytes) (from : in_channel) : unit =
    let bytes_read = input from buffer 0 (Bytes.length buffer) in
    if bytes_read > 0 then begin
      Buffer.add_subbytes accumulator buffer 0 bytes_read;
	  do_read accumulator buffer from
	end
  in
  let accumulator = Buffer.create 16 in
  let buffer = Bytes.create 256 in
  do_read accumulator buffer from;
  Buffer.contents accumulator

(* Read a litmus test written in LISA from a string. *)
(* Returns the initial state of the virtual machine, a list of ids for the proces threads, *)
(* a list of single program threads (a list of instructions for each process), *)
(* and the constraint on the result. *)
let load_litmus data =
  (* Find the sections of the file and check it's the right architecture. *)
  (* TODO: "input" should be the name of the input file. *)
  let split_result = SPLITTER.split "input" data in
  if not Splitter.(split_result.is_lisa) then raise (BadInput "Missing LISA header");
  let (init_range, program_range, condition_range, _) =
    Splitter.(split_result.locs) in

  (* Parse initial state. *)
  let lexbuf = LEXUTILS.from_section_string init_range data in
  let init = StateParser.init STATE_LEXER.token lexbuf in

  (* Parse LISA program. *)
  let lexbuf = LEXUTILS.from_section_string program_range data in
  let titles, instructions, _ = LISAParser.main LISA_LEXER.token lexbuf in

  (* Transpose rows of instructions into columns of instructions. *)
  let processes = Misc.transpose instructions in

  (* Parse final condition. *)
  let lexbuf = LEXUTILS.from_section_string condition_range data in
  let condition = StateParser.constraints STATE_LEXER.token lexbuf in

  { init; threads = titles; program = processes; final = condition }

(* Dump debugging representation of a loaded litmus test. *)
let print_litmus litmus =
  Format.printf "\nDumping litmus test...\n\n";

  (* Print inital state. *)
  Format.printf "Init: %a\n" MiscParser.pp_state litmus.init;

  (* Print the program AST. *)
  List.iter (fun (title, instructions) ->
    Format.printf "Process %d:\n" title;
    List.iter (fun instruction -> Format.printf "\t%a\n" BellBase.pp_parsedPseudo instruction) instructions
  ) (List.combine litmus.threads litmus.program);

  (* Print condition. *)
  let pp_locations (f : Format.formatter) (locations : (MiscParser.location * MiscParser.run_type) list) : unit =
    List.iter (fun (location, run_type) ->
      Format.fprintf f "%s %a" (MiscParser.dump_location location) MiscParser.pp_run_type run_type)
      locations
  in
  let show_atom (atom : (MiscParser.location, MiscParser.maybev) ConstrGen.atom) : string =
    match atom with
    | ConstrGen.LL (a, b) ->
        Format.sprintf "LL %s, %s" (MiscParser.dump_location a) (MiscParser.dump_location b)
    | ConstrGen.LV (location, value) ->
        Format.sprintf "LV %s, %s" (MiscParser.dump_location location) (SymbConstant.show_v value)
  in
  let pp_prop_option (f : Format.formatter) (value : MiscParser.prop option) : unit =
    match value with
    | Some prop -> Format.fprintf f "Some(%s)" (ConstrGen.prop_to_string show_atom prop)
    | None -> Format.fprintf f "None"
  in
  let pp_kinds (f : Format.formatter) (value : (string * MiscParser.quantifier) list) : unit =
    List.iter (fun (name, quantifier) -> Format.fprintf f "name,%s;" (ConstrGen.pp_kind quantifier)) value
  in
  let (locations, filter, final, kinds) = litmus.final in
  Format.printf "Condition: location = %a, filter = %a, final = %s, kinds = %a\n"
    pp_locations locations
    pp_prop_option filter
    (ConstrGen.constraints_to_string show_atom final)
    pp_kinds kinds
