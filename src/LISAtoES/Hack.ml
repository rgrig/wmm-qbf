(* TODO: Replace tabs with spaces. *)

type instructions = LISAParser.BellBase.parsedPseudo array
type instruction = LISAParser.BellBase.parsedInstruction
(* Range of values to enumerate, includes minimum and maximum. *)
type values = {
	minimum : int;
	maximum : int;
}
(* A write event and what it wrote. *)
type write_info = {
	event : event,
	global : string,
	value : int,
}
(* Boxed list of write events and what they wrote. *)
(* Used to accumulate data that allows justification relations to be built. *)
type justifications = write_info list ref

let translate (init : TODO) (program : TODO) (values : values) : EventStructure =
	(* TODO: Translate threads and product them, calculate justifications. *)

(* TODO: Accumulate write mappings for justification. *)
let rec translate_thread
	(instructions : instructions)
	(program_counter : int)
	(store : Store.t)
	(justifications : () list ref)
	(values : values)
	(depth : int)
: EventStructure =
	if program_counter >= Array.len instructions then
		EventStructure.empty
	else
		let line = Array.get instructions program_counter in
		match line with
		| Nop -> translate_thread instructions (program_counter + 1) store values depth
		| Label(_, instruction)
		| Instruction instruction -> translate_instruction
			instructions
			program_counter
			store
			values
			(depth + 1)
			instruction
		| Macro _
		| Symbolic _ -> assert false

and translate_instruction
	(instructions : instructions)
	(program_counter : int)
	(store : Store.t)
	(values : values)
	(depth : int)
	(instruction : instruction)
: EventStructure =
	match instruction with
	| Pld(destination, source, labels) ->
		let sum_of_reads = fun events value ->
			let store = Store.update store destination value in
			let child = translate_thread instructions (program_counter + 1) store values depth in
			let subtree = prefix true child in
			sum events subtree
		in
		fold_values sum_of_reads EventStructure.empty values.minumum values.maximum
	| Pst(destination, source, labels) ->
		assert value >= values.minimum
		assert value <= values.maximum
		let value = Store.lookup source in
		let child = translate_thread instructions (program_counter + 1) store values depth in
		(* TODO: Accumulate justification sources. *)
		prefix false child
	| Pbranch(Some(test), destination, labels) ->
		let value = Store.lookup test in
		(* TODO: Assumes that branch checks for non-zero values. *)
		let next = if value > 0 then
			find_label instructions destination in
		else
			program_counter + 1
		in
		translate_thread instructions next store values depth
	| Pbranch(None, destination, labels) ->
		let next = find_label instructions destination in
		translate_thread instructions next store values depth
	| _ -> assert false (* TODO: Other instructions. *)

(* Return the index of the first instruction with the given label. *)
let find_label (instructions : instructions) (label : string) : int =
	let rec search (instructions : instructions) (index : int) : int =
		let index = index + 1 in
		match Array.get instructions index with
		| Nop -> search instructions index
		| Label(test, _) where test = label -> index
		| Label _ -> search instructions index
		| Instruction _ -> search instructions index
		| Macro _ -> assert false
		| Symbolic _ -> assert false
	try search instructions 0
	with Invalid_argument _ -> raise Invalid_argument "label not found: " ^ label

(* Pretend that we have a list of all values and that we called List.fold_left on it. *)
(* Includes minimum and maximum. *)
(* TODO: This might fold the wrong way, but I'm not actually sure which way fold_left goes. *)
let rec fold_values (function : 'a -> int -> 'a) (init : 'a) (minimum : int) (maximum : int) : 'a =
	if minimum > maximum then
		init
	else
		let next = function init minimum in
		fold_values function next (minimum + 1) maximum

(* Assuming that root_a and root_b are read events at the top of each tree, sum the trees. *)
(* Only adds a conflict between the root events because all the others are implied. *)
let sum (a : EventStructure.t) (root_a : int) (b : EventStructure.t) (root_b : int) : EventStructure.t =
	{
		events_number = a.events_number + b.events_number;
		reads: List.fold_left (fun reads add -> (add + a.events_number) :: reads) a.reads b.reads;
		justifies: []; (* Built afterward. *)
		conflicts: (root_a, root_b) :: (root_b, root_a) :: (List.concat a.conflicts b.conflicts);
		order: List.concat a.order b.order;
	}

let product (a : EventStructure.t) (b : EventStructure.t) : EventStructure.t =
	{
		events_number = a.events_number + b.events_number;
		reads: List.fold_left (fun reads add -> (add + a.events_number) :: reads) a.reads b.reads;
		justifies: []; (* Built afterward. *)
		conflicts: List.concat a.conflicts b.conflicts;
		order: List.concat a.order b.order;
	}

(* Prefix a tree with a single read or write event. *)
let prefix (read : bool) (events : EventStructure.t) : EventStructure.t =
	let new_event = events.events_number + 1 in
	{
		events_number: new_event;
		reads: if read then new_event :: events.reads else events.reads;
		justifies: []; (* Built afterward. *)
		conflicts: events.conflicts;
		order: fold_values
			(fun order event -> (new_event, event) :: order)
			events.order
			1
			events.events_number
		;
	}
