(* This module translates LISA program ASTs from LISAParser into event structures. *)

(* TODO: Replace tabs with spaces. *)
(* TODO: Sanity check. *)

(* Range of values to enumerate, includes minimum and maximum. *)
type values = {
	minimum : int;
	maximum : int;
}

(* A location in memory denoted by the name of a global variable and an array index (pointer offset). *)
(* Non-array variables always have a zero offset. *)
type address = {
	global : string;
	offset : int;
}

(* Information about a read event, used as intermediate storage until justification has been calculated. *)
type read {
	id : event;
	from : address;
	value : int;
}

(* Information about a write event, used as intermediate storage until justification has been calculated. *)
type write {
	id : event;
	to : address;
	value : int;
}

(* Intermediate event structure, gets translated to the final datatype before leaving this module. *)
type events {
	reads : read list;
	writes : write list;
	conflict : relation;
	order : relation;
}

let empty_events = {
	reads = [];
	writes = [];
	conflict = [];
	order = [];
}

(* Translate a program AST into an event structure, this is the entrypoint into the module. *)
(* `init` gives the initial values for global variables, letting the init event justify non-zero reads. *)
(* `program` gives the multi-threaded program AST from LISAParser. *)
(* `values` gives the range of numeric values to enumerate for read events. *)
let translate
	(init : LISAParser.MiscParser.state)
	(program : LISAParser.BellBase.parsedInstruction list list)
	(values : values)
: EventStructure.t =
	(* The init event is special, and always gets the first ID number. *)
	let init_id = 1;

	(* This boxed counter is used to make sure all events get unique ID numbers. *)
	let next_id = ref init_id + 1;

	(* An initial set of write records needs to be added because the init event sets global to values *)
	(* given in the initial state AST. *)
	let events = writes_from_init init in

	(* Translate each thread and compose the resulting event structures together. *)
	let events = List.fold_left (fun events instructions ->
		let instructions = Array.of_list instructions in
		let subtree = translate_instructions instructions 0 Store.empty values next_id in
		product events subtree
	) empty_events program in

	(* Add the order relations for the init event. *)
	let events = prefix_event events init_id in

	(* Generate the justifies relation. *)
	(* In this case, "justifies" pairs reads and writes of the same variable and value. *)
	let justifies = List.fold_left (fun accumulator read ->
		List.fold_left (fun accumulator write ->
			if write_justifies_read write read then (write.id, read.id) :: accumulator else accumulator
		) accumulator events.writes
	) [] events.reads in

	(* Convert from intermediate representation to final event structure. *)
	{
		events_number = 1 + (List.len events.reads) + (List.len events.writes);
		reads = List.map (fun read -> read.id) events.reads;
		justifies = justifies;
		conflicts = events.conflict;
		order = events.order;
	}

(* Translates a sequence of instructions form a single thread into an event structure. *)
(* `program_counter` gives the index of the instruction to interpret, allowing arbitrary branching. *)
(* `depth` tracks the number of instructions interpreted to detect infinite loops. *)
let rec translate_instructions
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(program_counter : int)
	(store : Store.t)
	(values : values)
	(next_id : event ref)
	(depth : int)
: events
	if program_counter >= Array.len instructions then
		(* Program finished. *)
		{ reads=[]; writes=[]; conflict=[]; order=[]; }
	else
		let line = Array.get instructions program_counter in
		let depth = depth + 1 in
		match line with
		| Nop -> translate_instructions instructions (program_counter + 1) store values next_id depth
		| Label(_, instruction)
		| Instruction instruction -> translate_instruction
			instructions
			program_counter
			store
			values
			next_id
			depth
			instruction
		| Macro _
		| Symbolic _ -> assert false

(* Returns the event structure for an instruction and all following instructions. *)
(* This awkward recursion pattern is here because branch instructions can arbitrarily change the program *)
(* counter, and nesting instruction decoding pattern matches would be very unpleasant. *)
and translate_instruction
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(program counter : int)
	(store : Store.t)
	(values : values)
	(next_id : event ref)
	(depth : int)
	(instruction : LISAParser.BellBase.parsedInstruction)
: events
	match instruction with
	| Pld(destination, source, labels) ->
		(* Spawn a set of conflicting read events, one for each value that could be read. *)
		let destination = unwrap_reg destination in
		let source = address_from_addr_op store source in
		let program_counter = program_counter + 1 in
		let events = ref empty_events in
		for value = values.minimum to values.maximum do
			let store = Store.update store destination value in
			let subtree = translate_instructions instructions program_counter store values next_id depth in
			let subtree = prefix_read subtree next_id source value in
			events := sum events subtree
		done
		events
	| Pst(destination, source, labels) ->
		(* Spawn a write event. *)
		let destination = address_from_addr_op store destination in
		let value = value_from_reg_or_imm store source in
		let program_counter = program_counter + 1 in
		let subtree = translate_instructions instructions program_counter store values next_id depth in
		prefix_write subtree next_id destination value
	| Pbranch(Some(test), destination, labels) ->
		(* Conditional jump, doesn't create any events directly. *)
		let test = unwrap_reg test in
		let value = Store.lookup store test in
		(* TODO: What means true? *)
		let next = if value != 0 then find_label instructions destination else program_counter + 1 in
		translate_instructions instructions next store values next_id depth
	| Pbranch(None, destination, labels) ->
		(* Unconditional jump, doesn't create any events directly. *)
		let next = find_label instructions destination in
		translate_instructions instructions next store values next_id depth
	| _ -> assert false (* TODO: Other instructions. *)

(* Returns an event set with writes that attribute all the values in `init` to `event_id`. *)
let writes_from_init (init : LISAParser.MiscParser.state) (event_id : event) : events =
	let writes = List.fold_left (fun accumulator init ->
		(* TODO: Assumes that run_type isn't relevant. *)
		let (location, (run_type, value)) = init in

		let value = match value with
		| Concrete value -> value
		| Symbolic _ -> assert false (* Meaningless. *)

		let address = match location with
		| Location_reg _
		| Location_sreg _ -> assert false (* TODO: Allow writes to registers? *)
		| Location_global(Symbolic name) -> { global = name; offset = 0; }
		(* TODO: It doesn't look like the parser generates this in init. *)
		(* TODO: This means that some of the JCTC LISA tests are broken because they use arrays in init. *)
		| Location_deref(Symbolic name, offset) -> (* { global = name; offset = offset; } *) assert false
		| Location_global(Concrete _)
		| Location_deref(Concrete _, _) -> assert false (* Meaningless. *)
		{ id = event_id; to = address; value = value; } :: accumulator
	) [] init in
	{
		reads = [];
		writes = writes;
		conflict = [];
		order = [];
	}

(* Return true if a write has the same address and value as a read. *)
let write_justifies_read (write : write) (read : read) : bool =
	read.address.global = write.address.global &&
	read.address.offset = write.address.offset &&
	read.value = write.value

(* Add a read event before the given events. *)
let prefix_read (events : events) (next_id : event ref) (from : address) (value : int) : events =
	let id = !next_id in
	next_id := !next_id + 1;
	prefix_event {
		reads = { id = id; from = from; value = value; } :: events.reads;
		writes = events.writes;
		conflict = events.conflict;
		order = events.order;
	} id

(* Add a write event before the given events. *)
let prefix_write (events : events) (next_id : event ref) (to : address) (value : int) : events =
	let id = !next_id in
	next_id := !next_id + 1;
	prefix_event {
		reads = events.reads;
		writes = { id = id; to = to; value = value; } :: events.writes;
		conflict = events.conflict;
		order = events.order;
	} id

(* Add an event before the given event set, without updating lists of reads and writes. *)
(* TODO: Avoid generating lots of unused orders. *)
let prefix_event (events : events) (event : event) : events =
	(* TODO: Check I understood the notation properly. *)
	(* This should be equivalent to "≤0 ∪ ({⊥} × E)" but without (⊥, ⊥). *)
	let read_order = List.map (fun read -> (event, read.id)) events.reads in
	let write_order = List.map (fun write -> (event, write.id)) events.writes in
	{
		reads = events.reads;
		writes = events.writes;
		conflict = events.conflict;
		order = events.order @ read_order @ write_order;
	}

(* Sum event trees, assuming that root_a and root_b are the top of each tree. *)
(* Only adds a conflict between the root events to save generating lots of unused conflicts. *)
(* Assumes that the two trees use separate sets of event IDs. *)
let sum (a : events) (b : events) : events =
	{
		(* "E1 ∪ E2". *)
		reads = a.reads @ b.reads;
		writes = a.writes @ b.writes;
		(* "#1 ∪ #2 ∪ (E1 × E2) ∪ (E2 × E1)", except the redundant conflicts are elided, see above. *)
		conflict = (root_a, root_b) :: (root_b, root_a) :: (a.conflict @ b.conflict);
		(* "≤1 ∪ ≤2". *)
		order: a.order @ b.order;
	}

(* Cross event trees. *)
(* Assumes that the two trees use separate sets of event IDs. *)
let product (a : events) (b : events) : events =
	{
		(* "E1 ∪ E2". *)
		reads = a.reads @ b.reads;
		writes = a.writes @ b.writes;
		(* "#1 ∪ #2". *)
		conflict = a.conflict @ b.conflict;
		(* "≤1 ∪ ≤2". *)
		order: a.order @ b.order;
	}

(* Return the index of the first instruction with the given label. *)
let find_label (instructions : LISAParser.BellBase.parsedInstruction array) (label : string) : int =
	let rec search (instructions : LISAParser.BellBase.parsedInstruction array) (index : int) : int =
		match Array.get instructions index with
		| Label(test, _) where test = label -> index
		| Nop
		| Label _
		| Instruction _ -> search instructions (index + 1)
		| Macro _
		| Symbolic _ -> assert false
	(* Search until an index out of range happends. *)
	try search instructions 0
	with Invalid_argument _ -> raise Invalid_argument "label not found: " ^ label

let address_from_addr_op
	(store : Store.t)
	(value : LISAParser.MetaConst.k LISAParser.BellBase.addr_op)
: address =
	match source with
	| Addr_op_atom(reg_or_addr) -> address_from_reg_or_addr reg_or_addr
	| Addr_op_add(reg_or_addr, reg_or_imm) ->
		let base = address_from_reg_or_addr reg_or_addr in
		let offset = value_from_reg_or_imm store reg_or_imm in
		{ global = base.global; offset = base.offset + offset; }

let address_from_reg_or_addr
	(source : LISAParser.BellBase.reg_or_addr)
: address =
	match source with
	| Rega register -> assert false (* TODO: What does this mean? *)
	| Abs(Concrete _) -> assert false (* Not allowed by parser. *)
	| Abs(Symbolic global)) -> { global = global; offset = 0; }

let value_from_reg_or_imm
	(store : Store.t)
	(value : LISAParser.MetaConst.k LISAParser.BellBase.reg_or_imm)
: int =
	match value with
	| Regi reg -> Store.lookup store (unwrap_reg reg)
	| Imm metaconst -> unwrap_metaconst metaconst

let unwrap_reg (register : LISAParser.BellBase.reg) : int =
	match register with
	| GPRreg number -> number
	| Symbolic -> assert false

let unwrap_metaconst (value : LISAParser.MetaConst.k) : int =
	match value with
	| Int value -> value
	| Meta _ -> assert false
