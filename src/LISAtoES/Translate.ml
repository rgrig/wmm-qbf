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

type read {
	id : event;
	from : address;
	value : int;
}

type write {
	id : event;
	to : address;
	value : int;
}

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

let translate
	(init : LISAParser.TODO)
	(program : LISAParser.BellBase.parsedInstruction list list)
	(values : values)
: EventStructure.t =
	let store = (* TODO: From init. *)
	let init_id = 1;
	let next_id = ref init_id + 1;
	let events = List.fold_left (fun events instructions ->
		let instructions = Array.of_list instructions in
		let subtree = translate_instructions instructions 0 store values next_id in
		product events subtree
	) empty_events program in
	let events = prefix_event events init_id in
	let justifies = List.fold_left (fun accumulator read ->
		List.fold_left (fun write ->
			if write_justifies_read write read then (write.id, read.id) :: accumulator else accumulator
		) accumulator events.writes
	) [] events.reads in
	{
		events_number = 1 + (List.len events.reads) + (List.len events.writes);
		reads = List.map (fun read -> read.id) events.reads;
		justifies = TODO;
		conflicts = events.conflict;
		order = events.order;
	}

(* TODO: Sanity check. *)
let rec translate_instructions
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(program counter : int)
	(store : Store.t)
	(values : values)
	(next_id : event ref)
: events
	if program_counter >= Array.len instructions then
		{ reads=[]; writes=[]; conflict=[]; order=[]; }
	else
		let line = Array.get instructions program_counter in
		match line with
		| Nop -> translate_instructions instructions (program_counter + 1) store values next_id
		| Label(_, instruction)
		| Instruction instruction -> translate_instruction
			instructions
			program_counter
			store
			values
			next_id
			instruction
		| Macro _
		| Symbolic _ -> assert false

and translate_instruction
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(program counter : int)
	(store : Store.t)
	(values : values)
	(next_id : event ref)
	(instruction : LISAParser.BellBase.parsedInstruction)
: events
	match instruction with
	| Pld(destination, source, labels) ->
		let destination = unwrap_reg destination in
		let source = address_from_addr_op store source in
		let program_counter = program_counter + 1 in
		let events = ref empty_events in
		for value = values.minimum to values.maximum do
			let store = Store.update store destination value in
			let subtree = translate_instructions instructions program_counter store values next_id in
			let subtree = prefix_read subtree next_id source value in
			events := sum events subtree
		done
		events
	| Pst(destination, source, labels) ->
		let destination = address_from_addr_op store destination in
		let value = value_from_reg_or_imm store source in
		let program_counter = program_counter + 1 in
		let subtree = translate_instructions instructions program_counter store values next_id in
		prefix_write subtree next_id destination value
	| Pbranch(Some(test), destination, labels) ->
		let test = unwrap_reg test in
		let value = Store.lookup store test in
		(* TODO: What means true? *)
		let next = if value != 0 then find_label instructions destination else program_counter + 1 in
		translate_instructions instructions next store values next_id
	| Pbranch(None, destination, labels) ->
		let next = find_label instructions destination in
		translate_instructions instructions next store values next_id
	| _ -> assert false (* TODO: Other instructions. *)

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
	} id in

(* Add a write event before the given events. *)
let prefix_write (events : events) (next_id : event ref) (to : address) (value : int) : events =
	let id = !next_id in
	next_id := !next_id + 1;
	prefix_event {
		reads = events.reads;
		writes = { id = id; to = to; value = value; } :: events.writes;
		conflict = events.conflict;
		order = events.order;
	} id in

(* Add an events before the given events, without updating lists of reads and writes. *)
(* TODO: Avoid generating lots of unused conflicts. *)
let prefix_event (events : events) (event : event) : events =
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
		reads = a.reads @ b.reads;
		writes = a.writes @ b.writes;
		conflict = (root_a, root_b) :: (root_b, root_a) :: (a.conflict @ b.conflict);
		order: a.order @ b.order;
	}

(* Cross event trees. *)
(* Assumes that the two trees use separate sets of event IDs. *)
let product (a : events) (b : events) : events =
	{
		reads = a.reads @ b.reads;
		writes = a.writes @ b.writes;
		conflict = a.conflict @ b.conflict;
		order: a.order @ b.order;
	}

(* Return the index of the first instruction with the given label. *)
let find_label (instructions : LISAParser.BellBase.parsedInstruction array) (label : string) : int =
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

let address_from_addr_op
	(store : Store.t)
	(value : LISAParser.MetaConst.k LISAParser.BellBase.addr_op)
: address =
	match source with
	| Addr_op_atom(reg_or_addr) -> address_from_reg_or_addr reg_or_addr
	| Addr_op_add(reg_or_addr, reg_or_imm) ->
		let base = address_from_reg_or_addr reg_or_addr in
		let offset = value_from_reg_or_imm reg_or_imm in
		{ global=base.global; offset=base.offset + offset; }

let address_from_reg_or_addr
	(source : LISAParser.BellBase.reg_or_addr)
: address =
	match source with
	| Rega register -> assert false (* TODO: What does this mean? *)
	| Abs(Concrete _) -> assert false (* Not allowed by parser. *)
	| Abs(Symbolic global)) -> { global=global; offset=0; }

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
