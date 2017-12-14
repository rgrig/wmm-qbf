(* TODO: Replace tabs with spaces. *)

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

type read = {
	id : event;
	from : address;
	value : int;
}

type write = {
	id : event;
	to : address;
	value : int;
}

type accumulator = {
	reads : event list ref;
	writes : write list ref;
	order : relation list ref;
	conflict : relation list ref;
	next_id : event ref;
}

let translate (program : LISAParser.ast) (values : values) : EventStructure =
	let init_event = 1 in
	let accumulator = {
		reads : ref [];
		writes : ref [];
		order : ref [];
		conflict : ref [];
		next_id : ref (init_event + 1);
	} in
	List.iter (fun instructions ->
		(* TODO: This amounts to the product of all the parallel threads. *)
		let instructions = Array.of_list instructions in
		translate_thread accumulator init_event instructions 0 Store.empty values in
	) program

let rec translate_thread
	(accumulator : accumulator)
	(parent : event)
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(progam_counter : int)
	(store : Store.t)
	(values : values)
: unit =
	if program_counter >= Array.len instructions then
		()
	else
		let line = Array.get instructions program_counter in
		match line with
		| Nop -> translate_thread accumulator parent instructions (program_counter + 1) store values
		| Label(_, instruction)
		| Instruction instruction -> translate_instruction
			accumulator
			parent
			instructions
			program_counter
			store
			values
			instruction
		| Macro _
		| Symbolic _ -> assert false

and translate_instruction
	(accumulator : accumulator)
	(parent : event)
	(instructions : LISAParser.BellBase.parsedInstruction array)
	(progam_counter : int)
	(store : Store.t)
	(values : values)
	(instruction : LISAParser.BellBase.parsedInstruction)
: unit =
	match instruction with
	| Pld(destination, source, labels) ->
		let destination = unwrap_reg destination in
		let source = translate_source source store in
		for value = values.minimum to values.maximum do
			let store = Store.update store destination value in
			ei ijeijjj ij
		doneddr_op_add
		TODO
		accumulator.order := (init_event, root) :: !accumulator.order

let translate_source
	(source : LISAParser.MetaConst.k LISAParser.BellBase.addr_op)
	(store : Store.t)
: address =
	match source with
	| Addr_op_atom(reg_or_addr) -> address_from_reg_or_addr reg_or_addr
	| Addr_op_add(reg_or_addr, reg_or_imm) ->
		let base = address_from_reg_or_addr reg_or_addr in
		let offset = match reg_or_imm with
		| Regi reg -> Store.lookup store (unwrap_reg reg)
		| Imm metaconst -> unwrap_metaconst metaconst
		in
		{ global=base.global; offset=base.offset + offset; }

let address_from_reg_or_addr
	(source : LISAParser.BellBase.reg_or_addr)
: address =
	match source with
	| Rega register -> assert false (* TODO: Does this mean copy the value or something else? *)
	(* TODO: Is this only used for read? *)
	| Abs(Concrete _) -> assert false (* Not allowed in read operations by parser. *)
	| Abs(Symbolic global)) -> { global=global; offset=0; }

let unwrap_reg (register : LISAParser.BellBase.reg) : int =
	match register with
	| GPRreg number -> number
	| Symbolic -> assert false

let unwrap_metaconst (value : LISAParser.MetaConst.k) : int =
	match value with
	| Int value -> value
	| Meta _ -> assert false

Read takes a register and an address operation, the base case for which is a register or a name.
The code seems to imply that the register is expected to hold an address, but without an address-of operator
how does that make sense?
