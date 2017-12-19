(* This module translates LISA program ASTs from LISAParser into event structures. *)

open EventStructure
open MiscParser
open Constant
open BellBase
open MetaConst

exception LISAtoESException of string;;

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
type read = {
  id : event;
  from : address;
  value : int;
}

(* Information about a write event, used as intermediate storage until justification has been calculated. *)
type write = {
  id : event;
  into : address;
  value : int;
}

(* Intermediate event structure, gets translated to the final datatype before leaving this module. *)
type events = {
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

let unwrap_reg (register : BellBase.reg) : int =
  match register with
  | GPRreg number -> number
  | Symbolic_reg _ -> raise (LISAtoESException "Symbolic registers not supported")

let unwrap_metaconst (value : MetaConst.k) : int =
  match value with
  | Int value -> value
  | Meta _ -> raise (LISAtoESException "Symbolic constants not supported")

let value_from_reg_or_imm
  (store : Store.t)
  (value : MetaConst.k BellBase.reg_or_imm)
: int =
  match value with
  | Regi reg -> Store.lookup store (unwrap_reg reg)
  | Imm metaconst -> unwrap_metaconst metaconst

let address_from_reg_or_addr
  (source : BellBase.reg_or_addr)
: address =
  match source with
  | Rega register -> raise (LISAtoESException "Can't convert register to address")
  | Abs(Concrete _) -> assert false (* Not allowed by parser. *)
  | Abs(Symbolic global) -> { global = global; offset = 0; }

let address_from_addr_op
  (store : Store.t)
  (value : MetaConst.k BellBase.addr_op)
: address =
  match value with
  | Addr_op_atom(reg_or_addr) -> address_from_reg_or_addr reg_or_addr
  | Addr_op_add(reg_or_addr, reg_or_imm) ->
    let base = address_from_reg_or_addr reg_or_addr in
    let offset = value_from_reg_or_imm store reg_or_imm in
    { global = base.global; offset = base.offset + offset; }

let value_from_imm_or_addr_or_reg (store : Store.t) (from : MetaConst.k imm_or_addr_or_reg) : int =
  match from with
  | IAR_roa(Rega reg) -> Store.lookup store (unwrap_reg reg)
  | IAR_roa(Abs _) -> raise (LISAtoESException "mov from address not supported.")
  | IAR_imm value -> unwrap_metaconst value

let do_arithmetic (operation : op_t) (a : int) (b : int) (values : values) : int =
  Printf.printf "TODO HACK Operation on %d and %d\n" a b;

  let out = match operation with
  | Add -> a + b
  | Xor -> a lxor b
  | And -> a land b
  | Eq -> if a = b then 1 else 0
  | Neq -> if a = b then 0 else 1
  in
  if out < values.minimum || out > values.maximum then
    raise (LISAtoESException "Arithmetic result out of range")
  else
    out

let rec instruction_from_pseudo_label (pseudo : BellBase.parsedPseudo) : BellBase.parsedInstruction option =
  match pseudo with
  | Label(_, Instruction instruction) -> Some instruction
  | Label(_, next_label) -> instruction_from_pseudo_label next_label
  | Nop
  | Instruction _
  | Macro _
  | Symbolic _ -> None

(* Sum event trees, assuming that root_a and root_b are the top of each tree. *)
(* Only adds a conflict between the root events to save generating lots of unused conflicts. *)
(* Assumes that the two trees use separate sets of event IDs. *)
let sum (a : events) (b : events) (root_a : event) (root_b : event) : events =
  {
    (* "E1 ∪ E2". *)
    reads = a.reads @ b.reads;
    writes = a.writes @ b.writes;
    (* "#1 ∪ #2 ∪ (E1 × E2) ∪ (E2 × E1)", except the redundant conflicts are elided, see above. *)
    conflict = (root_a, root_b) :: (a.conflict @ b.conflict);
    (* "≤1 ∪ ≤2". *)
    order =  a.order @ b.order;
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
    order =  a.order @ b.order;
  }

(* Add an event before the given event set, without updating lists of reads and writes. *)
(* TODO: Avoid generating lots of unused orders. *)
let prefix_event (events : events) (event : event) : events =
  (* TODO: Check I understood the notation properly. *)
  (* This should be equivalent to "≤0 ∪ ({⊥} × E)" but without (⊥, ⊥). *)
  (* TODO: Why do I have to specify the types here to get this to compile? *)
  (* It isn't because the variables are named the same as the types, I've tried `r` and `w`. *)
  let read_order = List.map (fun (read : read) -> (event, read.id)) events.reads in
  let write_order = List.map (fun (write : write) -> (event, write.id)) events.writes in
  {
    reads = events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order @ read_order @ write_order;
  }

(* Add a read event before the given events and return the result and the allocated event id. *)
let prefix_read (events : events) (next_id : event ref) (from : address) (value : int) : events * event =
  let id = !next_id in
  next_id := !next_id + 1;
  let events = prefix_event events id in
  let events = {
    reads = { id = id; from = from; value = value; } :: events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order;
  } in
  events, id

(* Add a write event before the given events. *)
let prefix_write (events : events) (next_id : event ref) (into : address) (value : int) : events =
  let id = !next_id in
  next_id := !next_id + 1;
  let events = prefix_event events id in
  {
    reads = events.reads;
    writes = { id = id; into = into; value = value; } :: events.writes;
    conflict = events.conflict;
    order = events.order;
  }

(* Return true if a labelled instruction has the given label. *)
let rec has_label (pseudo : BellBase.parsedPseudo) (label : string) : bool =
  match pseudo with
  | Label(test, _) when test = label -> true
  | Label(_, next) -> has_label next label
  | Instruction _
  | Macro _
  | Symbolic _
  | Nop -> false

(* Return the index of the first instruction with the given label. *)
let find_label (instructions : BellBase.parsedPseudo array) (label : string) : int =
  let rec search (instructions : BellBase.parsedPseudo array) (index : int) : int =
    let pseudo = Array.get instructions index in
    if has_label pseudo label then index else search instructions (index + 1)
  in
  (* Search until an index out of range happends. *)
  try search instructions 0
  with Invalid_argument _ -> raise (Invalid_argument ("label not found: " ^ label))

(* Return true if a write has the same address and value as a read. *)
let write_justifies_read (write : write) (read : read) : bool =
  read.from.global = write.into.global &&
  read.from.offset = write.into.offset &&
  read.value = write.value

(* Returns a list of writes justified by the init event specified. *)
let writes_from_init (init : MiscParser.state) (event_id : event) : write list =
  List.fold_left (fun accumulator init ->
    (* TODO: Assumes that run_type isn't relevant. *)
    let (location, (run_type, value)) = init in

    let value = match value with
    | Concrete value -> value
    | Symbolic _ -> assert false (* Meaningless. *)
    in

    let address = match location with
    | Location_reg _
    | Location_sreg _ -> raise (LISAtoESException "write register [value] not supported.")
    | Location_global(Symbolic name) -> { global = name; offset = 0; }
    (* TODO: It doesn't look like the parser generates this in init. *)
    (* TODO: This means that some of the JCTC LISA tests are broken because they use arrays in init. *)
    | Location_deref(Symbolic name, offset) -> (* { global = name; offset = offset; } *) assert false
    | Location_global(Concrete _)
	(* TODO: This is what a[0] actually seems to match. *)
    | Location_deref(Concrete _, _) -> assert false (* Meaningless. *)
    in

    { id = event_id; into = address; value = value; } :: accumulator
  ) [] init

(* Translates a sequence of instructions form a single thread into an event structure. *)
(* `program_counter` gives the index of the instruction to interpret, allowing arbitrary branching. *)
(* `depth` tracks the number of instructions interpreted to detect infinite loops. *)
let rec translate_instructions
  (instructions : BellBase.parsedPseudo array)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : event ref)
  (depth : int)
: events =
  if depth > 16 then
    raise (LISAtoESException (Printf.sprintf
      "Program still running after %d instructions, aborting (maybe this program loops?)"
      depth
    ))
  else if program_counter >= Array.length instructions then
    (* Program finished. *)
    { reads=[]; writes=[]; conflict=[]; order=[]; }
  else
    let line = Array.get instructions program_counter in
    let depth = depth + 1 in
    match line with
    | Nop -> translate_instructions instructions (program_counter + 1) store values next_id depth
    | Label(_, next_label) ->
      let instruction = instruction_from_pseudo_label next_label in
      (match instruction with
      | Some instruction -> translate_instruction
        instructions
        program_counter
        store
        values
        next_id
        depth
        instruction
      | None -> translate_instructions instructions (program_counter + 1) store values next_id depth)
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
  (instructions : BellBase.parsedPseudo array)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : event ref)
  (depth : int)
  (instruction : BellBase.parsedInstruction)
: events =
  match instruction with
  | Pld(destination, source, labels) ->
    (* Spawn a set of conflicting read events, one for each value that could be read. *)
    let destination = unwrap_reg destination in
    let source = address_from_addr_op store source in
    let program_counter = program_counter + 1 in
    let events = ref empty_events in
    let last_root = ref None in

    Printf.printf "TODO HACK Load r%d = %s[%d]\n" destination source.global source.offset;

    for value = values.minimum to values.maximum do
      let new_store = Store.update store destination value in
      let subtree = translate_instructions
        instructions
        program_counter
        new_store
        values
        next_id
        depth
      in
      let subtree, read_id = prefix_read subtree next_id source value in
      match !last_root with
      | Some last_id -> (events := sum !events subtree last_id read_id)
      | None -> (events := subtree);
      last_root := Some read_id
    done;
    !events
  | Pst(Addr_op_atom(Rega destination), source, labels) ->
    (* Special case for writing to a register, doesn't create any events directly. *)
	let destination = unwrap_reg destination in
    let value = value_from_reg_or_imm store source in
	let program_counter = program_counter + 1 in
	let store = Store.update store destination value in

    Printf.printf "TODO HACK Register write r%d = %d\n" destination value;

    translate_instructions instructions program_counter store values next_id depth
  | Pst(destination, source, labels) ->
    (* Spawn a write event. *)
    let destination = address_from_addr_op store destination in
    let value = value_from_reg_or_imm store source in
    let program_counter = program_counter + 1 in

    Printf.printf "TODO HACK Store %s[%d] = %d\n" destination.global destination.offset value;

    let subtree = translate_instructions instructions program_counter store values next_id depth in
    prefix_write subtree next_id destination value
  | Pbranch(Some(test), destination, labels) ->
    (* Conditional jump, doesn't create any events directly. *)
    let test = unwrap_reg test in
    let value = Store.lookup store test in

    Printf.printf "TODO HACK Branch %s if r%d (currently %d)\n" destination test value;

    (* TODO: What means true? *)
    let next = if value != 0 then find_label instructions destination else program_counter + 1 in
    translate_instructions instructions next store values next_id depth
  | Pbranch(None, destination, labels) ->
    Printf.printf "TODO HACK Jump %s\n" destination;

    (* Unconditional jump, doesn't create any events directly. *)
    let next = find_label instructions destination in
    translate_instructions instructions next store values next_id depth
  | Pmov(destination, (RAI source)) ->
    (* Move from register or immediate. *)
    (* TODO: Support globals as source addresses, major restructuring needed. *)
    let destination = unwrap_reg destination in
    let value = value_from_imm_or_addr_or_reg store source in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    Printf.printf "TODO HACK Mov r%d = %d\n" destination value;

    translate_instructions instructions program_counter store values next_id depth
  | Pmov(destination, OP(operation, a, b)) ->
    (* Arithmetic, doesn't generate events. *)
    (* TODO: Support globals as source addresses, major restructuring needed. *)
    let destination = unwrap_reg destination in
    let a = value_from_imm_or_addr_or_reg store a in
    let b = value_from_imm_or_addr_or_reg store b in
    let value = do_arithmetic operation a b values in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    Printf.printf "TODO HACK Arithmetic r%d = %d\n" destination value;

    translate_instructions instructions program_counter store values next_id depth
  | _ -> assert false (* TODO: Other instructions. *)

(* Translate a program AST into an event structure, this is the entrypoint into the module. *)
(* `init` gives the initial values for global variables, letting the init event justify non-zero reads. *)
(* `program` gives the multi-threaded program AST from LISAParser. *)
(* `values` gives the range of numeric values to enumerate for read events. *)
let translate
  (init : MiscParser.state)
  (program : BellBase.parsedPseudo list list)
  (values : values)
: EventStructure.t =
  (* The init event is special, and always gets the first ID number. *)
  let init_id = 1 in

  (* This boxed counter is used to make sure all events get unique ID numbers. *)
  let next_id = ref (init_id + 1) in

  (* Translate each thread and compose the resulting event structures together. *)
  let compose_threads (events : events) (instructions : BellBase.parsedPseudo list) : events =
    let instructions = Array.of_list instructions in
    let subtree = translate_instructions instructions 0 Store.empty values next_id 0 in
    product events subtree
  in
  let events = List.fold_left compose_threads empty_events program in

  (* Add the order relations for the init event. *)
  let events = prefix_event events init_id in

  (* Add writes that are justified by init. *)
  let events = {
    reads = events.reads;
    writes = (writes_from_init init init_id) @ events.writes;
    conflict = events.conflict;
    order = events.order;
  } in

  (* Generate the justifies relation. *)
  (* In this case, "justifies" pairs reads and writes of the same variable and value. *)
  let justifies = List.fold_left (fun accumulator read ->
    List.fold_left (fun accumulator write ->
      if write_justifies_read write read then (write.id, read.id) :: accumulator else accumulator
    ) accumulator events.writes
  ) [] events.reads in

  (* Convert from intermediate representation to final event structure. *)
  {
    (* Beware, not all writes now correspond to events! Don't use it calculate number of events. *)
    events_number = !next_id - 1;
    (* TODO: Why do I have to specify the types here to get this to compile? *)
    reads = List.map (fun (read : read) -> read.id) events.reads;
    justifies = justifies;
    conflicts = events.conflict;
    order = events.order;
  }
