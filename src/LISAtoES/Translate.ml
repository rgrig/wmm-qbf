(* This module translates LISA program ASTs from LISAParser into event structures. *)

open MiscParser
open Constant
open BellBase
open MetaConst

exception LISAtoESException of string

let debug = ref false

(* Special global name for dummy writes, deliberately illegal according to the parser. *)
let dummy_global = " dummy write "

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
  r_id : EventStructure.event;
  r_from : address;
  r_value : int;
}

(* Information about a write event, used as intermediate storage until justification has been calculated. *)
type write = {
  w_id : EventStructure.event;
  w_into : address;
  (* Register thread and number, only given if the write came from a single register. *)
  w_from : (int * int) option;
  w_value : int;
}

(* Intermediate event structure, gets translated to the final datatype before leaving this module. *)
type events = {
  reads : read list;
  writes : write list;
  conflict : EventStructure.relation;
  order : EventStructure.relation;
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

let unwrap_val = function
  | Constant.Concrete i -> i
  | _ -> raise (LISAtoESException "Symbolic values not supported")

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
  if !debug then Printf.printf "Operation on %d and %d\n" a b;

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
let sum (a : events) (b : events) (root_a : EventStructure.event) (root_b : EventStructure.event) : events =
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
let prefix_event (events : events) (event : EventStructure.event) : events =
  (* TODO: Check I understood the notation properly. *)
  (* This should be equivalent to "≤0 ∪ ({⊥} × E)" but without (⊥, ⊥). *)
  let read_order = List.map (fun read -> (event, read.r_id)) events.reads in
  let write_order = List.map (fun write -> (event, write.w_id)) events.writes in
  {
    reads = events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order @ read_order @ write_order;
  }

(* Add a read event before the given events and return the result and the allocated event id. *)
let prefix_read (events : events) (next_id : EventStructure.event ref) (r_from : address) (r_value : int) : events * EventStructure.event =
  let r_id = !next_id in
  next_id := !next_id + 1;
  let events = prefix_event events r_id in
  let events = {
    reads = { r_id; r_from; r_value } :: events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order;
  } in
  (events, r_id)

(* Add a write event before the given events. *)
let prefix_write
  (events : events)
  (next_id : EventStructure.event ref)
  (w_from : (int * int) option)
  (w_into : address)
  (w_value : int)
: events =
  let w_id = !next_id in
  next_id := !next_id + 1;
  let events = prefix_event events w_id in
  {
    reads = events.reads;
    writes = { w_id; w_into; w_from; w_value } :: events.writes;
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
  read.r_from = write.w_into && read.r_value = write.w_value

(* Returns a list of writes justified by the init event specified. *)
let writes_from_init (init : MiscParser.state) (w_id : EventStructure.event) : write list =
  List.fold_left (fun accumulator init ->
    (* TODO: Assumes that run_type isn't relevant. *)
    let (location, (run_type, value)) = init in

    let w_value = unwrap_val value in

    let w_into = match location with
    | Location_reg _
    | Location_sreg _ -> raise (LISAtoESException "write register [value] not supported.")
    | Location_global(Symbolic name) -> { global = name; offset = 0; }
    (* TODO: It doesn't look like the parser generates this in init. *)
    (* TODO: This means that some of the JCTC LISA tests are broken because they use arrays in init. *)
    | Location_deref(Symbolic name, offset) -> (* { global = name; offset = offset; } *) assert false
    | Location_global(Concrete _)
    (* TODO: This is what a[0] actually seems to match. *)
    | Location_deref(Concrete _, _) -> assert false (* This pattern should be nonsense (but isn't). *)
    in

    { w_id; w_into; w_from = None; w_value } :: accumulator
  ) [] init

(* Translates a sequence of instructions form a single thread into an event structure. *)
(* `program_counter` gives the index of the instruction to interpret, allowing arbitrary branching. *)
(* `depth` tracks the number of instructions interpreted to detect infinite loops. *)
let rec translate_instructions
  (thread_name : int)
  (instructions : BellBase.parsedPseudo array)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : EventStructure.event ref)
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
    | Nop -> translate_instructions thread_name instructions (program_counter + 1) store values next_id depth
    | Label(_, next_label) ->
      let instruction = instruction_from_pseudo_label next_label in
      (match instruction with
      | Some instruction -> translate_instruction
        thread_name
        instructions
        program_counter
        store
        values
        next_id
        depth
        instruction
      | None -> translate_instructions thread_name instructions (program_counter + 1) store values next_id depth)
    | Instruction instruction -> translate_instruction
      thread_name
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
  (thread_name : int)
  (instructions : BellBase.parsedPseudo array)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : EventStructure.event ref)
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

    if !debug then
      Printf.printf "Load r%d = %s[%d]\n" destination source.global source.offset;

    for value = values.minimum to values.maximum do
      let new_store = Store.update store destination value in
      let subtree = translate_instructions
        thread_name
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

    if !debug then
      Printf.printf "Register write r%d = %d\n" destination value;

    translate_instructions thread_name instructions program_counter store values next_id depth
  | Pst(destination, source, labels) ->
    (* Spawn a write event. *)
    let destination = address_from_addr_op store destination in
    let value = value_from_reg_or_imm store source in
    let program_counter = program_counter + 1 in
    let source_register = match source with
    | Regi GPRreg number -> Some(thread_name, number)
    | _ -> None
    in

    if !debug then
      Printf.printf "Store %s[%d] = %d\n" destination.global destination.offset value;

    let subtree = translate_instructions thread_name instructions program_counter store values next_id depth in
    prefix_write subtree next_id source_register destination value
  | Pbranch(Some(test), destination, labels) ->
    (* Conditional jump, doesn't create any events directly. *)
    let test = unwrap_reg test in
    let value = Store.lookup store test in

    if !debug then
      Printf.printf "Branch %s if r%d (currently %d)\n" destination test value;

    (* TODO: Check this definition of true is correct for LISA. *)
    let next = if value != 0 then find_label instructions destination else program_counter + 1 in
    translate_instructions thread_name instructions next store values next_id depth
  | Pbranch(None, destination, labels) ->
    if !debug then
      Printf.printf "Jump %s\n" destination;

    (* Unconditional jump, doesn't create any events directly. *)
    let next = find_label instructions destination in
    translate_instructions thread_name instructions next store values next_id depth
  | Pmov(destination, (RAI source)) ->
    (* Move from register or immediate. *)
    (* TODO: Support globals as source addresses, major restructuring needed. *)
    let destination = unwrap_reg destination in
    let value = value_from_imm_or_addr_or_reg store source in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    if !debug then
      Printf.printf "Mov r%d = %d\n" destination value;

    translate_instructions thread_name instructions program_counter store values next_id depth
  | Pmov(destination, OP(operation, a, b)) ->
    (* Arithmetic, doesn't generate events. *)
    (* TODO: Support globals as source addresses, major restructuring needed. *)
    let destination = unwrap_reg destination in
    let a = value_from_imm_or_addr_or_reg store a in
    let b = value_from_imm_or_addr_or_reg store b in
    let value = do_arithmetic operation a b values in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    if !debug then
      Printf.printf "Arithmetic r%d = %d\n" destination value;

    translate_instructions thread_name instructions program_counter store values next_id depth
  | _ -> assert false (* TODO: Other instructions. *)

(* Generate the justifies relation. *)
(* In this case, "justifies" pairs reads and writes of the same variable and value. *)
let justify_reads (reads : read list) (writes : write list) : EventStructure.relation =
  List.fold_left (fun accumulator read ->
    List.fold_left (fun accumulator write ->
      if write_justifies_read write read then (write.w_id, read.r_id) :: accumulator else accumulator
    ) accumulator writes
  ) [] reads

(* Return a list of pairs of events that read or write the same global. *)
let match_locations (reads : read list) (writes : write list) : EventStructure.relation =
  (* Make one big list of all events and the global they touch. *)
  (* Type explicitly stated because inference fails here. *)
  let read_addresses = List.map (fun read -> (read.r_id, read.r_from)) reads in
  let write_addresses = List.map (fun write -> (write.w_id, write.w_into)) writes in
  let event_addresses = List.append read_addresses write_addresses in

  (* Find pairs with the same source/destination. *)
  List.fold_left (fun accumulator (a_event, a_global) ->
    List.fold_left (fun accumulator (b_event, b_global) ->
      if a_event != b_event && a_global = b_global then (a_event, b_event) :: accumulator else accumulator
    ) accumulator event_addresses
  ) [] event_addresses

(* TODO: Move? *)
(* Pretty much straight from the documentation. *)
module IntPairs =
  struct
    type t = int * int
      let compare (x0,y0) (x1,y1) =
        match Pervasives.compare x0 x1 with
        | 0 -> Pervasives.compare y0 y1
        | c -> c
  end
module IntPairsMap = Map.Make(IntPairs)
(* Aliases to help readability. *)
module RegisterMap = IntPairsMap
module ThreadMap = Util.IntMap

(* Parse a string register name into a register number. *)
let parse_register (name : string) : int =
  match BellBase.parse_reg name with
  | Some (BellBase.GPRreg i) -> i
  | _ -> raise (LISAtoESException "Failed to parse register name")

(* Translate conjunctions (only) into maps. *)
let rec parse_condition_expression
  ((values, registers) : int RegisterMap.t * int list ThreadMap.t)
  (expression : MiscParser.prop)
: int RegisterMap.t * int list ThreadMap.t = match expression with
  | ConstrGen.And expressions -> List.fold_left parse_condition_expression (values, registers) expressions
  | ConstrGen.Atom (ConstrGen.LV (MiscParser.Location_reg (thread, register), value)) ->
    let register = parse_register register in
    let value = unwrap_val value in
    let values = RegisterMap.add (thread, register) value values in
    (* Avoiding Map.update to retain compatibility with Ocaml < 4.06.0. *)
    (* TODO: Switch to update to save second traversal of map, if possible. *)
    (* TODO: Check that register only gets added once? *)
    let register_list = try
      register :: ThreadMap.find thread registers
    with
    | Not_found -> [register]
    in
    let registers = ThreadMap.add thread register_list registers in
    (values, registers)
  | _ -> failwith "not supported"

(* Parse final condition and return two maps: *)
(* - Unique register identification (thread number, register number) to expected value. *)
(* - Thread number to registers found in that thread mentioned in the condition. *)
let parse_condition (litmus : Lisa.litmus) : int RegisterMap.t * int list ThreadMap.t =
  let _, _, condition, _ = litmus.Lisa.final in

  (* Check this is an exists expression and get the enclosed logic. *)
  let expression = match condition with
  | ConstrGen.ExistsState expression -> expression
  | _ -> failwith "not supported"
  in

  parse_condition_expression (RegisterMap.empty, ThreadMap.empty) expression

(* Return a thread with write instructions (to a dummy location) for a set of registers appended. *)
let append_dummy_writes
  (thread : BellBase.parsedPseudo list)
  (registers : int list)
: BellBase.parsedPseudo list =
  let writes = List.map (fun register ->
    let reg_or_imm = Regi (GPRreg register) in
    let addr_op = Addr_op_atom(Abs(Symbolic dummy_global))in
    Instruction(Pst(addr_op, reg_or_imm, []))) registers
  in
  thread @ writes

(* Return litmus with extra write instructions appended. *)
(* The extra writes are from registers mentioned in the constraint to a dummy location. *)
(* The resulting write events are found later and used to indentify useful parts of the event structure. *)
let add_dummy_constraint_writes
  (litmus : Lisa.litmus)
  (thread_to_registers : int list ThreadMap.t)
: Lisa.litmus =
  let program = List.map2 (fun thread_name thread ->
    let registers =
      try ThreadMap.find thread_name thread_to_registers
      with Not_found -> [] in
    append_dummy_writes thread registers) litmus.Lisa.threads litmus.Lisa.program
  in
  Lisa.{ litmus with program }

(* Return the set of events caused by dummy write instructions that match the final condition. *)
let get_must_execute (events : events) (expected : int RegisterMap.t) : EventStructure.set =
  let writes = List.filter (fun write ->
    match write.w_from with
    | Some source -> 
      write.w_into.global = dummy_global
      && write.w_value = (RegisterMap.find source expected)
    | None -> false) events.writes
  in
  List.map (fun write -> write.w_id) writes

(* Translate a program AST into an event structure, this is the entrypoint into the module. *)
(* `init` gives the initial values for global variables, letting the init event justify non-zero reads. *)
(* `program` gives the multi-threaded program AST from LISAParser. *)
(* `min` and `max` give the range of numeric values to enumerate for read events (inclusive). *)
let translate litmus minimum maximum =
  let values = { minimum; maximum } in

  (* The init event is special, and always gets the first ID number. *)
  let init_id = 1 in

  (* This boxed counter is used to make sure all events get unique ID numbers. *)
  let next_id = ref (init_id + 1) in (* TODO: wrap in a function *)

  let (register_to_value, thread_to_registers) = parse_condition litmus in
  let litmus = add_dummy_constraint_writes litmus thread_to_registers in

  (* Translate each thread and compose the resulting event structures together. *)
  let compose_threads (events : events) (thread_name : int) (instructions : BellBase.parsedPseudo list)
  : events =
    let instructions = Array.of_list instructions in
    let subtree = translate_instructions thread_name instructions 0 Store.empty values next_id 0 in
    product events subtree
  in
  let events = List.fold_left2 compose_threads empty_events litmus.Lisa.threads litmus.Lisa.program in

  (* Add the order relations for the init event. *)
  let events = prefix_event events init_id in

  (* Generate the same location relation. *)
  let same_location = match_locations events.reads events.writes in

  (* Build set of write events that match the end condition. *)
  let must_execute = get_must_execute events register_to_value in
  
  (* TODO: can_execute should be more clever than this *)
  let can_execute = Util.range 1 (!next_id - 1) in
  
  (* Add virtual writes tied to init with all the values in the initialisation list. *)
  let events = {
    reads = events.reads;
    (* Beware: all writes for initialization are bound to one event, namely init_id.
    More generally, don't use the length of the following list to count events.*)
    writes = (writes_from_init litmus.Lisa.init init_id) @ events.writes;
    conflict = events.conflict;
    order = events.order;
  } in

  (* Generate the justifies relation. *)
  let justifies = justify_reads events.reads events.writes in
  let reads = List.map (fun r -> r.r_id) events.reads in

  (* Convert from intermediate representation to final event structure. *)
  (EventStructure.{
    events_number = !next_id - 1;
    reads;
    justifies;
    conflicts = events.conflict;
    order = events.order;
    sloc = same_location;
  }, can_execute, must_execute)
