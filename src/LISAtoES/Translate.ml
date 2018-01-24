(* This module translates LISA program ASTs from LISAParser into event structures. *)

open MiscParser
open Constant
open BellBase
open MetaConst

module ThreadMap = Util.IntMap

exception LISAtoESException of string

let debug = ref false

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

let get_id (next_id : EventStructure.event ref) : EventStructure.event =
  let id = !next_id in
  next_id := id + 1;
  id

(* Add an event before the given event set, without updating lists of reads and writes. *)
let prefix_event (events : events) (event : EventStructure.event) : events =
  let read_order = List.map (fun read -> (event, read.r_id)) events.reads in
  let write_order = List.map (fun write -> (event, write.w_id)) events.writes in
  {
    reads = events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order @ read_order @ write_order;
  }

(* Add a read event before the given events. *)
let prefix_read
  (events : events)
  (r_id : EventStructure.event)
  (r_from : address)
  (r_value : int)
: events =
  let events = prefix_event events r_id in
  let events = {
    reads = { r_id; r_from; r_value } :: events.reads;
    writes = events.writes;
    conflict = events.conflict;
    order = events.order;
  } in
  events

(* Add a write event before the given events. *)
let prefix_write
  (events : events)
  (w_id : EventStructure.event)
  (w_from : (int * int) option)
  (w_into : address)
  (w_value : int)
: events =
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

(* Returns a list of writes justified by the init event whose id is given. *)
let writes_from_init (init : MiscParser.state) (w_id : EventStructure.event) : write list =
  List.fold_left (fun accumulator init ->
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

(* Returns true if the state of all registers in the thread match the values in the condition. *)
let condition_met (store : Store.t) (condition : (int * int) list) : bool =
  let must_match = fun (register, value) ->
    if (Store.lookup store register) != value then raise Not_found
  in
  try List.iter must_match condition; true
  with Not_found -> false

(* Translates a sequence of instructions from a single thread into an event structure. *)
(* Returns event information and a set of events that tag branches where the final condition was met. *)
(* `condition` gives a list of the expected values for each register in this thread. *)
(* `program_counter` gives the index of the instruction to interpret, allowing arbitrary branching. *)
(* `depth` tracks the number of instructions interpreted to detect infinite loops. *)
(* `parent` gives the id of the parent event of this branch. *)
let rec translate_instructions
  (thread_name : int)
  (instructions : BellBase.parsedPseudo array)
  (condition : (int * int) list)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : EventStructure.event ref)
  (parent : EventStructure.event)
  (depth : int)
: events * EventStructure.set =
  if depth > 16 then
    raise (LISAtoESException (Printf.sprintf
      "Program still running after %d instructions, aborting (maybe this program loops?)"
      depth
    ))
  else if program_counter >= Array.length instructions then
    (* Program finished. *)
    let accept = if condition_met store condition then [parent] else [] in
    { reads=[]; writes=[]; conflict=[]; order=[]; }, accept
  else
    let line = Array.get instructions program_counter in
    let depth = depth + 1 in
    match line with
    | Nop -> translate_instructions
      thread_name
      instructions
      condition
      (program_counter + 1)
      store
      values
      next_id
      parent
      depth
    | Label(_, next_label) ->
      let instruction = instruction_from_pseudo_label next_label in
      (match instruction with
      | Some instruction -> translate_instruction
        thread_name
        instructions
        condition
        program_counter
        store
        values
        next_id
        parent
        depth
        instruction
      | None -> translate_instructions
        thread_name
        instructions
        condition
        (program_counter + 1)
        store
        values
        next_id
        parent
        depth)
    | Instruction instruction -> translate_instruction
      thread_name
      instructions
      condition
      program_counter
      store
      values
      next_id
      parent
      depth
      instruction
    | Macro _
    | Symbolic _ -> assert false

(* This awkward recursion pattern is here because branch instructions can arbitrarily change the program *)
(* counter, and nesting instruction decoding pattern matches would be very unpleasant. *)
and translate_instruction
  (thread_name : int)
  (instructions : BellBase.parsedPseudo array)
  (condition : (int * int) list)
  (program_counter : int)
  (store : Store.t)
  (values : values)
  (next_id : EventStructure.event ref)
  (parent : EventStructure.event)
  (depth : int)
  (instruction : BellBase.parsedInstruction)
: events * EventStructure.set =
  match instruction with
  | Pld(destination, source, labels) ->
    (* Spawn a set of conflicting read events, one for each value that could be read. *)
    let destination = unwrap_reg destination in
    let source = address_from_addr_op store source in
    let program_counter = program_counter + 1 in
    let events = ref empty_events in
    let accept = ref [] in
    let last_root = ref None in

    if !debug then
      Printf.printf "Load r%d = %s[%d]\n" destination source.global source.offset;

    for value = values.minimum to values.maximum do
      let new_store = Store.update store destination value in
      let read_id = get_id next_id in
      let subtree, subaccept = translate_instructions
        thread_name
        instructions
        condition
        program_counter
        new_store
        values
        next_id
        read_id
        depth
      in
      let subtree = prefix_read subtree read_id source value in
      accept := !accept @ subaccept;
      match !last_root with
      | Some last_id -> (events := sum !events subtree last_id read_id)
      | None -> (events := subtree);
      last_root := Some read_id
    done;
    !events, !accept
  | Pst(Addr_op_atom(Rega destination), source, labels) ->
    (* Special case for writing to a register, doesn't create any events directly. *)
    let destination = unwrap_reg destination in
    let value = value_from_reg_or_imm store source in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    if !debug then
      Printf.printf "Register write r%d = %d\n" destination value;

    translate_instructions
      thread_name
      instructions
      condition
      program_counter
      store
      values
      next_id
      parent
      depth
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

    let write_id = get_id next_id in
    let subtree, accept = translate_instructions
      thread_name
      instructions
      condition
      program_counter
      store
      values
      next_id
      write_id
      depth
    in
    let events = prefix_write subtree write_id source_register destination value in
    events, accept
  | Pbranch(Some(test), destination, labels) ->
    (* Conditional jump, doesn't create any events directly. *)
    let test = unwrap_reg test in
    let value = Store.lookup store test in

    if !debug then
      Printf.printf "Branch %s if r%d (currently %d)\n" destination test value;

    (* TODO: Check this definition of true is correct for LISA. *)
    let next = if value != 0 then find_label instructions destination else program_counter + 1 in
    translate_instructions thread_name instructions condition next store values next_id parent depth
  | Pbranch(None, destination, labels) ->
    if !debug then
      Printf.printf "Jump %s\n" destination;

    (* Unconditional jump, doesn't create any events directly. *)
    let next = find_label instructions destination in
    translate_instructions thread_name instructions condition next store values next_id parent depth
  | Pmov(destination, (RAI source)) ->
    (* Move from register or immediate. *)
    (* TODO: Support globals as source addresses, major restructuring needed. *)
    let destination = unwrap_reg destination in
    let value = value_from_imm_or_addr_or_reg store source in
    let program_counter = program_counter + 1 in
    let store = Store.update store destination value in

    if !debug then
      Printf.printf "Mov r%d = %d\n" destination value;

    translate_instructions
      thread_name
      instructions
      condition
      program_counter
      store
      values
      next_id
      parent
      depth
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

    translate_instructions
      thread_name
      instructions
      condition
      program_counter
      store
      values
      next_id
      parent
      depth
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

(* Parse a string register name into a register number. *)
let parse_register (name : string) : int =
  match BellBase.parse_reg name with
  | Some (BellBase.GPRreg i) -> i
  | _ -> raise (LISAtoESException "Failed to parse register name")

let rec parse_condition_expression
  (accumulator : (int * int) list ThreadMap.t)
  (expression : MiscParser.prop)
: (int * int) list ThreadMap.t = match expression with
  | ConstrGen.And expressions -> List.fold_left parse_condition_expression accumulator expressions
  | ConstrGen.Atom (ConstrGen.LV (MiscParser.Location_reg (thread, register), value)) ->
    let register = parse_register register in
    let value = unwrap_val value in
    (* Avoiding Map.update to retain compatibility with Ocaml < 4.06.0. *)
    (* TODO: Switch to update to save second traversal of map, if possible. *)
    let pairs = (register, value) :: try ThreadMap.find thread accumulator with Not_found -> [] in
    ThreadMap.add thread pairs accumulator
  | _ -> failwith "not supported"

(* Parse final condition and return a map from thread number to lists of registers and expected values. *)
let parse_condition (litmus : Lisa.litmus) : (int * int) list ThreadMap.t =
  let _, _, condition, _ = litmus.Lisa.final in

  (* Check this is an exists expression and get the enclosed logic. *)
  let expression = match condition with
  | ConstrGen.ExistsState expression -> expression
  | _ -> failwith "not supported"
  in

  parse_condition_expression ThreadMap.empty expression

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

  let condition = parse_condition litmus in

  (* Translate each thread and compose the resulting event structures together. *)
  let compose_threads
    ((events, accept) : events * EventStructure.set list)
    (thread_name : int)
    (instructions : BellBase.parsedPseudo list)
  : events * EventStructure.set list =
    let instructions = Array.of_list instructions in
    let program_counter = 0 in
    let depth = 0 in
    let thread_condition = try ThreadMap.find thread_name condition with Not_found -> [] in
    let subtree, subaccept = translate_instructions
      thread_name
      instructions
      thread_condition
      program_counter
      Store.empty
      values
      next_id
      init_id
      depth
    in
    (product events subtree), subaccept :: accept
  in
  let events, accept = List.fold_left2
    compose_threads (empty_events, []) litmus.Lisa.threads litmus.Lisa.program
  in

  (* Add the order relations for the init event. *)
  let events = prefix_event events init_id in

  (* Generate the same location relation. *)
  let same_location = match_locations events.reads events.writes in

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
    na = [];
    sc = [];
    rel = [];
    acq = [];
    consume = [];
    fences = [];
    ext = []
  }, accept)
