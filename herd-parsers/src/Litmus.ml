type litmus = {
  (* Initial state of the virtual machine. *)
  setup : setup_location * setup_value list;
  (* Parallel threads of program. *)
  processes : instruction list list;
  (* Logic to check final state. *)
  condition : logic;
}

(* Write destination in setup. *)
type setup_location =
| Register of register
| Variable of variable

(* Write source in setup. *)
type setup_value =
| Literal of int
(* TODO: What these last three mean is still open to interpretation. *)
(* Set to value of global variable? Assume zero if not set yet? *)
| Variable of variable
(* Literal address or address of constant? *)
| Address of int
(* Address of global variable, presumably? *)
| VariableAddress of variable

(* One line in one program process. *)
type statement = {
  instruction : instruction;
  label : string option;
  tags: string list;
}

type instruction = {
| Branch of {condition : register option; label : string}
| Fence of (string list) * (string list) option
| Mov of {destination : register; value : operation}
| Read of {destination : register; source : address}
| RMW of {destination : register; value : operation; address : address}
| WriteRegister of {destination : address; source : register; }
| WriteImmediate of {destination : address; value : int; }

(* Identifier for a register local to a process. *)
type register = {
  process : int;
  register : int;
}

(* Global variable. *)
type variable = {
	name : string;
}

type address =
| Register of register * address_add
| Variable of variable * address_add

type address_add =
| None
| Literal of int
| Register of register

(* Condition for test. *)
type logic =
(* True. *)
| Always
| Expression of logic_tree
| ForAll of logic_tree
| Exists of logic_tree
| NotExists of logic_tree

type logic_tree =
| True
| False
| Not of logic_tree
| And of logic_tree * logic_tree
| Or of logic_tree * logic_tree
| Implies of logic_tree * logic_tree
| Equality of condition_location * condition_value

(* Source of data for test in condition. *)
type condition_location =
| Register of register
| Variable of variable

(* Source of value to test against in condition. *)
type condition_value =
| Literal of int
| Variable of variable
