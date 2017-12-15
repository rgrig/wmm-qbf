(* A mapping from a register to a value. *)
type entry = {
	register : int;
	value : int;
}

(* A collection of mappings, newest first. *)
type t = entry list

let empty = []

(* Get the value stored in `register`. *)
let lookup (store : t) (register : int) : int =
	match store with
	| [] -> 0 (* Register not written. *)
	| entry :: rest where entry.register = register -> entry.value
	| _ :: rest lookup rest register

(* Return a store with a register overwritten. *)
let update (store : t) (register : int) (value : int) : t =
	{ reigster = register; value = value; } :: store
