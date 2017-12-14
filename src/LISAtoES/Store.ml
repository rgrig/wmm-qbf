(* A mapping from a register to a value. *)
type entry = {
	register : int;
	value : int;
}

type t = entry list

let empty = []

let lookup (store : t) (register : int) : int =
	match store with
	| [] -> assert false (* Register not written. *)
	| entry :: rest where entry.register = register -> entry.value
	| _ :: rest lookup rest register

let update (store : t) (register : int) (value : int) : t =
	{ reigster = register; value = value; } :: store
