type t = { co : bool ; init : bool ; sc : bool } 

val pp : t -> string
val default : t
val compat : t

val set_enumco : bool -> t -> t
val set_init : bool -> t -> t
val set_enumsc : bool -> t -> t
