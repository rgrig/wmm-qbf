type t = { co : bool ; init : bool ; sc : bool } 

val show : t -> string
val pp : Format.formatter -> t -> unit
val default : t
val compat : t

val set_enumco : bool -> t -> t
val set_init : bool -> t -> t
val set_enumsc : bool -> t -> t
