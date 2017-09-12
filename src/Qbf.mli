type variable = string
type model = variable list

type t

val mk_var : variable -> t
val mk_implies : t list -> t -> t
val mk_true : unit -> t
val mk_false : unit -> t
val mk_and : t list -> t
val mk_or : t list -> t
val mk_not : t -> t
val mk_exists : variable list -> t -> t
val mk_forall : variable list -> t -> t

val holds : t -> bool * bool -> bool option
val models : t -> bool -> model list
