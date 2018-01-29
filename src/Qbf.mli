type variable = string
type model = variable list
type qid = int (* quantifier id *)

(* TODO: Make abstract so other modules are forced to use the constructors.
Use the on_ trick. *)
type t =
  | Var of variable
  | Not of t
  | And of t list
  | Or of t list
  | Exists of variable list * t * qid
  | Forall of variable list * t * qid

val fresh_var : ?prefix:string -> unit -> variable

val mk_var : variable -> t
val mk_implies : t list -> t -> t
val mk_true : unit -> t
val mk_false : unit -> t
val mk_and : t list -> t
val mk_or : t list -> t
val mk_not : t -> t
val mk_exists : variable list -> t -> t
val mk_forall : variable list -> t -> t

val holds : t -> bool
val models : t -> model list
val show: t -> string
val pp : Format.formatter -> t -> unit
