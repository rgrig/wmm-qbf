type configuration
type predicate = configuration -> Qbf.t
type relation = configuration -> configuration -> Qbf.t

val justifies : EventStructure.t -> relation
val valid : EventStructure.t -> predicate

val fresh_configuration : EventStructure.t -> configuration
val forall : configuration -> Qbf.t -> Qbf.t
val exists : configuration -> Qbf.t -> Qbf.t
val is_set : configuration -> EventStructure.set -> Qbf.t

val subset : relation
val equal : relation

val flip : relation -> relation
val intersect : relation -> relation -> relation
val union : relation -> relation -> relation


(* When we introduce (existentially quantified) intemediate configurations
we need to have access to a validity predicate. *)

val sequence : EventStructure.t -> relation -> relation -> relation
val iterate : EventStructure.t -> int -> relation -> relation
val at_most_n : EventStructure.t -> int -> relation -> relation
