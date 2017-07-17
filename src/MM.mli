type configuration
type q_relation

(* We're going to have predicates on configurations, like
   down-closed, and predicates on relations like acyclic *)
type 'a predicate = 'a -> Qbf.t
type relation = configuration -> configuration -> Qbf.t

val justifies : EventStructure.t -> relation
val valid_conf : EventStructure.t -> configuration predicate
val valid_rel : EventStructure.t -> relation

val fresh_configuration : EventStructure.t -> configuration
val forall : configuration -> Qbf.t -> Qbf.t
val exists : configuration -> Qbf.t -> Qbf.t
val equals_set : configuration -> EventStructure.set -> Qbf.t

val subset : relation
val equal : relation

val flip : relation -> relation
val intersect : relation -> relation -> relation
val union : relation -> relation -> relation

val intersect_n : relation list -> relation
val union_n : relation list -> relation

val fresh_relation : EventStructure.t -> q_relation
val reflexive : EventStructure.t -> q_relation predicate

(* When we introduce (existentially quantified) intermediate configurations
we need to have access to a validity predicate. *)

val sequence : EventStructure.t -> relation -> relation -> relation
val at_most_n : EventStructure.t -> int -> relation -> relation

val set_of_model : configuration -> Qbf.model -> EventStructure.set

