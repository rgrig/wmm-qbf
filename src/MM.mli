type so_var

(* We're going to have predicates on so_vars, like
   down-closed, and predicates on relations like acyclic *)
type 'a predicate = 'a -> Qbf.t
type relation = so_var -> so_var -> Qbf.t

val justifies : EventStructure.t -> relation
val valid_conf : EventStructure.t -> so_var predicate
val valid_rel : EventStructure.t -> relation

val fresh_configuration : EventStructure.t -> so_var
val forall : so_var -> Qbf.t -> Qbf.t
val exists : so_var -> Qbf.t -> Qbf.t
val equals_set : so_var -> EventStructure.set -> Qbf.t

val subset : relation
val equal : relation

val flip : relation -> relation
val intersect : relation -> relation -> relation
val union : relation -> relation -> relation

val intersect_n : relation list -> relation
val union_n : relation list -> relation

val fresh_relation : EventStructure.t -> so_var
val reflexive : EventStructure.t -> so_var predicate

(* When we introduce (existentially quantified) intermediate so_vars
we need to have access to a validity predicate. *)

val sequence : EventStructure.t -> relation -> relation -> relation
val at_most_n : EventStructure.t -> int -> relation -> relation

val set_of_model : so_var -> Qbf.model -> EventStructure.set

