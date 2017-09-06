type so_var

(* We're going to have predicates on so_vars, like
   down-closed, and predicates on relations like acyclic *)
type 'a predicate = 'a -> Qbf.t
type relation = so_var -> so_var -> Qbf.t

val size_of : so_var -> int

val justifies : EventStructure.t -> relation
val valid_conf : EventStructure.t -> so_var predicate
val valid_rel : EventStructure.t -> relation

val fresh_so_var : ?prefix:string -> EventStructure.t -> int -> so_var
val writes : EventStructure.t -> so_var predicate
val forall : so_var -> Qbf.t -> Qbf.t
val exists : so_var -> Qbf.t -> Qbf.t
val equals_set : so_var -> EventStructure.set -> Qbf.t
val _in: int list -> so_var -> Qbf.t

val subset : relation
val equal : relation

val flip : relation -> relation
val intersect : relation -> relation -> relation
val union : relation -> relation -> relation

val intersect_n : relation list -> relation
val union_n : relation list -> relation

val reflexive : EventStructure.t -> so_var predicate

(* When we introduce (existentially quantified) intermediate so_vars
we need to have access to a validity predicate. *)

val sequence : EventStructure.t -> relation -> relation -> relation
val at_most_n : EventStructure.t -> int -> relation -> relation
val same_label : EventStructure.t -> int -> int -> bool
val set_of_model : so_var -> Qbf.model -> EventStructure.set

(**/**)
(* Section ignored by ocamldoc *)

val test_sizeof: OUnit.test
val test_name: OUnit.test
val test_var: OUnit.test
val test_subset: OUnit.test
val test_subset2: OUnit.test
val test_subset_r: OUnit.test
val test_flip: OUnit.test
val test_equal: OUnit.test
val test_union: OUnit.test
