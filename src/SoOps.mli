open SO

(* For arities 1 and 2 we have special types because they are used so often.
Arity-1 relations are sometimes called "predicates"; arity-2 relations are
sometimes called just "relations". *)
type rel1 = SO.term -> SO.formula (* arity-1 relations *)
type rel2 = SO.term -> SO.term -> SO.formula (* arity-2 relations *)

val add_rel : relation RelMap.t -> (rel_sym * relation) -> relation RelMap.t
val rels : (rel_sym * relation) list -> relation RelMap.t

val add_specials : structure -> structure

val check_inv : structure -> formula -> unit
val model_check : structure -> formula -> bool

val so_to_qbf : structure -> formula -> Qbf.t
val dump: structure -> formula -> unit

(* [mk_implies [p1;p2] q] is (p₁ ∧ p₂) → q *)
val mk_implies : formula list -> formula -> formula
val mk_eq : rel2
val mk_fresh_reln : ?prefix:string -> unit -> SO.so_var * rel2
val mk_crel1 : string -> rel1
val mk_crel2 : string -> rel2
val mk_qrel1 : string -> SO.so_var * rel1
val mk_qrel2 : string -> SO.so_var * rel2
val subset : so_var -> so_var -> formula
val iff : formula list -> formula list -> formula
val eq : so_var -> so_var -> formula

(* TODO(rgrig): These should probably be refactored as combinators for arity-1
relations. *)
val intersect : so_var -> so_var -> so_var -> formula
val union : so_var -> so_var -> so_var -> formula

val eq_crel: so_var -> rel_sym -> formula

(* Combinators for arity-1 relations. *)
val and1 : rel1 list -> rel1
val or1 : rel1 list -> rel1

val set_intersect : rel1 list -> rel1 (* =and1 *)
val set_union : rel1 list -> rel1 (* =or1 *)

(* Combinators for arity-2 relations. *)
val r_tc: int -> rel2 -> rel2
val tc: int -> rel2 -> rel2
val invert : rel2 -> rel2
val maybe : rel2 -> rel2
val sequence : rel2 -> rel2 -> rel2
val sequence_n : rel2 list -> rel2
val rel_union : rel2 -> rel2 -> rel2
val rel_union_n : rel2 list -> rel2
val rel_intersect : rel2 -> rel2 -> rel2
val rel_minus: rel2 -> rel2 -> rel2

(* From arity-2 relations to formulas. *)
val rel_subset : rel2 -> rel2 -> formula
val rel_eq : rel2 -> rel2 -> formula
val rel_empty : rel2 -> formula
val transitive: rel2 -> formula
val irreflexive: rel2 -> formula
val acyclic: rel2 -> formula
val total : rel1 -> rel2 -> formula
  (* [total s r] says that r is total over all events in s *)

val eq_crel2: SO.so_var -> string -> SO.formula

val cross: (term -> formula) -> (term -> formula) -> term -> term -> formula
