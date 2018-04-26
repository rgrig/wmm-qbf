open SO

type rel1 = SO.term -> SO.formula
type rel2 = SO.term -> SO.term -> SO.formula

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
val mk_crel1 : string -> SO.rel_sym * rel1
val mk_crel2 : string -> SO.rel_sym * rel2
val mk_qrel2 : string -> SO.so_var * rel2
val subset : so_var -> so_var -> formula
val iff : formula list -> formula list -> formula
val eq : so_var -> so_var -> formula

val intersect : so_var -> so_var -> so_var -> formula
val union : so_var -> so_var -> so_var -> formula

val eq_crel: so_var -> rel_sym -> formula

val invert : rel2 -> rel2
val sequence : rel2 -> rel2 -> rel2
val rel_union : rel2 -> rel2 -> rel2
val rel_intersect : rel2 -> rel2 -> rel2

val rel_subset : rel2 -> rel2 -> formula
val rel_eq : rel2 -> rel2 -> formula

val r_tc: int -> rel2 -> rel2
val tc: int -> rel2 -> rel2

val transitive: rel2 -> formula
val irreflexive: rel2 -> formula
val acyclic: rel2 -> formula

val eq_crel2: SO.so_var -> string -> SO.formula

val rel_minus: rel2 -> rel2 -> rel2

val cross: (term -> formula) -> (term -> formula) -> term -> term -> formula
