open SO
val add_rel : relation RelMap.t -> (rel_sym * relation) -> relation RelMap.t
val rels : (rel_sym * relation) list -> relation RelMap.t

val add_specials : structure -> structure

val check_inv : structure -> formula -> unit
val model_check : structure -> formula -> bool

val so_to_qbf : structure -> formula -> Qbf.t
val dump: structure -> formula -> unit

(* [mk_implies [p1;p2] q] is (p₁ ∧ p₂) → q *)
val mk_implies : formula list -> formula -> formula
val mk_eq : term -> term -> formula
val mk_fresh_reln : ?prefix:string -> unit -> SO.so_var * (SO.term -> SO.term -> SO.formula)
val subset : so_var -> so_var -> formula
val iff : formula list -> formula list -> formula
val eq : so_var -> so_var -> formula

val intersect : so_var -> so_var -> so_var -> formula
val union : so_var -> so_var -> so_var -> formula

val eq_crel: so_var -> rel_sym -> formula

val invert : (term -> term -> formula) -> term -> term -> formula
val sequence : (term -> term -> formula) -> (term -> term -> formula) -> term -> term -> formula
val rel_union : (term -> term -> formula) -> (term -> term -> formula) -> term -> term -> formula
val rel_intersect : (term -> term -> formula) -> (term -> term -> formula) -> term -> term -> formula
val rel_subset : (term -> term -> formula) -> (term -> term -> formula) -> formula
val rel_eq : (term -> term -> formula) -> (term -> term -> formula) -> formula

val r_tc: int -> (term -> term -> formula) -> term -> term -> formula
val tc: int -> (term -> term -> formula) -> term -> term -> formula

val transitive: (term -> term -> formula) -> formula
val irreflexive: (term -> term -> formula) -> formula
val acyclic: (term -> term -> formula) -> formula

val eq_crel2: SO.so_var -> string -> SO.formula
