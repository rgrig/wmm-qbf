open SO
val add_rel : relation RelMap.t -> (rel_sym * relation) -> relation RelMap.t
val rels : (rel_sym * relation) list -> relation RelMap.t

val add_specials : structure -> structure

val check_inv : structure -> formula -> unit
val model_check : structure -> formula -> bool

val so_to_qbf : structure -> formula -> Qbf.t

(* [mk_implies [p1;p2] q] is (p₁ ∧ p₂) → q *)
val mk_implies : formula list -> formula -> formula
val mk_eq : term -> term -> formula
val subset : so_var -> so_var -> formula
val eq : so_var -> so_var -> formula

val intersect : so_var -> so_var -> so_var -> formula
val union : so_var -> so_var -> so_var -> formula

val eq_crel: SO.so_var -> SO.rel_sym -> SO.formula
