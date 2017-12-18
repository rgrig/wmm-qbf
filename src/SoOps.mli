open SO
val rels : (rel_sym * relation) list -> relation RelMap.t
val add_specials : structure -> structure

val check_inv : structure -> formula -> unit
val model_check : Qbf.checker_opts -> structure -> formula -> bool

val so_to_qbf : structure -> formula -> Qbf.t

(* [mk_implies [p1;p2] q] is (p₁ ∧ p₂) → q *)
val mk_implies : formula list -> formula -> formula
val mk_eq : term -> term -> formula
val subset : so_var -> so_var -> formula
val eq : so_var -> so_var -> formula

val intersect : so_var -> so_var -> so_var -> formula
val union : so_var -> so_var -> so_var -> formula

