val rels : (SO.rel_sym * SO.relation) list -> SO.relation SO.RelMap.t
val add_specials : SO.structure -> SO.structure

val check_inv : SO.structure -> SO.formula -> unit
val model_check : (bool * bool * bool) -> SO.structure -> SO.formula -> unit

val so_to_qbf : SO.structure -> SO.formula -> Qbf.t

(* [mk_implies [p1;p2] q] is (p₁ ∧ p₂) → q *)
val mk_implies : SO.formula list -> SO.formula -> SO.formula
val mk_eq : SO.term -> SO.term -> SO.formula
val subset : SO.so_var -> SO.so_var -> SO.formula
val intersect : SO.fo_var -> SO.fo_var -> SO.fo_var -> SO.formula
val eq : SO.so_var -> SO.so_var -> SO.formula
