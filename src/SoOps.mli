val rels : (SO.rel_sym * SO.relation) list -> SO.relation SO.RelMap.t

val check_inv : SO.structure -> SO.formula -> unit
val model_check : SO.structure -> SO.formula -> bool
