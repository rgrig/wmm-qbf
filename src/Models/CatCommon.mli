type event_setset = EventStructure.set list

val build_so_structure
  : EventStructure.t -> event_setset -> SO.relation SO.RelMap.t
val sos_of_es : EventStructure.t -> event_setset -> SO.structure

val maximal : SO.so_var -> SO.formula
val rf_constrain : SoOps.rel1 -> SoOps.rel2 -> SO.formula
val co_constrain : SoOps.rel1 -> SoOps.rel2 -> SO.formula
val valid : SO.so_var -> SO.formula
val goal_constrain : event_setset -> SO.so_var -> SO.formula

val name_final : int -> string

(* Relations used in many CAT memory models. *)
val get_acq : unit -> SoOps.rel1
val get_cause : unit -> SO.so_var * SoOps.rel2
val get_co : unit -> SO.so_var * SoOps.rel2
val get_goal : unit -> SO.so_var * SoOps.rel1
val get_hb : unit -> SO.so_var * SoOps.rel2
val get_na : unit -> SoOps.rel1
val get_po : unit -> SoOps.rel2
val get_r : unit -> SoOps.rel1
val get_rel : unit -> SoOps.rel1
val get_rf : unit -> SO.so_var * SoOps.rel2
val get_rlx : unit -> SoOps.rel1
val get_sc : unit -> SoOps.rel1
val get_sloc : unit -> SoOps.rel2
val get_w : unit -> SoOps.rel1
