type event_setset = EventStructure.set list

val build_so_structure
  : EventStructure.t -> event_setset -> SO.relation SO.RelMap.t
val sos_of_es : EventStructure.t -> event_setset -> SO.structure

val maximal : SO.so_var -> SO.formula
val rf_constrain :
  (SO.term -> SO.formula) ->
  (SO.term -> SO.term -> SO.formula) ->
  (SO.term -> SO.term -> SO.formula) ->
  SO.formula

val co_constrain :
  (SO.term -> SO.formula) ->
  (SO.term -> SO.term -> SO.formula) ->
  SO.formula
val goal_constrain : event_setset -> SO.so_var -> SO.formula

val name_final : int -> string

(* Relations used in many CAT memory models. *)
val get_co : unit -> SO.so_var * SoOps.rel2
val get_hb : unit -> SO.so_var * SoOps.rel2
val get_po : unit -> SO.rel_sym * SoOps.rel2
val get_rf : unit -> SO.so_var * SoOps.rel2
val get_w : unit -> SO.rel_sym * SoOps.rel1
