module E = EventStructure
module GH = GraphHelpers

val build_so_structure : E.t -> E.event list list -> SO.relation SO.RelMap.t
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
val goal_constrain : E.event list list -> SO.so_var -> SO.formula

val name_final : int -> string
