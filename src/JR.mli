val always_justifies : EventStructure.t -> MM.relation
val always_justifies_tc : EventStructure.t -> MM.relation
val always_eventually_justifies : EventStructure.t -> MM.relation
val always_eventually_justifies_tc : EventStructure.t -> MM.relation

val do_enum: string -> EventStructure.t -> EventStructure.set option -> unit
val do_decide: string -> EventStructure.t -> EventStructure.set -> unit
