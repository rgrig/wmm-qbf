type worker = EventStructure.t -> EventStructure.set -> unit

val model : unit -> worker
val dump_qbf : unit -> bool
val dump_query : unit -> bool
val dump_lisa : unit -> bool
val use_solver : unit -> bool
val es_files : unit -> string list
val lisa_files : unit -> string list

val set_current_file : string -> unit
val filename : unit -> string

val parse_args : (string * worker) list -> unit
