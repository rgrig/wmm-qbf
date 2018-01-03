val dump_lisa : unit -> bool
val dump_query : unit -> bool
val qbf_dump : unit -> bool
val qbf_prenex : unit -> bool
val use_solver : unit -> bool

val es_files : unit -> string list
val lisa_files : unit -> string list

val set_current_file : string -> unit
val filename : unit -> string

type worker = EventStructure.t -> EventStructure.set -> unit
val model : unit -> worker
val parse_args : (string * worker) list -> unit
