type worker = EventStructure.t -> EventStructure.set -> unit
type solver = SolveQbf | SolveSO

val model : unit -> worker
val dump_qbf : unit -> bool
val dump_query : unit -> bool
val dump_lisa : unit -> bool
val filename : unit -> string
val use_solver : unit -> solver option
val qbf_solver_bin : unit -> string
val so_solver_bin : unit -> string
val es_files : unit -> string list
val lisa_files : unit -> string list

val set_current_file : string -> unit
val set_solver : solver option -> unit

val parse_args : (string * worker) list -> unit
val show_solver : solver option -> string
