type worker = EventStructure.t -> EventStructure.set list -> unit
type solver = SolveQbf | SolveSO | SolveNitpick

val model : unit -> worker
val dump_es : unit -> bool
val dump_qbf : unit -> bool
val dump_query : unit -> bool
val dump_lisa : unit -> bool
val filename : unit -> string
val use_solver : unit -> solver option
val qbf_solver_bin : unit -> string
val run_also : unit -> string
val so_solver_bin : unit -> string
val so_solver_opts : unit -> string list
val verbose : unit -> bool
val vals : unit -> int * int
val es_files : unit -> string list
val lisa_files : unit -> string list

val set_current_file : string -> unit
val set_solver : solver option -> unit

val parse_args : (string * worker) list -> unit
val show_solver : solver option -> string
val print_options : unit -> unit
