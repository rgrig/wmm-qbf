(* WIP fix for wmm-qbf to make it use pipes. *)
(* NOTE: This is likely only to work on POSIX. *)

(* Call the solver as a subprocess, passing it the given input. *)
(* Either returns the resulting output or throws SubprocessFailed if the process writes to stderr. *)
val run_solver: string -> string
