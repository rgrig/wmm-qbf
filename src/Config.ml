type worker = EventStructure.t -> EventStructure.set -> unit
type solver = SolveQbf | SolveSO

let dump_qbf_val = ref false
let dump_qbf () = !dump_qbf_val

let dump_query_val = ref false
let dump_query () = !dump_query_val

let dump_lisa_val = ref false
let dump_lisa () = !dump_lisa_val

let model_val = ref None
let model () = Util.from_some !model_val

let qbf_solver_bin_val = ref "qfun-enum"
let qbf_solver_bin () = !qbf_solver_bin_val

let so_solver_bin_val = ref "qfm"
let so_solver_bin () = !so_solver_bin_val

let use_solver_val = ref (Some SolveQbf)
let use_solver () = !use_solver_val

let use_lisa_val = ref false
let use_lisa () = !use_lisa_val

let es_files_val = ref []
let es_files () = !es_files_val

let lisa_files_val = ref []
let lisa_files () = !lisa_files_val

let filename_val = ref ""
let filename () = !filename_val
let set_current_file f = filename_val := f

let list_models ms () =
  let one (name, _) = Printf.eprintf "%s\n" name in
  List.iter one ms

let choose_model available_models name =
  try model_val := Some (List.assoc name available_models)
  with Not_found -> Printf.eprintf "E: unrecognized model name: %s\n" name

let default_solver = Some SolveQbf
let solver_of_string = function
    "qbf" | "QBF" -> Some SolveQbf
  | "so"  | "SO"  -> Some SolveSO
  | "none" -> None
  | _ -> default_solver

let set_solver s = use_solver_val := s
let choose_solver name = set_solver (solver_of_string name)


let show_solver = function
    Some SolveQbf -> "qbf"
  | Some SolveSO -> "so"
  | None -> "no solver"

let command_spec available_models =
  Arg.align
  [ "--use-lisa", Arg.Set use_lisa_val,
    "  use LISA as input language for test"
  ; "--dump-lisa", Arg.Set dump_lisa_val,
    "  print the LISA AST"
  ; "--dump-qbf", Arg.Set dump_qbf_val,
    "  print QBF query before executing"
  ; "--dump-query", Arg.Set dump_query_val,
    "  print query before executing"
  ; "--model", Arg.String (choose_model available_models),
    "  pick a model"
  ; "--list-models", Arg.Unit (list_models available_models),
    "  print list of models"
  ; "--qbf-solver-path", Arg.String ((:=) qbf_solver_bin_val),
    "  set the path to the Qbf solver binary"
  ; "--so-solver-path", Arg.String ((:=) so_solver_bin_val),
    "  set the path to the SO solver binary"  
  ; "--solver", Arg.String choose_solver,
      "  pick the solver type to use. (default: " ^ (show_solver default_solver) ^ ")"]

let parse_args (available_models : (string * worker) (*nonempty*) list) =
  model_val := Some (snd (List.hd available_models));
  let command_spec = command_spec available_models in
  es_files_val := [];
  lisa_files_val := [];
  let record_file name = match Filename.extension name with
    | ".es" -> es_files_val := name :: !es_files_val
    | ".lisa" -> lisa_files_val := name :: !lisa_files_val
    | _ -> Printf.eprintf "W: unrecognized extension, ignoring %s\n" name in
  let usage = Printf.sprintf "%s <files>" Sys.executable_name in
  Arg.parse command_spec record_file usage

