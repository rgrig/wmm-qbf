(* Parses results from the QBF solver *)

let re_model = Str.regexp "^v.*$"
let re_var = Str.regexp "\\+\\([a-zA-Z0-9_]+\\)"
let parse_models data =
  (* TODO: Someone who understands what the models in question are should check this explanation. *)
  (* Returns a list of variables found in data within the given range, accumulating list in found. *)
  let rec find_vars (start_index : int) (end_index : int) (found : string list) : string list =
    try
      (* Find next variable. *)
      let var_start = Str.search_forward re_var data start_index in
      let var_end = Str.match_end () in
      let var = String.sub data var_start (var_end - var_start) in

      (* Accumulate variables. *)
      find_vars var_end end_index (var::found)
    (* Done. *)
    with Not_found -> found
  in

  (* TODO: Someone who understands what the models in question are should check this explanation. *)
  (* Returns a list of models found in data, starting from index, accumulating list in found. *)
  (* Each model is represented as a list of variables. *)
  let rec find_models (start_index : int) (found : string list list) : string list list =
    try
      (* Find line containing model data. *)
      let model_start = Str.search_forward re_model data start_index in
      let model_end = Str.match_end () in

      (* Find vars in this model. *)
      let model = find_vars model_start model_end [] in

      (* Accumulate models. *)
      find_models model_end (model::found)
    (* Done. *)
    with Not_found -> found
  in
  
  find_models 0 []


let run_also program data =
  RunSolver.run_program program [||] data

(* TODO: Is there a way to detect if the output is malformed due to errors? *)
let parse_answer =
  let re_yes_answer = Str.regexp "^s cnf 1\\|Satisfiable" in
  fun data -> begin
    (match (Config.run_also ()) with
      | "" -> ()
      | p -> Printf.eprintf "%s:\n%s\n" p (run_also p data));
    (try ignore (Str.search_forward re_yes_answer data 0); true
    with Not_found -> false)
  end
