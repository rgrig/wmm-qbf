open OUnit


let test_verbose = ref false

let options = Arg.align [("--test-verbose", Arg.Set test_verbose, "run tests with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let test_suites =  [
  SOBasic.so_structure_tests
; SOBasic.so_formula_tests
; JRSO2Tests.tests
]

let () =
  Config.parse_args Pride.available_models;
  Config.set_current_file ".test";

  Printf.printf "Running with SO Solver\n";
  Printf.printf "======================\n";
  Config.set_solver (Some Config.SolveSO);
  List.iter (fun t -> ignore @@ run_test_tt t ~verbose:(!test_verbose)) test_suites;

  Printf.printf "Running with QBF Solver\n";
  Printf.printf "=======================\n";
  Config.set_solver (Some Config.SolveQbf);
  List.iter (fun t -> ignore @@ run_test_tt t ~verbose:(!test_verbose)) test_suites
