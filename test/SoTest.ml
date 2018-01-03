open OUnit


let verbose = ref false

let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let test_suites =  [
  SOBasic.so_structure_tests
; SOBasic.so_formula_tests
; JRSO2Tests.tests
]

let () =
  Config.set_solver (Some Config.SolveSO);
  List.iter (fun t -> ignore @@ run_test_tt t ~verbose:(!verbose)) test_suites;
  Config.set_solver (Some Config.SolveQbf);
  List.iter (fun t -> ignore @@ run_test_tt t ~verbose:(!verbose)) test_suites
