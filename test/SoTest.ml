open OUnit


let verbose = ref false

let t1 = "t1" >:: (fun () ->
  let s =
    { SO.size = 3
    ; relations = SoOps.rels [("foo", [[]])]  } in
  let f = SO.CRel ("foo", []) in
  SoOps.check_inv s f
)


let test_suite = "so" >::: [t1]

let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let _ = run_test_tt test_suite ~verbose:(!verbose)

