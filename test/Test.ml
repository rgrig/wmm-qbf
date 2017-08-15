open OUnit

let verbose = ref false;;

   
let test_suite = "" >::: MMTest.tests;;
let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;
               
let _ = Arg.parse options (fun _ -> ()) ""
  
let _ = run_test_tt test_suite ~verbose:(!verbose)
      
