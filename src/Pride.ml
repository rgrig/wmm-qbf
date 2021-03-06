(* NOTE: This cannot go in [Config] because of cyclic module dependencies. *)
let available_models : (string * Config.worker) list =
  ("j+r-so", JRSO.do_decide) (* default *)
  ::
  [ (* TODO(rgrig): Are these all supposed to be [na_do_decide]? *)
    "cat-cpp-na", CatCPP.na_do_decide
  ; "cat-cpp-rlx", CatCPP.na_do_decide
  ; "cat-cpp-ra", CatCPP.na_do_decide
  ; "cat-cpp-sc", CatCPP.na_do_decide
  ; "rc11-simple", CatCPP.simple_do_decide
  ; "cat-ra", CatRA.do_decide
  ; "cat-sc", CatSC.do_decide

  ; "so-toy", SOToy.do_decide
  ]

let print_accept accept =
  Printf.eprintf "Execution can include events:  [%s]\n" (Util.map_join ", " (
      fun s -> "[" ^ (Util.map_join ", " string_of_int s) ^ "]"
    ) accept)

let run_on_es filename ch =
  Config.set_current_file filename;
  let es, accept = EsOps.parse filename ch in
  let es = EventStructure.apply_axioms es in
  if (Config.verbose ()) then (
    Printf.eprintf "  Model size:  %d"  es.EventStructure.events_number;
    flush stderr;
    print_accept accept;
  );
  (Config.model ()) es accept

let run_on_lisa filename ch =
  Config.set_current_file filename;
  let source = Lisa.read_to_eof ch in
  let litmus = Lisa.load_litmus source in
  (if Config.dump_lisa () then Lisa.print_litmus litmus);
  let min, max = Config.vals () in
  let es, accept, labels = Translate.translate litmus min max in
  let es = EventStructure.apply_axioms es in
  if (Config.dump_es ()) then EventStructure.dump filename es accept labels;
  if (Config.verbose ()) then (
    Printf.eprintf "  Model size:  %d\n"  es.EventStructure.events_number;
    flush stderr;
    print_accept accept;
  );
  (Config.model ()) es accept

let run_on_file run filename =
  (match Util.on_channel filename (run filename) with
  | None -> Printf.eprintf "E: could not open %s\n" filename
  | Some () -> ())

let () =
  Config.parse_args available_models;
  if Config.verbose () then Config.print_options ();
  List.iter (run_on_file run_on_es) (Config.es_files ());
  List.iter (run_on_file run_on_lisa) (Config.lisa_files ())

