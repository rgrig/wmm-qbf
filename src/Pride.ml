(* NOTE: This cannot go in [Config] because of cyclic module dependencies. *)
let available_models =
  ("j+r-so", JRSO.do_decide) (* default *)
  ::
  [
    (* "j+r", JR.do_decide*)
  (*
  "common-valid-conf", ValidConf.do_decide
  (* TODO  ; "j+r-enum", JR.do_enum *)
  ; "j+r-so", JRSO.do_decide
  ; "cat-sc", CatSC.do_decide
  ; "cat-ra", CatRA.do_decide 
  *)
    ("cat-cpp", CatCPP.do_decide)
  ]

let print_accept accept =
  Printf.eprintf "Execution can include events:  [%s]\n" (Util.map_join ", " (
      fun s -> "[" ^ (Util.map_join ", " string_of_int s) ^ "]"
    ) accept)

let run_on_es filename ch =
  Config.set_current_file filename;
  let es, accept = EsOps.parse filename ch in
  if (Config.verbose ()) then print_accept accept;

  (Config.model ()) es accept

let run_on_lisa filename ch =
  Config.set_current_file filename;
  let source = Lisa.read_to_eof ch in
  let litmus = Lisa.load_litmus source in
  (if Config.dump_lisa () then Lisa.print_litmus litmus);
  let min, max = Config.vals () in
  let es, accept = Translate.translate litmus min max in
  if (Config.verbose ()) then print_accept accept;
  (* TODO: A switch to dump the ES is some useful format. *)
  (* TODO: Find target executions. *)
  (Config.model ()) es accept

let run_on_file run filename =
  (match Util.on_channel filename (run filename) with
  | None -> Printf.eprintf "E: could not open %s\n" filename
  | Some () -> ())

let () =
  Config.parse_args available_models;
  if Config.verbose () then (
    Config.print_options ();
    flush stderr;
  );
  List.iter (run_on_file run_on_es) (Config.es_files ());
  List.iter (run_on_file run_on_lisa) (Config.lisa_files ())

