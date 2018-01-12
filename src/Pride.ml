(* NOTE: This cannot go in [Config] because of cyclic module dependencies. *)
let available_models =
  ("j+r", JR.do_decide) (* default *)
  ::
  [ "common-valid-conf", ValidConf.do_decide
(* TODO  ; "j+r-enum", JR.do_enum *)
  ; "j+r-so", JRSO.do_decide
  ; "j+r-so2", JRSO2.do_decide
  ; "j+r-so2-valid-conf", JRSO2ValidConf.do_decide
  ; "pes", PES.do_decide
  ; "pes-certifies", PESCertifies.do_decide
  ; "pes-follows", PESFollows.do_decide
  ; "pes-make-promise", PESMakePromise.do_decide
  ; "pes-promise-read", PESPromiseRead.do_decide
  ; "pes-transitions", PESTransitions.do_decide
  ; "cat-sc", CatSC.do_decide
  ; "cat-ra", CatRA.do_decide
  ; "cat-cpp", CatCPP.do_decide
  ]

let run_on_es filename ch =
  Config.set_current_file filename;
  match EsOps.parse filename ch with
  | _, None -> Printf.eprintf "W: no target execution: skipping %s" filename
  | es, Some target -> (Config.model ()) es target

let run_on_lisa filename ch =
  let source = Wrapper.read_to_eof ch in
  let ast = Wrapper.load_litmus source in
  (if Config.dump_lisa () then Wrapper.print_litmus ast);
  let (init, _, program, _) = ast in
  let min, max = Config.vals () in
  let es = Translate.translate init program min max in
  (* TODO: A switch to dump the ES is some useful format. *)
  (* TODO: Find target executions. *)
  ignore es

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

