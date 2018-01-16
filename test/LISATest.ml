let verbose = ref false

let print_an ?(decoration = "") name =
  let open Printf in
  let pone f x = printf " %d%s" x decoration in
  let plist f = printf "  %a\n" (Util.hp_list pone) in
  printf "%s\n%a" name (Util.hp_list plist)

let print_a2 name pairs =
  print_an name @@ List.map (fun (x, y) -> [x; y]) pairs

let print_a1 ?(decoration="") name elements =
  print_an ~decoration name @@ List.map (fun x -> [x]) elements

let es_of_lisa lisa_filename =
  let lisa_text = Lisa.read_to_eof (open_in lisa_filename) in
  let litmus = Lisa.load_litmus lisa_text in
  if !verbose then Lisa.print_litmus litmus;
  let es, can_execute, must_execute = Translate.translate litmus 0 1 in
  let open EventStructure in
  Printf.printf "events %d\n" es.events_number;
  print_a2 "sloc" es.sloc;
  print_a1 "reads" es.reads;
  print_a1 "labels" (get_events es) ~decoration:" \"TODO\"";
  print_a2 "justifies" es.justifies;
  print_a2 "conflicts" es.conflicts;
  print_a2 "order" es.order;
  print_a1 "mustExecute" must_execute;
  print_a1 "canExecute" (get_events es)

let args = Arg.
  [ "-v", Set verbose, "be verbose"
  ; "--debug-translate", Set Translate.debug, "debug translation" ]

let () =
  Arg.parse args es_of_lisa "Translates LISA to event structures."
