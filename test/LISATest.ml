(* This test program takes one file as an argument and dumps the parsed LISA. *)
(* It's designed as a temporary tool for checking the syntax of litmus files. *)
(* This should become obsolete once the LISA parser is properly wired up. *)
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
  let lisa_text = Wrapper.read_to_eof (open_in lisa_filename) in
  let init, _, program, condition = Wrapper.load_litmus lisa_text in
  let es = Translate.translate init program 0 1 in
  let module ES = EventStructure in
  Printf.printf "events %d\n" (ES.events_number es);
  print_a2 "sloc" (ES.sloc es);
  print_a1 "reads" (ES.reads es);
  print_a1 "labels" (ES.events es) ~decoration:" \"TODO\"";
  print_a2 "justifies" (ES.justifies es);
  print_a2 "conflicts" (ES.conflicts es);
  print_a2 "order" (ES.order es);
  Printf.printf "execution\n"

let args = Arg.
  [ "-v", Set verbose, "be verbose"
  ; "--debug-translate", Set Translate.debug, "debug translation" ]


let () =
  Arg.parse args es_of_lisa "Translates LISA to event structures."
