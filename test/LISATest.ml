(* This test program takes one file as an argument and dumps the parsed LISA. *)
(* It's designed as a temporary tool for checking the syntax of litmus files. *)
(* This should become obsolete once the LISA parser is properly wired up. *)
open EventStructure
open Translate

let verbose = ref false

let print_an name =
  let open Printf in
  let pone f = printf " %d" in
  let plist f = printf "  %a\n" (Util.hp_list pone) in
  printf "%s\n%a" name (Util.hp_list plist)

let print_a2 name pairs =
  print_an name @@ List.map (fun (x, y) -> [x; y]) pairs

let print_a1 name elements =
  print_an name @@ List.map (fun x -> [x]) elements

let es_of_lisa lisa_filename =
  let lisa_text = Wrapper.read_to_eof (open_in lisa_filename) in
  let init, _, program, _ = Wrapper.load_litmus lisa_text in
  let events = Translate.translate init program 0 1 in
  let open Printf in
  printf "events %d\n" events.events_number;
  print_a2 "sloc" events.sloc;
  print_a1 "reads" events.reads;
  printf "labels\n";
  for i = 1 to events.events_number do
    printf "  %d \"TODO\"\n" i
  done;
  print_a2 "justifies" events.justifies;
  print_a2 "conflicts" events.conflicts;
  print_a2 "order" events.order;
  printf "execution\n"

let args = Arg.
  [ "-v", Set verbose, "be verbose" ]


let () =
  Arg.parse args es_of_lisa "Translates LISA to event structures."
