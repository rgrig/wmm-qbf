(* This test program takes one file as an argument and dumps the parsed LISA. *)
(* It's designed as a temporary tool for checking the syntax of litmus files. *)
(* This should become obsolete once the LISA parser is properly wired up. *)
open EventStructure
open Translate

let rec repeat action times =
  action times;
  if times <= 1 then () else repeat action (times - 1)

let program = Array.get Sys.argv 0
let _ = if (Array.length Sys.argv) != 2 then begin
  Format.printf "Usage: %s filename\n" program;
  exit 0
end
let filename = Array.get Sys.argv 1
let _ = Printf.printf "Reading file %s\n" filename
let source = Wrapper.read_to_eof (open_in filename)
let _ = Printf.printf "Dumping input...\n\n%s\n" source
let litmus = Wrapper.load_litmus source
let _ = Wrapper.print_litmus litmus
let (init, _, program, _) = litmus
let events = Translate.translate init program 0 1
let _ = Printf.printf "events %d\n" events.events_number
let reads_string = List.map (fun read -> string_of_int read) events.reads
let _ = Printf.printf "reads %s\n" (String.concat " " reads_string)
let _ = Printf.printf "labels\n"
let _ = repeat (fun index -> Printf.printf "  %d \"TODO\"\n" index) events.events_number
let _ = Printf.printf "justifies\n"
let _ = List.iter (fun (a, b) -> Printf.printf "  %d %d\n" a b) events.justifies
let _ = Printf.printf "conflicts\n"
let _ = List.iter (fun (a, b) -> Printf.printf "  %d %d\n" a b) events.conflicts
let _ = Printf.printf "order\n"
let _ = List.iter (fun (a, b) -> Printf.printf "  %d %d\n" a b) events.order
let _ = Printf.printf "execution\n"
let _ = Printf.printf "sloc\n"
let _ = List.iter (fun (a, b) -> Printf.printf "  %d %d\n" a b) events.sloc
