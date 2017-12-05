(* This test program takes one file as an argument and dumps the parsed LISA. *)
(* It's designed as a temporary tool for checking the syntax of litmus files. *)
(* This should become obsolete once the LISA parser is properly wired up. *)

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
