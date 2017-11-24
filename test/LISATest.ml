(* This test program takes one file as an argument and dumps the parsed LISA. *)
(* It's designed as a temporary tool for checking the syntax of litmus files. *)
(* This should become obsolete once the LISA parser is properly wired up. *)

let program = Array.get Sys.argv 0
let _ = if (Array.length Sys.argv) != 2 then Format.printf "Usage: %s filename\n" program
let filename = Array.get Sys.argv 1
let litmus = Wrapper.load_litmus filename
let _ = Wrapper.print_litmus litmus
