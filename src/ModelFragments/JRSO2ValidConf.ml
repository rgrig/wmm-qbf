open SO
open SoOps
open JRSO2

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target =
  let size = es.E.events_number in
  let x = mk_fresh_sv () in
  let f =
    SoAny (x, 1,
           And [
             eq_crel x "target"
           ; valid x ]
          )
  in
  let s = { SO.size = size; SO.relations = build_so_structure es target } in
  if Config.dump_query () then (
    let basename = Filename.remove_extension (Config.filename ()) in
    let f_c = open_out (basename ^ ".sol") in
    Printf.fprintf f_c "%s\n" (show_formula f); 
    close_out f_c;

    let s_c = open_out (basename ^ ".str") in
    Printf.fprintf s_c "%s\n" (show_structure s);
    close_out s_c;
  );
  Printf.printf "result: %b\n" (SoOps.model_check s f)

