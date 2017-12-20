open PES
open Printf

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target =
  let g = MM.fresh_so_var es 1 ~prefix:"goal" in
  let q = Qbf.mk_and [
      MM.equals_set g target
    ; certifiable es 2 g
    ] in
  let q = MM.exists g q
  in
  match Config.use_solver () with
    Some (Config.SolveQbf) -> printf "result: %b\n" (Qbf.holds q)
  | Some _ -> failwith "This model requires the Qbf solver."
  | None -> ()
