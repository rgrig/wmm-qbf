open PES
open Printf

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target =
  let c = MM.fresh_so_var es 1 ~prefix:"conf" in
  let q = Qbf.mk_and [
      MM.equals_set c [1;2]
    ; follows_config es c 3
    ] in
  let q = MM.exists c q in
  match Config.use_solver () with
    Some (Config.SolveQbf) -> printf "result: %b\n" (Qbf.holds q)
  | Some _ -> failwith "This model requires the Qbf solver."
  | _ -> ()
