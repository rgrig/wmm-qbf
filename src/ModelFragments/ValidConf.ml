open PES
open Printf


(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target solver_opts =
  let c = MM.fresh_so_var es 1 ~prefix:"conf" in
  let p = MM.fresh_so_var es 1 ~prefix:"proms" in  
  let g = MM.fresh_so_var es 1 ~prefix:"goal" in
  let q = Qbf.mk_and [
      MM.equals_set g target
    ; MM.valid_conf es g
    ] in
  let q = MM.exists c
    @@ MM.exists p
    @@ MM.exists g q
  in
  Util.maybe (Qbf.holds q solver_opts) (printf "result: %b\n")
