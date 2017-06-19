open Printf

module U = Util

let do_one fn =
  let wmm = U.parse fn in
  let ctx = U.mk_context wmm.Wmm.events in
  let start_var = U.mk_var "START" [1,ctx.U.n] in
  let end_var = U.mk_var "END" [1,ctx.U.n] in
  let q =
    let step1 = U.step1 wmm ctx in
    let c = U.at2 ctx.U.c_spec in
    let start_var = U.at1 start_var in
    let end_var = U.at1 end_var in
    Qbf.mk_and
    [ U.equal ctx start_var (c 0)
    ; U.equal ctx end_var (c 1)
    ; step1 c 1 ] in
  let q = Qbf.mk_and
    [ U.is_set ctx start_var [] (* wmm.Wmm.execution *)
    ; q ] in
  let q = U.add_validity wmm ctx q in
  let q = U.add_quantifiers ctx q in
  let q = Qbf.mk_exists (U.var_allnames start_var) q in
  let q = Qbf.mk_exists (U.var_allnames end_var) q in

  printf "%a" Qbf.pp_qcir q


let () =
  Arg.parse [] do_one "wmmEnum <infiles>"
