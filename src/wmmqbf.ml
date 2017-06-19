open Printf

module U = Util

let do_one fn =
  let wmm = U.parse fn in
  let ctx = U.mk_context wmm.Wmm.events wmm.Wmm.events in
  let start_var = U.mk_var "START" [1,ctx.U.n] in
  let end_var = U.mk_var "END" [1,ctx.U.n] in
  let q =
    let step1 = U.step1 wmm ctx in
    let c = U.at2 ctx.U.c_spec in
    let start_var = U.at1 start_var in
    let end_var = U.at1 end_var in
    U.transitive_closure ctx step1 start_var c end_var in
  let q = Qbf.mk_and
    [ U.is_set ctx start_var []
    ; U.is_set ctx end_var wmm.Wmm.execution
    ; q ] in
  let q = U.add_validity wmm ctx q in
  let q = U.add_quantifiers ctx q in
  let q = Qbf.mk_exists (U.var_allnames start_var) q in
  let q = Qbf.mk_exists (U.var_allnames end_var) q in

  printf "%a" Qbf.pp_qcir q

let () =
  Arg.parse [] do_one "wmmqbf <infile>"
