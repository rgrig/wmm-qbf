open SO
open SoOps
   
let do_decide _ _  =
  let p1 = SO.mk_fresh_sv () in
  let p2 = SO.mk_fresh_sv () in
  let x = SO.mk_fresh_fv () in
  let f =
    SoAll (p1, 1,
    SoAny (p2, 1,
    FoAll (x,
           iff [QRel (p1, [Var x])]
               [QRel (p2, [Var x])]
          ) ) ) in
  let s = SO.{ size = 2; relations = RelMap.empty } in
  Printf.printf "%s" (SO.show_isabelle_structure "toy" s);
  Printf.printf "%s" (SO.show_isabelle_formula f)
  (*Printf.printf "result: %b\n%!" (SoOps.model_check s f)*)

