module E = EventStructure
open SO
open SoOps

type reln = fo_var -> fo_var -> formula

let fr rf co = sequence (invert rf) co

let com rf co fr = rel_union (rel_union rf co) fr

let cat_constrain rf co po =
  let fr = fr rf co in
  acyclic (rel_union (com rf co fr) po)

let do_decide es accept =
  let size = es.E.events_number in
  let curry_crel name a b = CRel (name, [a; b]) in
  let g_id = mk_fresh_sv ~prefix:"execution" () in
  let g x = QRel (g_id, [x]) in
  let rf_id, rf = mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = mk_fresh_reln ~prefix:"do_decide_co" () in
  let po = rel_intersect (rel_minus (curry_crel "order") mk_eq) (cross g g) in
  let f =
    SoAny (
      g_id, 1,
      SoAny (
        co_id, 2,
        SoAny (
          rf_id, 2,
          And [
            CatCommon.goal_constrain accept g_id
          ; JRSO.valid g_id
          ; CatCommon.rf_constrain g rf (curry_crel "justifies")
          ; CatCommon.co_constrain g co
          ; cat_constrain rf co po
          ]
        )
      )
    )
  in

  let s = {
      size = size;
      relations = CatCommon.build_so_structure es accept
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

