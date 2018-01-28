module E = EventStructure
module GH = GraphHelpers
open SO
open SoOps
open CatCommon

type reln = fo_var -> fo_var -> formula

let intersect a b =
    List.filter (fun x -> List.mem x a) b

let fr rf co = (sequence (invert rf) co)

let com rf co fr = rel_union (rel_union rf co) fr

let po_loc po = rel_intersect po (fun a b -> CRel ("sloc", [a;b]))
             
let cat_constrain rf co po =
  let fr = fr rf co in
  And [
    acyclic (rel_union (com rf co fr) (po_loc po))
  ; acyclic (rel_union po rf)
  ]

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
          ; CatCommon.rf_constrain g rf
              (rel_intersect
                 (curry_crel "justifies")
                 (cross g g)
              )
          ; CatCommon.co_constrain g co
          ; rel_subset co (cross g g)
          ; rel_subset rf (cross g g)

          ; cat_constrain rf co po
          ]
        )
      )
    )
  in

  let s = {
      size = size;
      relations = CatCommon.build_so_structure
          E.{ es with
              na = []
            ; rel = es.reads
            ; acq = List.filter (fun e -> not (List.mem e es.reads)) (Util.range 1 es.events_number)
            }
          accept
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then SoOps.dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)
