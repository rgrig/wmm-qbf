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
             
let cat_constrain rf co fr po =
  And [
    acyclic (rel_union (com rf co fr) (po_loc po))
  ; acyclic (rel_union po rf)
  ]

let do_decide es accept =
  let size = es.E.events_number in
  let curry_crel name a b = CRel (name, [a; b]) in
  let rf_id, rf = mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = mk_fresh_reln ~prefix:"do_decide_co" () in
  let f =
    SoAny (
      co_id, 2,
      SoAny (
        rf_id, 2,
        And [
          rf_constrain rf (curry_crel "justifies")
        ; cat_constrain rf co (fr rf co) (curry_crel "order")
        ; co_constrain co
        ; eq_crel2 co_id "co"
        ; eq_crel2 rf_id "rf"
        ]
      )
    )
  in

  let s = {
      size = size;
      relations = CatCommon.build_so_structure es accept
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then SoOps.dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)
