module E = EventStructure
open SO
open SoOps

type reln = fo_var -> fo_var -> formula

let fr rf co = (sequence (invert rf) co)

let com rf co fr = rel_union (rel_union rf co) fr

let cat_constrain rf co fr po =
  acyclic (rel_union (com rf co fr) po)

let conflict_free c =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (
    x,
    FoAll (
      y,
      (mk_implies [
          QRel (c, [Var x])
        ; QRel (c, [Var y])
        ] (Not (Or [
          CRel ("conflict", [Var x; Var y])
        ; CRel ("conflict", [Var x; Var y])
        ]
        ))
      )
    )
  )

let maximal c =
  let c' = mk_fresh_sv () in
  SoAny (
    c', 1,
    mk_implies [
      conflict_free c
    ; conflict_free c'
    ; subset c c'
    ] (subset c' c)
  )

let constrain_goal g =
  let x = mk_fresh_fv () in
  FoAll (
    x,
    And [
      mk_implies [CRel ("can", [Var x])] (QRel (g, [Var x]))
    ; mk_implies [QRel (g, [Var x])] (CRel ("must", [Var x]))
    ]
  )

let do_decide es can must =
  let size = es.E.events_number in
  let curry_crel name a b = CRel (name, [a; b]) in
  let g = mk_fresh_sv () in
  let rf_id, rf = mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = mk_fresh_reln ~prefix:"do_decide_co" () in
  let f =
    SoAny (
      g, 1,
      SoAny (
        co_id, 2,
        SoAny (
          rf_id, 2,
          And [
            constrain_goal g
          ; CatCommon.rf_constrain rf (curry_crel "justifies")
          ; cat_constrain rf co (fr rf co) (curry_crel "order")
          ; CatCommon.co_constrain co
          ]
        )
      )
    )
  in

  let s = {
      size = size;
      relations = CatCommon.build_so_structure es can must
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

