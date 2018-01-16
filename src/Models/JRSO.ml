module E = EventStructure
open SO
open SoOps

let build_so_structure es can must =
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let reads = List.map f es.E.reads in
  let can = List.map f can in
  let must = List.map f must in
  rels [
    ("order", (2, order))
  ; ("conflict", (2, conflict))
  ; ("justifies", (2, justifies))
  ; ("reads", (1, reads))
  ; ("can", (1, can))
  ; ("must", (1, must))
  ; ("empty_set", (1, []))
  ]

(* Configuration justifies *)
(* ∀y∈(b-a). (∃x∈a . x ⊢ y) *)
let justify a b =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (y,
         (mk_implies
            [
              Not (QRel (a, [Var y]))
            ; QRel (b, [Var y])
            ; CRel ("reads", [Var y])
            ] (* only justify new stuff *)
            (FoAny (x,
                    And [
                      QRel (a, [Var x]);
                      CRel ("justifies", [Var x; Var y])
                    ]
                   )
            )
         )
        )

let valid a =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  let x' = mk_fresh_fv () in
  let y' = mk_fresh_fv () in
  And [
      FoAll (x, (FoAll (y,
        mk_implies
          [ QRel (a, [Var x])
          ; QRel (a, [Var y])
          ; CRel ("conflict", [Var x; Var y]) ]
          (mk_eq (Var x) (Var y)))))
    ; FoAll (y',
                 mk_implies [QRel (a, [Var y'])]
                   (FoAll (x', mk_implies
                             [CRel ("order", [Var x'; Var y'])]
                             (QRel (a, [Var x']))
                          )
                   )
    )]

(* Bounded reflexive transitive closure, up to n steps *)
let rec tc arity f n a b =
  let x = mk_fresh_sv () in
  match n with
    0 -> eq a b
  | _ -> Or [
    eq a b
  ; SoAny (x, arity, And [f a x; tc arity f (n-1) x b])
  ]

let always_justifies a b =
  And [justify a b; subset a b; valid a; valid b]

let always_justifies_tc = tc 1 always_justifies

let always_eventually_justifies n a b =
  let x = mk_fresh_sv () in
  let y = mk_fresh_sv () in
  And
    [ subset a b
    ; valid a
    ; valid b
    ; SoAll (x, 1,
        mk_implies
          [ always_justifies_tc n a x ]
          ( SoAny (y, 1,
              And
                [ always_justifies_tc n x y; justify y b ] ) ) ) ]

let true_reln n a b =
  let x = mk_fresh_sv () in
  SoAny (x, 1, subset x x)

let aej_tc m = tc 1 (always_eventually_justifies m)
(* let aej_tc m = tc 1 (true_reln m) *)

let do_decide es can must =
  let size = es.E.events_number in
  let x = mk_fresh_sv () in
  let y = mk_fresh_sv () in
  let can_s = mk_fresh_sv () in
  let must_s = mk_fresh_sv () in
  let f =
    SoAny (
      can_s, 1,
      SoAny (
        must_s, 1,
        SoAny (
          x, 1,
          SoAny (y, 1,
                 And [
                   eq_crel x "empty_set"
                 ; eq_crel can_s "can"
                 ; eq_crel must_s "must"
                 ; subset y can_s
                 ; subset must_s y
                 ; aej_tc size size x y ]
                )
        )
      )
    )
  in
  let s = { size = size; relations = build_so_structure es can must } in
  if Config.dump_query () then dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

