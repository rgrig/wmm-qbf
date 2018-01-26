module E = EventStructure
open SO
open SoOps

let build_so_structure es accept =
  let final_id = ref 0 in
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let reads = List.map f es.E.reads in
  rels ([
    ("order", (2, order))
  ; ("conflict", (2, conflict))
  ; ("justifies", (2, justifies))
  ; ("reads", (1, reads))
  ; ("empty_set", (1, []))
  ] @
      List.map (fun fin ->
          (Printf.sprintf "final%d" (incr final_id; !final_id)),
          (1, List.map f fin)
        ) accept
    )

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

let always_eventually_justifies n c d =
  let c' = mk_fresh_sv () in
  let c'' = mk_fresh_sv () in
  And
    [ subset c d
    ; valid c
    ; valid d
    ; SoAll (
        c', 1,
        mk_implies
          [ always_justifies_tc n c c' ]
          (SoAny (c'', 1, And [always_justifies_tc n c' c''; justify c'' d ]))
      )
    ]


let aej_tc m = tc 1 (always_eventually_justifies m)
(* let aej_tc m = tc 1 (true_reln m) *)

let maximal c =
  let c' = mk_fresh_sv () in
  SoAny (
    c', 1,
    mk_implies [
      valid c
    ; valid c'
    ; subset c c'
    ] (subset c' c)
  )


let do_decide es accept =
  let size = es.E.events_number in
  let x = mk_fresh_sv () in
  let y = mk_fresh_sv () in
  let f =
    SoAny (x, 1,
      SoAny (y, 1,
             And [
               eq_crel x "empty_set"
             ; maximal y
             ; aej_tc size size x y
             ; CatCommon.goal_constrain accept y
             ]
            )
    )
  in
  let s = { size = size; relations = build_so_structure es accept } in
  if Config.dump_query () then dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

