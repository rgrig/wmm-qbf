module E = EventStructure
open SO

let build_so_structure es target =
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let target = List.map f target in
  SoOps.rels [
    ("order", order)
  ; ("conflict", conflict)
  ; ("justifies", justifies)
  ; ("target", target)
  ; ("empty_set", [[]])
  ]

let justify a b =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  let f = FoAny (x,
                  And [
                    QRel (a, [Var x]);
                    CRel ("justifies", [Var x; Var y])
                  ]
                )
  in
  FoAll (y, mk_implies [QRel (a, [Var y])] f)

let subset a b =
  let y = mk_fresh_name () in
  FoAll (y, mk_implies [QRel (a, [Var y])] (QRel (b, [Var y])))

let valid a =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  let x' = mk_fresh_name () in
  let y' = mk_fresh_name () in
  And [
    QRel (a, [Var x])
  ; QRel (a, [Var y])
    (*  ; mk_implies [CRel "conflict" [Var a; Var b]] (Eq (a, b)) *)
  ; FoAll (y',
           mk_implies [QRel (a, [Var y'])]
             (FoAll (x', mk_implies
                       [CRel ("order", [Var x'; Var y'])]
                       (QRel (a, [Var x']))
                    )
             )
          )
  ]

let always_justifies a b =
  And [justify a b; subset a b; valid a; valid b]

let eq a b =
  And [subset a b; subset b a]

let always_justifies_tc_0 = eq

let rec always_justifies_tc n a b =
  let x = mk_fresh_name () in
  let step = match n with
      0 -> always_justifies_tc_0
    | _ -> always_justifies_tc (n-1)
  in
  Or [
    eq a b
    ; SoAny (x, 1, And [always_justifies a x; step x b])
  ]

let always_eventually_justifies n a b =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  And [
    subset a b
  ; SoAll (x, 1,
           SoAny (y, 1,
                  mk_implies [always_justifies_tc n a x]
                    (And [always_justifies_tc n x y; justify y b])
                 )
          )
  ]

let aej_tc_0 m = eq

let rec aej_tc m n a b =
  let x = mk_fresh_name () in
  let step = match n with
      0 -> aej_tc_0 m
    | _ -> aej_tc m (n-1)
  in
  Or [
    eq a b
  ; SoAny (x, 1, And [always_eventually_justifies m a x; step a b])  
  ]
  
let eq_crel a n =
  let x = mk_fresh_name ~prefix:"eq_crel" () in
  FoAll (x,
         And [
           mk_implies [QRel (a, [Var x])] (CRel (n, [Var x]))
         ; mk_implies [CRel (n, [Var x])] (QRel (a, [Var x]))
         ]
    )

let do_decide es target solver_opts =
  let size = es.E.events_number in
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  let q =
    SoAny (x, 1,
           SoAny (y, 1,
                  And [
                    eq_crel x "empty_set"
                  ; eq_crel y "target"
                  ; aej_tc size size x y ]
                 )
          )
  in
  let s = { SO.size = size; SO.relations = build_so_structure es target } in
  let q = SoOps.so_to_qbf s q in
  Util.maybe (Qbf.holds q solver_opts) (Printf.printf "result: %b\n")
