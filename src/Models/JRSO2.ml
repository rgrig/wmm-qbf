module E = EventStructure
open SO

let build_so_structure es goal =
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let target = List.map f goal in
  SoOps.rels [
    ("order", order)
  ; ("conflict", conflict)
  ; ("justifies", justifies)
  ; ("target", target)
  ; ("empty_set", [[]])
  ]

(* Configuration justifies *)
(* ∀y∈b. (∃x∈a . x ⊢ y) *)
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
  FoAll (
    x, (
      FoAll (
        y,
        And [
          QRel (a, [Var x])
        ; QRel (a, [Var y])
        ; mk_implies [CRel ("conflict", [Var x; Var y])] (Eq [Var x; Var y])
        ; FoAll (y',
                 mk_implies [QRel (a, [Var y'])]
                   (FoAll (x', mk_implies
                             [CRel ("order", [Var x'; Var y'])]
                             (QRel (a, [Var x']))
                          )
                   )
                )
        ]
      )
    )
  )

let eq a b =
  And [subset a b; subset b a]

(* Bounded reflexive transitive closure, up to n steps *)
let rec tc arity f n a b =
  let x = mk_fresh_name () in
  let step = match n with
      0 -> eq
    | _ -> tc arity f (n-1)
  in
  Or [
    eq a b
  ; SoAny (x, arity, And [f a x; step x b])
  ]

let always_justifies a b =
  And [justify a b; subset a b; valid a; valid b]

let always_justifies_tc = tc 1 always_justifies

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

let aej_tc m = tc 1 (always_eventually_justifies m)

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
  let dump_qbf,dump_query,debug = solver_opts in
  if dump_query then (
      SO.pp_formula Format.std_formatter q;
      Printf.printf "\n";
      SO.pp_structure Format.std_formatter s;
    );
  let q = SoOps.so_to_qbf s q in
  Util.maybe (Qbf.holds q (dump_qbf,false,debug))
    (Printf.printf "result: %b\n")
