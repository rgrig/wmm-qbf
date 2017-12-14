module E = EventStructure
open SO

type reln = fo_var -> fo_var -> formula

let build_so_structure es goal =
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let target = List.map f goal in
  let reads = List.map f es.E.reads in
  SoOps.rels [
    ("order", order)
  ; ("conflict", conflict)
  ; ("justifies", justifies)
  ; ("target", target)
  ; ("reads", reads)
  ; ("empty_set", [[]])
  ]
(*
let eq r r' =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  FoAll (x, (
      FoAll (y,
             And [
               mk_implies [QRel (r, [Var x; Var y])] (QRel (r', [Var x; Var y]))
             ; mk_implies [QRel (r', [Var x; Var y])] (QRel (r, [Var x; Var y]))
             ]
            )
    )
    )
*)
let eq r r' =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  FoAll (x, (
      FoAll (y,
             And [
               mk_implies [r x y] (r' x y)
             ; mk_implies [r' x y] (r x y)
             ]
            )
    )
    )

let invert r a b = r b a

(*

let invert r r' =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  FoAll (x, (
      FoAll (y,
             And [
               mk_implies [QRel (r, [Var x; Var y])] (QRel (r', [Var y; Var x]))
             ; mk_implies [QRel (r', [Var x; Var y])] (QRel (r, [Var y; Var x]))
             ]
            )
    )
    )
*)
(*
let sequence r1 r2 r12 =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  let y' = mk_fresh_name () in
  let z = mk_fresh_name () in
  FoAll (x, (
      FoAll (z, (
          And [
            (* r1 x y ∧ r2 y z ⇒ r12 x z *)
            mk_implies [
              (FoAny (y, And [
                   QRel (r1, [Var x; Var y])
                 ; QRel (r2, [Var y; Var z])
                 ]))] (QRel (r12, [Var x; Var z]))

          (* r12 x z ⇒ ∃y. r1 x y ∧ r2 y z *)
          ; mk_implies [(QRel (r12, [Var x; Var z]))]
              (FoAny (y', And [
                   QRel (r1, [Var x; Var y])
                 ; QRel (r2, [Var y; Var z])
                 ]))
          ]
        ))
    ))
*)

let sequence r1 r2 x z = 
  let y = mk_fresh_name () in
  FoAny (y, And [
      r1 x y
    ; r2 y z
    ])

let rel_union r1 r2 x y =
  Or [r1 x y; r2 x y]

let rel_intersect r1 r2 x y =
  And [r1 x y; r2 x y]
    
let rel_subset r1 r2 =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  FoAll (x, FoAll (y, mk_implies [r1 x y] (r2 x y)))

let rf_constrain rf jst read_set =
  let rf_rf_inv = sequence rf (invert rf) in
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  let r = mk_fresh_name () in
  let w = mk_fresh_name () in
  And [
    FoAll (x, FoAll (y,
                     (mk_implies [rf_rf_inv x y] (Eq [Var x; Var y])
                     )
                    )
          )
  ; rel_subset rf jst
  ; FoAll (r, mk_implies
             [QRel (read_set, [Var r])]
             (FoAny (w, rf w r)))
  ]
  
(*
let co_constrain co = Eq [co;co]
*)
let eq a b =
  And [rel_subset a b; rel_subset b a]

(* Bounded reflexive transitive closure, up to n steps *)
let rec r_tc n f a b =
  let x_id = mk_fresh_name () in
  let x i j = QRel (x_id, [Var i; Var j]) in
  let step = match n with
      0 -> eq
    | _ -> r_tc (n-1) f
  in
  Or [
    eq a b
  ; SoAny (x_id, 1, And [f a x; step x b])
  ]

(* Bounded transitive closure *)
(* f+ a b ≜ f a b ∨ (∃x. f a x ∧ f+ x b) *)
let rec tc n f a b =
  let x = mk_fresh_name () in
  let step = match n with
      0 -> f
    | _ -> tc (n-1) f
  in
  Or [
    f a b
  ; SoAny (x, 1, And [f a x; step x b])
  ]


let mk_fresh_reln () =
  let r_id = mk_fresh_name () in
  let r i j = QRel (r_id, [Var i; Var j]) in
  (r_id, r)

let empty_reln r =
  let x = mk_fresh_name () in
  let y = mk_fresh_name () in
  FoAll (
    x,
    FoAll (
      y,
      Not (r x y)
    )
  )

let id_rel x y = Eq [Var x; Var y]

let acyclic n r : formula =
  let r' = tc n r in
  empty_reln (rel_intersect r' id_rel)
  

let cat_constrain rf po a b =
  acyclic 1 rf

let do_cat po jst read_set a b =
  let rf_id, rf = mk_fresh_reln () in
  And [
    rf_constrain rf jst read_set
  ; cat_constrain rf po a b
  ]
