open SO
open SoOps

let rf_constrain rf jst =
  let rf_rf_inv = sequence rf (invert rf) in
  let r = mk_fresh_fv ~prefix:"rf_r" () in
  let w = mk_fresh_fv ~prefix:"rf_w" () in
  And [
    rel_subset rf_rf_inv mk_eq
  (* justification ∈ (W × R) *) 
  ; rel_subset rf jst 
  ; FoAll (
      r,
      mk_implies
        [CRel ("reads", [Var r])]
        (FoAny (w, rf (Var w) (Var r)))
    )
  ]

let co_constrain co =
  let a = mk_fresh_fv () in
  let b = mk_fresh_fv () in
  FoAll (
    a,
    FoAll (
      b,
      And [
        iff [
          CRel ("writes", [Var a])
        ; CRel ("writes", [Var b])
        ; CRel ("sloc", [Var a; Var b])
        ] [Or [(co (Var a) (Var b)); (co (Var b) (Var a))]]
      (* Alternatively it might be sufficient to constrain co to be
         acyclic, rather than trancl irrefl. *)
      ; irreflexive co
      ; transitive co
      ]
    )
  )

let fr rf co = (sequence (invert rf) co)

let com rf co fr = rel_union (rel_union rf co) fr

