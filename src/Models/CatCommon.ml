module E = EventStructure
module GH = GraphHelpers
open SO
open SoOps


let name_final i = Printf.sprintf "final%d" i

(* Each of the relations in the SO structure is represented as a list
   of lists. A set is a list of singletons, a binary relation is a list
   of lists of length 2, a tenary relation is a list of lists of length
   3, etc.

     {(3, 4), (1, 2)} = [[3;4]; [1;2]]
     {4,6,2,1} = [[4]; [6]; [2]; [1]]
*)
let build_so_structure es accept =
  let final_id = ref 0 in

  (* Turn single elements into singleton lists *)
  let f x = [x] in
  let reads = List.map f es.E.reads in
  let writes =
    List.map f
      (List.filter
         (fun f -> not ((List.mem f es.E.reads) || (List.mem f es.E.fences)))
         (Util.range 1 (es.E.events_number))
      )
  in
  let na = List.map f es.E.na in
  let sc = List.map f es.E.sc in
  let rel = List.map f es.E.rel in
  let acq = List.map f es.E.acq in
  let con = List.map f es.E.consume in
  let fences = List.map f es.E.fences in
  let universe = List.map f (Util.range 1 es.E.events_number) in
  
  (* Turn pairs into a list of two elements *)
  let f (x,y) = [x;y] in

  (* We'll take the symmetric closure of the transitive closure for
     the same location relation *)
  let sloc' = GH.symmetric_closure (GH.transitive_closure es.E.sloc) in
  let sloc = List.map f sloc' in
  let xs = Util.range 2 es.E.events_number in
  let sloc_extra = List.map (fun x -> [1;x]) xs in
  let sloc = sloc @ sloc_extra in

  let order = List.map f es.E.order in
  let justifies = List.map f es.E.justifies in
  let conflict = List.map f es.E.conflicts in
  let ext = List.map f es.E.ext in

  SoOps.rels ([
    ("sloc", (2, sloc))
  ; ("conflict", (2,conflict))
  ; ("order", (2, order))
  ; ("justifies", (2, justifies))
  ; ("ext", (2, ext))
  ; ("empty_set", (1, []))
  ; ("universe", (1, universe))
  ; ("init", (1, [[1]]))
  ; ("reads", (1, reads))
  ; ("writes", (1, writes))
  ; ("na", (1, na))
  ; ("sc", (1, sc))
  ; ("rel", (1, rel))
  ; ("acq", (1, acq))
  ; ("con", (1, con))
  ; ("fences", (1, fences))
  ] @
      List.map (fun fin ->
          (name_final (incr final_id; !final_id)),
          (1, List.map (fun f -> [f]) fin)
        ) accept
    )

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
        ] (
          (* Conflict is symmetric so we only need to check one
             direction *)
          Not (CRel ("conflict", [Var x; Var y]))
        )
      )
    )
  )

let maximal x =
  let c' = mk_fresh_sv () in
  SoAll (
    c', 1,
    mk_implies [
      conflict_free x
    ; conflict_free c'
    ; subset x c'
    ] (subset c' x)
  )

let goal_constrain accept g =
  let final_id = ref 0 in
  And (
    List.map (fun a ->
        let e = mk_fresh_fv () in
        FoAny (e,
          And [
            QRel (g, [Var e])
          ; CRel (name_final (incr final_id; !final_id), [Var e])
          ]
        )
      )
      accept
    )
