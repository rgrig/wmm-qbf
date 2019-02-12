module E = EventStructure
module GH = GraphHelpers
open SoOps

type event_setset = EventStructure.set list

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
  let rlx = List.map f es.E.rlx in
  let con = List.map f es.E.consume in
  let fences = List.map f es.E.fences in
  let universe = List.map f (Util.range 1 es.E.events_number) in
  
  (* Turn pairs into a list of two elements *)
  let f (x,y) = [x;y] in

  (* We'll take the symmetric closure of the transitive closure for
     the same location relation *)
  let sloc' = GH.symmetric_closure (GH.transitive_closure es.E.sloc) in
  let sloc = List.map f sloc' in

  let order = List.map f es.E.order in
  let justifies = List.map f es.E.justifies in
  let conflict = List.map f es.E.conflicts in
  let ext = List.map f es.E.ext in

  SoOps.rels ([
    ("acq", (1, acq))
  ; ("con", (1, con))
  ; ("conflict", (2,conflict))
  ; ("empty_rel", (2, []))
  ; ("empty_set", (1, []))
  ; ("ext", (2, ext))
  ; ("fences", (1, fences))
  ; ("init", (1, [[1]]))
  ; ("justifies", (2, justifies))
  ; ("na", (1, na))
  ; ("order", (2, order))
  ; ("reads", (1, reads))
  ; ("rel", (1, rel))
  ; ("rlx", (1, rlx))
  ; ("rmw", (2, [(* TODO *)]))
  ; ("sc", (1, sc))
  ; ("sloc", (2, sloc))
  ; ("universe", (1, universe))
  ; ("writes", (1, writes))
  ] @
      List.map (fun fin ->
          (name_final (incr final_id; !final_id)),
          (1, List.map (fun f -> [f]) fin)
        ) accept
    )

let sos_of_es es accept = SO.
  { size = es.EventStructure.events_number
  ; relations = build_so_structure es accept }
  

let curry_crel name a b = SO.CRel (name, [a; b])

(* NOTE: We do not constrain rf to be included in (gxg). This should be
fine for most memory models, where adding new rf edges can only invalidate
constraints. *)
let rf_constrain g rf =
  let rf_rf_inv = sequence rf (invert rf) in
  let r = SO.mk_fresh_fv ~prefix:"rf_r" () in
  let w = SO.mk_fresh_fv ~prefix:"rf_w" () in
  SO.And [
    (* Each read has at most one incoming rf edge *)
    rel_subset rf_rf_inv mk_eq
  ; rel_subset rf (curry_crel "justifies")
  ; FoAll (
      r,
      mk_implies
        [CRel ("reads", [Var r]); g (SO.Var r)]
        (FoAny (w, And [
             rf (Var w) (Var r)
           ; CRel ("writes", [Var w])
           ; g (Var w)
           ]))
    )
  ]

(* NOTE: the user of this function is responsible of requiring that co is acyclic *)
let co_constrain g co =
  let sloc_irrefl = rel_minus (curry_crel "sloc") mk_eq in
  let a = SO.mk_fresh_fv () in
  let b = SO.mk_fresh_fv () in
  SO.(FoAll (
    a,
    FoAll (
      b,
      And [
        iff [
            CRel ("writes", [Var a])
          ; CRel ("writes", [Var b])
          ; g (Var a)
          ; g (Var b)
          ; sloc_irrefl (Var a) (Var b)
          ]
        [Or [(co (Var a) (Var b)); (co (Var b) (Var a))]]
      ]
    )
  ))

let conflict_free c =
  let x = SO.mk_fresh_fv () in
  let y = SO.mk_fresh_fv () in
  SO.(FoAll (
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
  ))

let maximal x =
  let c' = SO.mk_fresh_sv () in
  SO.(SoAll (
    c', 1,
    mk_implies [
      conflict_free x
    ; conflict_free c'
    ; subset x c'
    ] (subset c' x)
  ))

let valid a =
  let open SO in
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

(* TODO(rg): change type of [g] to [SoOps.rel1], and update uses *)
let goal_constrain accept g =
  let final_id = ref 0 in
  SO.(And (
    valid g
    ::
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
    ))

let get_acq () = SoOps.mk_crel1 "acq"
let get_cause () = SoOps.mk_qrel2 "cause"
let get_co () = SoOps.mk_qrel2 "co"
let get_goal () = SoOps.mk_qrel1 "goal"
let get_hb () = SoOps.mk_qrel2 "hb"
let get_na () = SoOps.mk_crel1 "na"
let get_po () = SoOps.mk_crel2 "order"
let get_r () = SoOps.mk_crel1 "reads"
let get_rel () = SoOps.mk_crel1 "rel"
let get_rf () = SoOps.mk_qrel2 "rf"
let get_rlx () = SoOps.mk_crel1 "rlx"
let get_rmw () = SoOps.mk_crel2 "rmw"
let get_sc () = SoOps.mk_crel1 "sc"
let get_sloc () = SoOps.mk_crel2 "sloc"
let get_w () = SoOps.mk_crel1 "writes"
