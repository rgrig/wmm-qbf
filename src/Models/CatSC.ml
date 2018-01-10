module E = EventStructure
module GH = GraphHelpers
open SO
open SoOps

type reln = fo_var -> fo_var -> formula

let intersect a b =
    List.filter (fun x -> List.mem x a) b

let build_so_structure es goal =
  (* 
     Each of the relations in the SO structure is represented as a
     list of lists. A set is a list of singletons, a binary relation
     is a list of lists of length 2, a tenary relation is a list of
     lists of length 3, etc. 
     
     {(3, 4), (1, 2)} = [[3;4]; [1;2]]
     {4,6,2,1} = [[4]; [6]; [2]; [1]]
  *)
  (* Turn single elements into singleton lists *)
  let f x = [x] in
  let target = List.map f goal in
  let reads = List.map f (intersect es.E.reads goal) in
  let writes = 
    List.map f
      (intersect (List.filter
         (fun f -> not (List.mem f es.E.reads))
         (Util.range 1 (es.E.events_number))
      ) goal)
  in

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

  let filter (xss: E.event list list) = List.filter (fun xs ->
      List.for_all (fun x -> List.mem x goal) xs
    ) xss
  in
  
  let sloc = filter sloc in
  let order = filter order in
  let justifies = filter justifies in
  
  SoOps.rels [
    ("target", (1, target))
  ; ("sloc", (2, sloc))
  ; ("order", (2, order))
  ; ("justifies", (2, justifies))
  ; ("reads", (1, reads))
  ; ("writes", (1, writes))
  ; ("empty_set", (1, []))

  ; ("co", (2, [[2;3]]))
  ; ("rf", (2, [[3;7];[1;8]]))
  ; ("my_po", (2, [[7;8]]))
  ; ("my_fr", (2, [[8;3]]))
  ; ("my_rf", (2, [[8;2]]))    
  ]


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
        (FoAny (w,
                rf (Var w) (Var r)
               )
        )
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

let cat_constrain rf co fr po =
  acyclic (rel_union (com rf co fr) po)

let eq_crel2 a n =
  let x = mk_fresh_fv ~prefix:"eq_crel2_x" () in
  let y = mk_fresh_fv ~prefix:"eq_crel2_y" () in
  FoAll (
    x,
    FoAll (
      y,
      And [
        mk_implies [QRel (a, [Var x; Var y])] (CRel (n, [Var x; Var y]))
      ; mk_implies [CRel (n, [Var x; Var y])] (QRel (a, [Var x; Var y]))
      ]
    )
  )

let do_decide es target =
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
          rf_constrain
            rf
            (curry_crel "justifies")
        ; cat_constrain rf co (fr rf co) (curry_crel "order")
        ; co_constrain co 
        ]
      )
    )
  in

  let s = {
      size = size;
      relations = build_so_structure es target
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

