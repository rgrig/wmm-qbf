(**
 * Based on Repairing C++ Sequential Consistency (Ori Lahav et. al.)
 *)

module E = EventStructure

let set_minus a b x =
  SO.And [a x; SO.Not (b x)]

let set_eq a b =
  let x = SO.mk_fresh_fv () in
  SO.FoAll (x, SoOps.iff [a (SO.Var x)] [b (SO.Var x)])

let set_to_reln r x y =
  SO.And [
    SoOps.mk_eq x y
  ; r x
    (*; r y (* redundant as x = y *) *)
  ]

let complement s x =
  SO.Not (s x)

let reflcl r = SoOps.rel_union r SoOps.mk_eq

let sb po i m =
  SoOps.rel_union po (SoOps.cross i (set_minus m i))

let intersect a b x =
  SO.And [a x; b x]

let union a b x =
  SO.Or [a x; b x]

let rel_minus a b x y =
  SO.And [a x y; SO.Not (b x y)]

let rs n writes nas sloc sb rf =
  SoOps.sequence
    (set_to_reln writes)
    (SoOps.sequence
       (reflcl (SoOps.rel_intersect sb sloc))
       (SoOps.sequence
          (set_to_reln (intersect writes (complement nas)))
          (SoOps.r_tc n rf)
       )
    )

let sw reads nas rel acq_rel acq sc f rf sb rs =
  SoOps.sequence
    (set_to_reln (union rel (union acq_rel sc)))
    (SoOps.sequence
       (reflcl (SoOps.sequence (set_to_reln f) sb))
       (SoOps.sequence
          rs
          (SoOps.sequence
             rf
             (SoOps.sequence
                (set_to_reln (intersect reads (complement nas)))
                (SoOps.sequence
                   (reflcl (SoOps.sequence sb (set_to_reln f)))
                   (set_to_reln (union acq (union acq_rel sc)))
                )
             )
          )
       )
    )

let hb n sb sw =
  SoOps.tc n (SoOps.rel_union sb sw)

let fr rf mo =
  SoOps.rel_minus (SoOps.sequence (SoOps.invert rf) mo) SoOps.mk_eq

let eco rf mo fr =
  SoOps.rel_union
    rf
    SoOps.(rel_union
       mo
       (rel_union
          fr
          (rel_union
             (sequence mo rf)
             (sequence fr rf)
          )
       )
    )

let coh_constrain hb eco =
  SoOps.irreflexive (SoOps.sequence hb eco)

let atomic1_constrain eco =
  SoOps.irreflexive eco

let atomic2_constrain fr mo =
  SoOps.irreflexive (SoOps.sequence fr mo)

let fhb f sc hb =
  SoOps.sequence (set_to_reln (intersect f sc)) (reflcl hb)
let hbf f sc hb =
  SoOps.sequence (reflcl hb) (set_to_reln (intersect f sc))
let sb_neq_loc sb sloc =
  SoOps.rel_minus sb sloc

let scb sb hb sb_neq_loc mo fr sloc =
  SoOps.rel_union
    sb
    (SoOps.rel_union
       (SoOps.sequence
          sb_neq_loc
          (SoOps.sequence
             hb
             sb_neq_loc
          )
       )
       (SoOps.rel_union
          (SoOps.rel_intersect hb sloc)
          (SoOps.rel_union mo fr)
       )
    )

let psc_base sc fhb scb hbf =
  SoOps.sequence
    (SoOps.rel_union (set_to_reln sc) fhb)
    (SoOps.sequence
       scb
       (SoOps.rel_union (set_to_reln sc) hbf)
    )

let psc_f f sc hb eco =
  SoOps.sequence
    (set_to_reln (intersect f sc))
    (SoOps.sequence
       (SoOps.rel_union
          hb
          (SoOps.sequence
             hb
             (SoOps.sequence eco hb)
          )
       )
       (set_to_reln (intersect f sc))
    )

let psc psc_base psc_f =
  SoOps.rel_union psc_base psc_f

let sc_constrain psc =
  SoOps.acyclic psc

let sb_rf_constrain sb rf =
  SoOps.acyclic (SoOps.rel_union sb rf)

let conflict writes universe sloc =
  SoOps.rel_intersect
    (SoOps.rel_union
       (SoOps.cross writes universe)
       (SoOps.cross universe writes)
    )
    sloc

let mo nas co =
  SoOps.sequence
    (set_to_reln (complement nas))
    (SoOps.sequence co (set_to_reln (complement nas)))

let race ext conflict hb atomics =
  SoOps.rel_intersect
    ext
    (rel_minus
       (rel_minus
          conflict
          (SoOps.rel_union hb (SoOps.invert hb))
       )
       (SoOps.cross atomics atomics)
    )

let racy_constrain race =
  let curry_crel name a b = SO.CRel (name, [a; b]) in
  SoOps.rel_eq race (curry_crel "empty_rel")

let cat_constrain n rf mo po reads writes rel acq_rel acq sc sloc nas i m f =
  (* Observation: Our po = sb anyway *)
  let sb = sb po i m in
  let rs = rs n writes nas sloc sb rf in
  let sw = sw reads nas rel acq_rel acq sc f rf sb rs in
  let hb = hb n sb sw in
  let fr = fr rf mo in
  let eco = eco rf mo fr in
  let fhb = fhb f sc hb in
  let hbf = hbf f sc hb in
  let sb_neq_loc = sb_neq_loc sb sloc in
  let scb = scb sb hb sb_neq_loc mo fr sloc in
  let psc_base = psc_base sc fhb scb hbf in
  let psc_f =  psc_f f sc hb eco in
  let psc = psc psc_base psc_f in
  SO.And [
    coh_constrain hb eco
  ; atomic1_constrain eco
  ; atomic2_constrain fr mo
  ; sc_constrain psc
  ]


let do_decide es accept =
  let size = es.E.events_number in
  let curry_crel name a b = SO.CRel (name, [a; b]) in
  let curry_cset name a = SO.CRel (name, [a]) in
  let exec_id = SO.mk_fresh_sv ~prefix:"execution" () in
  let exec x = SO.QRel (exec_id, [x]) in
  let rf_id, rf = SoOps.mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = SoOps.mk_fresh_reln ~prefix:"do_decide_co" () in
  let exec2 = SoOps.cross exec exec in
  let po = SoOps.rel_intersect (curry_crel "order") exec2 in
  let sloc = SoOps.rel_intersect (curry_crel "sloc") exec2 in
  let ext = SoOps.rel_intersect (curry_crel "ext") exec2 in

  let na = intersect (curry_cset "na") exec in
  let writes = intersect (curry_cset "writes") exec in
  let reads = intersect (curry_cset "reads") exec in
  let rel = intersect (curry_cset "rel") exec in
  let rel_acq = intersect (intersect (curry_cset "acq") (curry_cset "rel")) exec in
  let acq = intersect (curry_cset "acq") exec in
  let sc = intersect (curry_cset "sc") exec in
  let fences = intersect (curry_cset "fences") exec in

  let mo = mo na co in
  let sb = sb po (curry_cset "init") exec in
  let rs = rs size writes na sloc sb rf in
  let sw = sw reads na rel rel_acq acq sc fences rf sb rs in
  let conflict = conflict writes exec sloc in

  let f =
    SO.SoAny (
      exec_id,1,
      SO.SoAny (
        co_id,2,
        SO.SoAny (
          rf_id,2,
          SO.And [
            CatCommon.goal_constrain accept exec_id
          ; JRSO.valid exec_id
          ; CatCommon.rf_constrain exec rf
(* XXX              (SoOps.rel_intersect
                 (curry_crel "justifies")
                 (SoOps.cross exec exec)
              ) *)
          ; CatCommon.co_constrain exec co
          ; SoOps.rel_subset co exec2
          ; SoOps.rel_subset rf exec2

          ; SO.Or [
              racy_constrain
                (race ext conflict (hb size sb sw)
                   (set_minus exec  na)
                )
            ; cat_constrain size rf
                mo po reads writes rel rel_acq acq sc sloc na
                (curry_cset "init")
                (curry_cset "universe")
                fences
            ]
          ]
        )
      )
    )
  in

  let s = SO.{
    size = size;
    relations = CatCommon.build_so_structure es accept
  }
  in

  if Config.dump_query () then SoOps.dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)

let simple_rc11_formula accept =
  let co_id, co = CatCommon.get_co () in
  let alpha_beta_id, alpha_beta = SoOps.mk_qrel2 "alphabeta" in
  let rf_id, rf = CatCommon.get_rf () in
  let goal_id, goal = CatCommon.get_goal () in
  let po = CatCommon.get_po () in
  let sb = SoOps.rel_minus po SoOps.mk_eq in
  let sloc = CatCommon.get_sloc () in
  let sc = CatCommon.get_sc () in
  let pre_psc_id, pre_psc = SoOps.mk_qrel2 "prepsc" in
  let w = CatCommon.get_w () in
  let r = CatCommon.get_r () in
  let f = CatCommon.get_f () in
  let rmw = CatCommon.get_rmw () in
  let hb, hb_axiom =
    let acq = CatCommon.get_acq () in
    let rel = CatCommon.get_rel () in
    let rlx = CatCommon.get_rlx () in
    let at_least_acq x = SO.Or [ acq x; sc x ] in
    let at_least_rel x = SO.Or [ rel x; sc x ] in
    let at_least_rlx x = SO.Or [ rlx x; acq x; rel x; sc x ] in
    let sw_end_sfx x y = SO.And
      [ r x; at_least_rlx x; at_least_acq y
      ; SO.Or [SoOps.mk_eq x y ; SO.And [sb x y; f y] ] ] in
    let sw_end = SoOps.sequence rf sw_end_sfx in

    let sw_begin_pfx x y = SO.And
      [ at_least_rel x
      ; SO.Or [SoOps.mk_eq x y ; SO.And [f x; sb x y] ] ] in

    let rs_pfx x y = SO.And
      [ w x
      ; SO.Or [ SoOps.mk_eq x y ; SO.And [ sb x y; sloc x y ] ]
      ; w y ; at_least_rlx y ] in
    let sw_begin = SoOps.sequence sw_begin_pfx rs_pfx in

    let sb_maybe = SoOps.maybe sb in
    let alpha = SoOps.sequence_n [ sw_end; sb_maybe; sw_begin ] in
    let beta = SoOps.sequence rf rmw in
    let hb = SoOps.rel_union
      sb
      (SoOps.sequence_n [ sb_maybe; sw_begin; alpha_beta; sw_end; sb_maybe ]) in
    let hb_axiom = SO.And
      [ SoOps.rel_subset alpha alpha_beta
      ; SoOps.rel_subset beta alpha_beta
      ; SoOps.rel_subset SoOps.mk_eq alpha_beta
      ; SoOps.transitive alpha_beta ] in
    (hb, hb_axiom) in
  let coherence_axiom = SO.And
    [ SoOps.irreflexive hb
    ; SoOps.irreflexive (SoOps.sequence rf hb)
    ; SoOps.irreflexive (SoOps.sequence_n [co; rf; hb])
    ; SoOps.irreflexive (SoOps.sequence co hb)
    ; SoOps.irreflexive (SoOps.sequence_n [co; hb; SoOps.invert rf])
    ; SoOps.irreflexive (SoOps.sequence_n [co; rf; hb; SoOps.invert rf]) ] in
  let rb = SoOps.sequence (SoOps.invert rf) co in
  let atomicity_axiom =
    SoOps.rel_empty (SoOps.rel_intersect rmw (SoOps.sequence rb co)) in
  let sc_axiom =
    let sb_notloc = SoOps.rel_minus sb sloc in
    let hb_loc = SoOps.rel_intersect hb sloc in
    let scb = SoOps.rel_union_n
                [ sb; SoOps.sequence_n [sb_notloc; hb; sb_notloc]; hb_loc; co; rb] in
    let psc_base = SoOps.sequence_n 
      [ (fun i j -> SO.Or [ SO.And [SoOps.mk_eq i j ; sc i ]; SO.And [ f i ; sc i; hb i j ] ] )
      ; scb
      ; (fun i j -> SO.Or [ SO.And [SoOps.mk_eq i j ; sc i ]; SO.And [ hb i j; f j; sc j ] ] ) ] in
    let psc_f = SoOps.rel_intersect
      (fun i j -> SO.And [ f i ; sc i ; f j ; sc j ] )
      (SoOps.rel_union hb (SoOps.sequence_n [hb; eco rf co rb; hb] ) ) in    
    let psc = SoOps.rel_union psc_base psc_f in
    SO.SoAny (pre_psc_id, 2, SO.And
      [ SoOps.total sc pre_psc
      ; SoOps.transitive pre_psc
      ; SoOps.irreflexive pre_psc
      ; SoOps.irreflexive (SoOps.sequence pre_psc psc) ]) in
  let no_thin_air_axiom =
    (* SoOps.acyclic (SoOps.rel_union sb rf), slightly optimized *)
    let cause_id, cause = CatCommon.get_cause () in
    SO.SoAny (cause_id, 2, SO.And
      [ SoOps.rel_subset sb cause
      ; SoOps.rel_subset rf cause
      ; SoOps.transitive cause ]) in
  let racy_axiom =
    let na = CatCommon.get_na () in
    let x = SO.mk_fresh_fv () in let vx = SO.Var x in
    let y = SO.mk_fresh_fv () in let vy = SO.Var y in
    SO.FoAny (x, SO.FoAny (y, SO.And
      [ goal vx; goal vy
      ; w vx; SO.Not (SoOps.mk_eq vx vy); sloc vx vy
      ; SO.Not (hb vx vy); SO.Not (hb vy vx)
      ; SO.Or [na vx; na vy] ])) in
  SO.(
  SoAny (goal_id, 1,
  SoAny (rf_id, 2,
  SoAny (co_id, 2,
  SoAny (alpha_beta_id, 2,
    And
      [ hb_axiom
      ; coherence_axiom
      ; atomicity_axiom
      ; sc_axiom
      ; no_thin_air_axiom
      ; CatCommon.rf_constrain goal rf
      ; CatCommon.co_constrain goal co
      ; SoOps.transitive co
        (* TODO: the above probably needs moving in CatCommon. Test SC model! *)
      ; SO.Or
        [ CatCommon.goal_constrain accept goal_id
        ; racy_axiom ] ]
  )))))

(* No fences. *)
let simple_do_decide es accept =
  let f = simple_rc11_formula accept in
  let s = CatCommon.sos_of_es es accept in
  if Config.dump_query () then SoOps.dump s f;
  Printf.printf "result: %b\n%!" (SoOps.model_check s f)


let na_do_decide es accept =
  do_decide es accept

let rlx_do_decide es accept =
  let es =
    E.{
      es with
      na = []
    ; rlx = es.na
    }
  in
  do_decide es accept

let ra_do_decide es accept =
  let writes = List.filter
         (fun f -> not ((List.mem f es.E.reads) || (List.mem f es.E.fences)))
         (Util.range 1 (es.E.events_number))
  in

  let es =
    E.{
      es with
      na = []
    ; rel = es.reads
    ; acq = writes
    }
  in
  do_decide es accept

let sc_do_decide es accept =
  let es =
    E.{
      es with
      na = []
    ; sc = es.na
    }
  in
  do_decide es accept
