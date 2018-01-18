(** 
 * Based on Repairing C++ Sequential Consistency (Ori Lahav et. al.)
 *)

module E = EventStructure
module GH = GraphHelpers
open SO
open SoOps

let cross a b x y =
  And [a x; b y]

let set_minus a b (x:term) =
  And [a x; Not (b x)]

let set_eq a b =
  let x = mk_fresh_fv () in
  FoAll (x, iff [a (Var x)] [b (Var x)])

let set_to_reln r x y =
  And [
    mk_eq x y
  ; r x
    (*; r y (* redundant as x = y *) *)
  ]

let complement s x =
  Not (s x)

let reflcl r = rel_union r mk_eq

let sb po i m =
  rel_union po (cross i (set_minus m i))

let intersect a b x =
  And [a x; b x]

let union a b x =
  Or [a x; b x]

let rel_minus a b x y =
  And [a x y; Not (b x y)]
    
let rs n writes nas sloc sb rf =
  sequence
    (set_to_reln writes)
    (sequence
       (reflcl (rel_intersect sb sloc))
       (sequence
          (set_to_reln (intersect writes (complement nas)))
          (r_tc n rf)
       )
    )

let sw reads nas rel acq_rel acq sc f rf sb rs =
  sequence
    (set_to_reln (union rel (union acq_rel sc)))
    (sequence
       (reflcl (sequence (set_to_reln f) sb))
       (sequence
          rs
          (sequence
             rf
             (sequence 
                (set_to_reln (intersect reads (complement nas)))
                (sequence
                   (reflcl (sequence sb (set_to_reln f)))
                   (set_to_reln (union acq (union acq_rel sc)))
                )
             )
          )
       )
    )

let hb n sb sw =
  tc n (rel_union sb sw)

let fr rf mo = rel_minus (sequence (invert rf) mo) mk_eq

let eco rf mo fr =
  rel_union
    rf
    (rel_union
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
  irreflexive (sequence hb eco)

let atomic1_constrain eco =
  irreflexive eco
    
let atomic2_constrain fr mo =
  irreflexive (sequence fr mo)

let fhb f sc hb = sequence (set_to_reln (intersect f sc)) (reflcl hb)
let hbf f sc hb = sequence (reflcl hb) (set_to_reln (intersect f sc))
let sb_neq_loc sb sloc = rel_minus sb sloc

let scb sb hb sb_neq_loc mo fr sloc =
  rel_union
    sb
    (rel_union
       (sequence
          sb_neq_loc
          (sequence
             hb
             sb_neq_loc
          )
       )
       (rel_union
          (rel_intersect hb sloc)
          (rel_union mo fr)
       )
    )

let psc_base sc fhb scb hbf =
  sequence
    (rel_union (set_to_reln sc) fhb)
    (sequence
       scb
       (rel_union (set_to_reln sc) hbf)
    )

let psc_f f sc hb eco =
  sequence
    (set_to_reln (intersect f sc))
    (sequence
       (rel_union
          hb
          (sequence
             hb
             (sequence eco hb)
          )
       )
       (set_to_reln (intersect f sc))
    )

let psc psc_base psc_f =
  rel_union psc_base psc_f

let sc_constrain psc =
  acyclic psc

let sb_rf_constrain sb rf =
  acyclic (rel_union sb rf)

let conflict writes universe sloc =
  rel_intersect
    (rel_union
       (cross writes universe)
       (cross universe writes)
    )
    sloc

let mo nas co =
  sequence
    (set_to_reln (complement nas))
    (sequence co (set_to_reln (complement nas)))

let race ext conflict hb atomics =
  rel_intersect
    ext
    (rel_minus
       (rel_minus
          conflict
          (rel_union hb (invert hb))
       )
       (cross atomics atomics)
    )

let racy_constrain race =
  let curry_crel name a b = CRel (name, [a; b]) in
  rel_eq race (curry_crel "empty_set")

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
  And [
    coh_constrain hb eco 
  ; atomic1_constrain eco
  ; atomic2_constrain fr mo 
  ; sc_constrain psc
  ]

let do_decide es can must =
  let size = es.E.events_number in
  let curry_crel name a b = CRel (name, [a; b]) in
  let curry_cset name a = CRel (name, [a]) in
  let rf_id, rf = mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = mk_fresh_reln ~prefix:"do_decide_co" () in
  let f_consistent =
    SoAny (
      co_id, 2,
      SoAny (
        rf_id, 2,
        And [
          CatCommon.rf_constrain rf (curry_crel "justifies")
        ; CatCommon.co_constrain co
        ; cat_constrain size rf
            (mo (curry_cset "na") co)
            (curry_crel "order")
            (curry_cset "reads")
            (curry_cset "writes")
            (curry_cset "rel")
            (intersect (curry_cset "rel") (curry_cset "acq"))
            (curry_cset "acq")
            (curry_cset "sc")
            (curry_crel "sloc")
            (curry_cset "nas")
            (curry_cset "init")
            (curry_cset "universe")
            (curry_cset "fences")
        ]
      )
    )
  in

  let rf_id, rf = mk_fresh_reln ~prefix:"do_decide_rf" () in
  let co_id, co = mk_fresh_reln ~prefix:"do_decide_co" () in
  let mo = mo (curry_cset "na") co in
  let sb = sb (curry_crel "order") (curry_cset "init") (curry_cset "universe") in
  let rs = rs size
      (curry_cset "writes")
      (curry_cset "na")
      (curry_crel "sloc")
      sb rf
  in
  let sw = sw (curry_cset "reads")
      (curry_cset "na")
      (curry_cset "rel")
      (intersect (curry_cset "acq") (curry_cset "rel"))
      (curry_cset "acq")
      (curry_cset "sc")
      (curry_cset "fences")
      rf sb rs
  in

  let f_race =
    SoAny (
      co_id, 2,
      SoAny (
        rf_id, 2,
        And [
          CatCommon.rf_constrain rf (curry_crel "justifies")
        ; CatCommon.co_constrain co
        ; cat_constrain size rf
            mo
            (curry_crel "order")
            (curry_cset "reads")
            (curry_cset "writes")
            (curry_cset "rel")
            (intersect (curry_cset "rel") (curry_cset "acq"))
            (curry_cset "acq")
            (curry_cset "sc")
            (curry_crel "sloc")
            (curry_cset "na")
            (curry_cset "init")
            (curry_cset "universe")
            (curry_cset "fences")
        ; Not (
            racy_constrain
              (race
                 (curry_crel "ext")
                 (conflict
                    (curry_cset "writes")
                    (curry_cset "universe")
                    (curry_crel "sloc")
                 )
                 (hb size sb sw)
                 (set_minus (curry_cset "universe") (curry_cset "na"))
              )
          )
        ]
      )
    )
  in
  
  let s = {
      size = size;
      relations = CatCommon.build_so_structure es
    }
  in

  let f = Or [f_consistent; f_race] in
  if Config.dump_query () then SoOps.dump s f;
  Printf.printf "result: %b\n" (SoOps.model_check s f)
