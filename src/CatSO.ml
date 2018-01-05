module E = EventStructure
open SO
open SoOps

type reln = fo_var -> fo_var -> formula

let build_so_structure es goal =
  let f (x,y) = [x;y] in
  let order = List.map f es.E.order in
  let conflict = List.map f es.E.conflicts in
  let justifies = List.map f es.E.justifies in
  let f x = [x] in
  let target = List.map f goal in
  let reads = List.map f es.E.reads in
  let writes = List.map f
      (List.filter
         (fun f -> not (List.mem f es.E.reads))
         (Util.range 1 (es.E.events_number))
      ) in
  SoOps.rels [
    ("order", order)
  ; ("conflict", conflict)
  ; ("justifies", justifies)
  ; ("target", target)
  ; ("reads", reads)
  ; ("writes", writes)
  ; ("empty_set", [])
  ]

let eq r r' =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
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

let sequence r1 r2 x z = 
  let y = mk_fresh_fv () in
  FoAny (y, And [
      r1 x (Var y)
    ; r2 (Var y) z
    ])

let rel_union r1 r2 x y =
  Or [r1 x y; r2 x y]

let rel_intersect r1 r2 x y =
  And [r1 x y; r2 x y]
    
let rel_subset r1 r2 =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (
    x,
    FoAll (
      y,
      mk_implies
        [r1 (Var x) (Var y)]
        (r2 (Var x) (Var y))
    )
  )

let rf_constrain rf jst read_set =
  let rf_rf_inv = sequence rf (invert rf) in
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  let r = mk_fresh_fv () in
  let w = mk_fresh_fv () in
  And [
    FoAll (
      x,
      FoAll (
        y,
        (mk_implies [rf_rf_inv (Var x) (Var y)] (mk_eq (Var x) (Var y))
        )
      )
    )
  (* justification is ∈ (W × R) *) 
  ; rel_subset rf jst
  ; FoAll (r,
           mk_implies
             [QRel (read_set, [Var r])]
             (FoAny (w,
                     rf (Var w) (Var r)
                    )
             )
          )
  ]
  
(*
let co_constrain co = Eq [co;co]
*)
let eq a b =
  And [rel_subset a b; rel_subset b a]

(* Bounded reflexive transitive closure, up to n steps *)
let rec r_tc n f (a: term) (b:term) =
  let x = mk_fresh_fv () in
  let step = match n with
      0 -> mk_eq
    | _ -> r_tc (n-1) f
  in
  Or [
    mk_eq a b
  ; FoAny (x, And [f a (Var x); step (Var x) b])
  ]
    
(* Bounded transitive closure *)
(* f+ a b ≜ f a b ∨ (∃x. f a x ∧ f+ x b) *)
let rec tc n f a b =
  let x = mk_fresh_fv () in
  let step = match n with
      0 -> f
    | _ -> tc (n-1) f
  in
  Or [
    f a b
  ; FoAny (x, And [f a (Var x); step (Var x) b])
  ]

let mk_fresh_reln () =
  let r_id = mk_fresh_sv () in
  let r i j = QRel (r_id, [i; j]) in
  (r_id, r)

let empty_reln r =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (
    x,
    FoAll (
      y,
      Not (r (Var x) (Var y))
    )
  )

let acyclic n r : formula =
  let r' = tc n r in
  empty_reln (rel_intersect r' mk_eq)
  

let cat_constrain n rf po =
  acyclic n (rel_union rf po)

let do_cat n po jst read_set =
  let rf_id, rf = mk_fresh_reln () in
  SoAny (
    rf_id, 2, (
      And [
        rf_constrain rf jst read_set
      ; cat_constrain n rf po
      ]
    )
  )

let do_decide es target =
  let size = es.E.events_number in
  let curry_crel name a b = CRel (name, [a; b]) in
  let read_set = mk_fresh_sv () in
  let f =
    SoAny (
      read_set, 1,
      And [
        eq_crel read_set "reads"
      ; do_cat
          (List.length target)
          (curry_crel "order")
          (curry_crel "justifies")
          read_set
      ]
    )
  in

  let s = {
      size = size;
      relations = build_so_structure es target
    }
  in

  (* Debug stuff *)
  if Config.dump_query () then (
    let basename = Filename.remove_extension (Config.filename ()) in
    let f_c = open_out (basename ^ ".sol") in
    Printf.fprintf f_c "%s\n" (show_formula f);
    close_out f_c;

    let s_c = open_out (basename ^ ".str") in
    Printf.fprintf s_c "%s\n" (show_structure s);
    close_out s_c;
  );
  Printf.printf "result: %b\n" (SoOps.model_check s f)

