open Printf
module U = Util
module E = EventStructure

(**
   maximal x ≜ valid_conf x ∧ ∃y . valid_conf y ‌∧ x ⊆ y → x = y
*)
let maximal_conf es x =
  let y = MM.fresh_so_var es 1 in
  MM.forall y @@ Qbf.mk_and [
    MM.valid_conf es x;
    Qbf.mk_implies
      [MM.valid_conf es y; MM.subset x y]
      (MM.equal x y) (* more effeciently could be `MM.subset y x' but less literate *)
  ]

(**
   Assume e is a write

   certifiable e C ≜ ∀Y . (C ⊆ Y) ∧ maximal_conf Y → (∃z∈(equiv e) . z ∈ Y)

   This might be that we want to do z ∈ (Y\C). Intuition: are we
   certifying a new memory access, or can we rely on those that have
   already been executed?
*)
let certifiable es e c =
  let y = MM.fresh_so_var es 1 ~prefix:(Printf.sprintf "cert%d_" e) in
  let s_writes = List.filter (MM.same_label es e) (EventStructure.writes es) in
  MM.forall y
    (Qbf.mk_implies
       [MM.subset c y; maximal_conf es y]
       (Qbf.mk_or @@ List.map (fun z -> MM._in [z] y) s_writes)
    )

let grows_by es x y ev =
  let events = EventStructure.events es in
  Qbf.mk_and @@ [
    MM.subset x y
  ; MM._in [ev] y
  ] @
    List.map (fun b ->
        Qbf.mk_implies [MM._in [b] y] (
          if b = ev
          then Qbf.mk_true ()
          else (MM._in [b] x)
        )
      ) events

let follows_config es c e =
  Qbf.mk_and @@ List.map (fun f ->
      if List.mem (f, e) (EventStructure.order_tc es)
      then MM._in [f] c
      else Qbf.mk_true ()
    ) (EventStructure.events es)

(** 
     e follows config    e∈W → e∈P    conf' = conf ∪ {e}
   ———————————————————————————————————————————————————————
                 <conf, P> ––→ <conf', P>
*)
let promise_read es (conf, proms) (conf', proms') =
  (* This relies on the input relation being the transitive reduction *)
  (* This is wrong. This should be a function
     follows_config -> so_var -> int -> Qbf.t

     Such that given an conf, the event should immediately follow but
     not be a member of conf.
  *)
  let preconds x =
    let write_imp_prom =
      if List.mem x (EventStructure.writes es)
      then MM._in [x] proms
      else Qbf.mk_true ()
    in

    (*let justifying_writes = List.map fst
        (List.filter (fun (_,y) -> x == y) (EventStructure.justifies es))
      in*)
    
    Qbf.mk_and [
      follows_config es conf x
    ; write_imp_prom
    ; grows_by es conf conf' x
    (*; Qbf.mk_implies [MM._in [x] conf'] (Qbf.mk_or (List.map (fun x -> MM._in [x] proms) justifying_writes))*)
    ]
  in

  (* ∃ev∈W . follows_config ev ∧ ev∈proms ∧ conf_has_e ev ∧ ev∈conf' *)
  Qbf.mk_and [
    Qbf.mk_or (List.map preconds (EventStructure.events es))
  ; MM.equal proms proms'
  ]

(** 
     e∈W     e is certifiable      proms' = proms ∪ {e}
   —————————————————————————————————————————————————–————
            <conf, proms> ––→ <conf', proms'>
*)
let make_promise es (conf,proms) (conf',proms') =
  let writes = EventStructure.writes es in
  let events = EventStructure.events es in

  (* e∈W ∧ certifiable e *)
  (* This is terribly named. What about 'certifiable_write' *)
  let is_certifiable e =
    if List.mem e writes
    then certifiable es e conf
    else Qbf.mk_false ()
  in
  
  (* ∀ev∈events . f ev → ev ∈ proms' *)
  (* This has the effect of adding all certifiable writes at once,
     which is wrong. I should do a "grows by e" type thing as in the
     rule above. This would suggest I should macro such a function,
     too.*)
(*  let k = Qbf.mk_and @@ List.map (fun x -> Qbf.mk_implies [f x] (MM._in [x] proms')) events in
  MM.exists writes @@ (Qbf.mk_and [MM.writes es writes; k])
*)
  Qbf.mk_and [
    Qbf.mk_or @@ List.map (fun e -> Qbf.mk_implies [is_certifiable e] (grows_by es proms proms' e)) events
  ; MM.equal conf conf'
  ]

let promise_step es (conf,proms) (conf',proms') =
  Qbf.mk_or [
    promise_read es (conf,proms) (conf',proms')
  ; make_promise es (conf,proms) (conf',proms')
  ]

let promising es conf proms goal =
  (*  let writes = EventStructure.writes es in *)
  let rec do_step (conf, proms) n =
    let conf' = MM.fresh_so_var es 1 in
    let proms' = MM.fresh_so_var es 1 in
    let r =
      if n = 0 then
        MM.equal conf goal
      else
        Qbf.mk_or [
          MM.equal conf goal
        ; Qbf.mk_and @@ [
            MM.valid_conf es conf'
          ; promise_step es (conf,proms) (conf',proms')
          ; do_step (conf', proms') (n-1)
          ] (*@ List.map (fun e -> Qbf.mk_implies [MM._in [e] proms] (certifiable es e conf)) writes*)
        ]
    in
    MM.exists conf' @@ MM.exists proms' @@ r
  in
  do_step (conf, proms) (EventStructure.events_number es)

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target solver_opts =
  let c = MM.fresh_so_var es 1 ~prefix:"conf" in
  let p = MM.fresh_so_var es 1 ~prefix:"proms" in  
  let g = MM.fresh_so_var es 1 ~prefix:"goal" in
  let q = Qbf.mk_and [
      MM.equals_set c []
    ; MM.equals_set p []
    ; MM.equals_set g target
    ; MM.valid_conf es c
    ; MM.valid_conf es g
    ; promising es c p g
    ] in
  let q = MM.exists c
    @@ MM.exists p
    @@ MM.exists g q
  in
  Util.maybe (Qbf.holds q solver_opts) (printf "result: %b\n")

