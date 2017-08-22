open Printf

module E = EventStructure

(**
   maximal x ≜ valid_conf x ∧ ∃y . valid_conf y → y ⊆ x
*)
let maximal_conf es x =
  let y = MM.fresh_so_var es 1 in
  MM.forall y @@ Qbf.mk_and [
    MM.valid_conf es x;
    (Qbf.mk_implies [MM.valid_conf es y] (MM.subset y x))
  ]

(**
   certifiable e ≜ ∀y . maximal y → (∃z∈(equiv e) . z ∈ y)
*)
let certifiable es e =
  let y = MM.fresh_so_var es 1 in
  let s_writes = List.filter (MM.same_label es e) (EventStructure.writes es) in
  MM.forall y
    (Qbf.mk_implies
       [maximal_conf es y]
       (Qbf.mk_or @@ List.map (fun z -> MM._in [z] y) s_writes)
    )

(** 
     e follows config    e∈W → e∈P    conf' = conf ∪ {e}
   ———————————————————————————————————————————————————————
                 <conf, P> ––→ <conf', P>
*)
let promise_read es (conf, proms) (conf', proms') =
  (*Qbf.mk_or @@ List.map (fun x -> Qbf.mk_implies *)
  let writes = MM.fresh_so_var es 1 in
  let events = EventStructure.events es in

  let compose x rel =
    List.map snd (List.filter (fun (l,r) -> x == l) rel)
  in

  (* This relies on the input relation being the transitive reduction *)
  let follows_config x =
    let ns = compose x (EventStructure.order es) in
    Qbf.mk_or @@ List.map (fun n -> Qbf.mk_not (MM._in [x] conf)) ns
  in
  let writes_in_promises i =
    Qbf.mk_implies [MM._in [i] writes] (MM._in [i] proms)
  in

  (* TODO: Scrutinise *)
  (* ∀w . (w ∈ conf) → (w ∈ conf') ∧ (w != x) → (w ∈ conf' → w ∈ conf) ∧ (w = x) → w ∈ conf'*)
  (*
  let conf_has_e x =
    Qbf.mk_and @@
      List.map (fun w -> Qbf.mk_implies [MM._in [w] conf] (MM._in [w] conf')) events
      @ List.map (fun w -> if w != x then (Qbf.mk_implies [MM._in [w] conf'] (MM._in [w] conf)) else
                             MM._in [w] conf') events
  in
  *)

  (* conf ⊆ conf' ∧ (∀b∈events . b∈conf' → (b = e) ∨ b ∈ conf) *)
  let conf_has_e e =
    Qbf.mk_and @@ [
      MM.subset conf conf'
    ; Qbf.mk_and @@ List.map (fun b -> Qbf.mk_implies [MM._in [b] conf'] (if b = e then Qbf.mk_or [] else (MM._in [b] conf))) events
    ]
  in

  let preconds x =
    Qbf.mk_and [
      follows_config x
    ; writes_in_promises x
    ; conf_has_e x
    ]
  in

  (* We need to constrain our SO var to being the writes *)
  (* ∃ev∈W . follows_config ev ∧ ev∈proms ∧ conf_has_e ev ∧ ev∈conf' *)
  let k = Qbf.mk_or (List.map (fun x -> Qbf.mk_implies [preconds x] (MM._in [x] conf')) (EventStructure.writes es)) in
  MM.exists writes @@ (Qbf.mk_and @@ [MM.writes es writes; k])



(** 
     e∈W     e is certifiable      proms' = proms ∪ {e}
   —————————————————————————————————————————————————–————
            <conf, proms> ––→ <conf', proms'>
*)
let make_promise es (conf,proms) (conf',proms') =
  let writes = MM.fresh_so_var es 1 in
  let events = EventStructure.events es in

  (* {e} ∈ W ∧ certifiable e *)
  let f e = Qbf.mk_and [MM._in [e] writes; certifiable es e] in

  (* ∀ev∈events . f ev → ev ∈ proms' *)
  let k = Qbf.mk_and @@ List.map (fun x -> Qbf.mk_implies [f x] (MM._in [x] proms')) events in
  MM.exists writes @@ (Qbf.mk_and [MM.writes es writes; k])


let promise_step es (conf,proms) (conf',proms') =
  Qbf.mk_or [
    promise_read es (conf,proms) (conf',proms')
  ; make_promise es (conf,proms) (conf',proms')
  ]

let promising es conf proms goal =
  let writes = EventStructure.writes es in
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
          ] @ List.map (fun e -> Qbf.mk_implies [MM._in [e] proms] (certifiable es e)) writes
        ]
    in
    MM.exists conf' @@ MM.exists proms' @@ r
  in
  do_step (conf, proms) (EventStructure.events_number es)

let do_decide fn es target =
  let c = MM.fresh_so_var es 1 in
  let p = MM.fresh_so_var es 1 in
  let g = MM.fresh_so_var es 1 in
  let q = Qbf.mk_and [
      MM.equals_set c []
    ; MM.equals_set p []
    ; MM.equals_set g target
    ; MM.valid_conf es c
    ; MM.valid_conf es g
    ; promising es c p g
    ] in
  (* ? *)
  let q = MM.exists c (MM.exists p (MM.exists g q)) in
  let fn = sprintf "%s-decide" fn in
  printf "result: %b\n" (Qbf.holds fn q)
