open Printf
module U = Util
module E = EventStructure

let debugging = false

let debug f = if debugging then f () else ()

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
  debug @@ (fun x -> Printf.printf "  entering grows_by\n");
  debug @@ (fun x -> Printf.printf "    List.length ev = %d\n" (List.length ev));
  let events = EventStructure.events es in
  let rec copy xs = function
      1 -> [xs]
    | n -> xs :: copy xs (n-1)
  in
  Qbf.mk_and @@ [
    MM.subset x y
  ; MM._in ev y
  ] @
    List.map (fun b ->
        Qbf.mk_implies [MM._in b y] (
          if b == ev
          then Qbf.mk_true ()
          else (MM._in b x)
        )
      ) (Util.n_cartesian_product (copy events (List.length ev)))

let follows_config es c e =
  debug @@ (fun x ->Printf.printf "  entering follows_config\n");
  Qbf.mk_and @@ List.map (fun f ->
      if List.mem (f, e) (EventStructure.order_tc es)
      then MM._in [f] c
      else Qbf.mk_true ()
    ) (EventStructure.events es)

let coh es co rf =
  debug @@ (fun x -> Printf.printf "  entering coh\n");
  Qbf.mk_true ()

let b_to_qbf b = if b then Qbf.mk_true () else Qbf.mk_false ()

(** 
     e∈W     e is certifiable      proms' = proms ∪ {e}
   —————————————————————————————————————————————————–————
          <conf, proms, rf> ––→ <conf, proms', rf>
*)
let promise es co (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> Printf.printf "\n=== entering promise ===\n");
  let writes = EventStructure.writes es in
  let events = EventStructure.events es in

  (* e∈W ∧ certifiable e *)
  (* This is terribly named. What about 'certifiable_write' *)
  let is_certifiable e =
    if List.mem e writes
    then certifiable es e c
    else Qbf.mk_false ()
  in
  
  Qbf.mk_and [
    Qbf.mk_or @@ List.map (fun e -> Qbf.mk_implies [is_certifiable e] (grows_by es q q' [e])) events
  ; MM.equal c c'
  ; MM.equal rf rf'
  ]

let read es co (c,q,rf) (c',q',rf') =
  debug @@ (fun x ->Printf.printf "\n=== entering read ===\n");
  let reads = EventStructure.reads es in
  let writes = EventStructure.writes es in
  let events = EventStructure.events es in
  let justifies = EventStructure.justifies es in
  
  let is_readable r =
    if List.mem r reads
    then Qbf.mk_or @@ List.map (
        fun w -> Qbf.mk_and [
            grows_by es rf rf' [r;w]
          ; grows_by es c c' [r]
          ; coh es co rf'
          ; MM._in [w] q
          ; b_to_qbf (List.mem (w,r) justifies)
          ]
      ) writes
    else Qbf.mk_false ()
  in
  
  Qbf.mk_and [
    Qbf.mk_or @@ List.map is_readable events
  ; MM.equal q q'
  ]

let fulfill es co (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> Printf.printf "\n=== entering fulfill ===\n");
  let is_fulfillable w = Qbf.mk_or [
      follows_config es c w
    ; MM._in [w] q
    ; coh es co rf
    ]
  in
  Qbf.mk_and [
    Qbf.mk_or @@ List.map is_fulfillable (EventStructure.writes es)
  ; MM.equal q q'
  ; MM.equal rf rf'
  ]

let promise_step es co (c,q, rf) (c',q', rf') =
  debug @@ (fun x -> Printf.printf "entering promise_step\n");
  Qbf.mk_or [
    promise es co (c,q,rf) (c',q',rf')
  ; read es co (c,q,rf) (c',q',rf')
  ; fulfill es co (c,q,rf) (c',q',rf')
  ]

let promising es co (c,q,rf) goal =
  debug @@ (fun x -> Printf.printf "entering promising\n");
  (*  let writes = EventStructure.writes es in *)
  let rec do_step (c,q,rf) n =
    let c' = MM.fresh_so_var es 1 in
    let q' = MM.fresh_so_var es 1 in
    let rf' = MM.fresh_so_var es 2 ~prefix:"rf" in
    let r =
      if n = 0 then
        MM.equal c goal
      else
        Qbf.mk_or [
          MM.equal c goal
        ; Qbf.mk_and @@ [
            MM.valid_conf es c'
          ; promise_step es co (c,q,rf) (c',q',rf')
          ; do_step (c', q', rf') (n-1)
          ] (*@ List.map (fun e -> Qbf.mk_implies [MM._in [e] proms] (certifiable es e conf)) writes*)
        ]
    in
    MM.exists c' @@ MM.exists q' @@ MM.exists rf' r
  in
  do_step (c,q,rf) (EventStructure.events_number es)

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target solver_opts =
  let c = MM.fresh_so_var es 1 in
  let q = MM.fresh_so_var es 1 in
  let g = MM.fresh_so_var es 1 in
  let rf = MM.fresh_so_var es 2 ~prefix:"rf" in
  let co = MM.fresh_so_var es 2 in
  let query = Qbf.mk_and [
      MM.equals_set c []
    ; MM.equals_set q []
    ; MM.equals_sets rf []
    ; MM.equals_set g target
    ; MM.valid_conf es c
    ; MM.valid_conf es g
    ; promising es co (c,q,rf) g
    ] in
  let query = MM.exists c
    @@ MM.exists q
    @@ MM.exists g
    @@ MM.exists rf
    @@ MM.exists co query
  in
  Util.maybe (Qbf.holds query solver_opts) (printf "result: %b\n")

