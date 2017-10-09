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
    
let grows_by es x y ev =
  debug @@ (fun x -> printf "  entering grows_by\n");
  debug @@ (fun x -> printf "    List.length ev = %d\n" (List.length ev));
  let events = EventStructure.events es in
  Qbf.mk_and @@ [
    MM.subset x y
  ; MM._in ev y
  ] @
    List.map (fun b ->
        Qbf.mk_implies [MM._in b y] (
          if b = ev
          then Qbf.mk_true ()
          else (MM._in b x)
        )
      ) (Util.n_cartesian_product (U.copy events (List.length ev)))

let follows_config es c e =
  debug @@ (fun x -> printf "  entering follows_config\n");
  Qbf.mk_and @@ List.map (fun f ->
      if List.mem (f, e) (EventStructure.order_tc es)
      then MM._in [f] c
      else Qbf.mk_true ()
    ) (EventStructure.events es)

let coh es co rf =
  debug @@ (fun x -> printf "  entering coh\n");
  Qbf.mk_true ()

let b_to_qbf b = if b then Qbf.mk_true () else Qbf.mk_false ()

(** 
     e∈W     e is certifiable      proms' = proms ∪ {e}
   —————————————————————————————————————————————————–————
          <conf, proms, rf> ––→ <conf, proms', rf>
*)
let promise es co evt (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> printf "\n=== entering promise ===\n");
  let writes = EventStructure.writes es in
  let events = EventStructure.events es in

  Qbf.mk_and [
    Qbf.mk_or @@ List.map (fun e -> Qbf.mk_and [
        b_to_qbf (List.mem e writes)
      ; b_to_qbf (List.mem (evt, e) (EventStructure.order_tc es))
      ; (grows_by es q q' [e])]
      ) events
  ; MM.equal c c'
  ; MM.equal rf rf'
  ]

let read es co evt (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> printf "\n=== entering read ===\n");
  let reads = EventStructure.reads es in
  let writes = EventStructure.writes es in
  let justifies = EventStructure.justifies es in
  
  let is_readable r =
    if List.mem r reads
    then Qbf.mk_or @@ List.map (
        fun w -> Qbf.mk_and [
            grows_by es rf rf' [r;w]
          ; grows_by es c c' [r]
          ; follows_config es c r
          ; b_to_qbf (List.mem (evt, r) (EventStructure.order_tc es))
          ; coh es co rf'
          ; MM._in [w] q
          ; b_to_qbf (List.mem (w,r) justifies)
          ]
      ) writes
    else Qbf.mk_false ()
  in
  
  Qbf.mk_and [
    Qbf.mk_or @@ List.map is_readable reads
  ; MM.valid_conf es c'
  ; MM.equal q q'
  ]

let fulfil es co evt (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> printf "\n=== entering fulfill ===\n");
  let is_fulfillable w = Qbf.mk_and [
      follows_config es c w
    ; MM._in [w] q
    ; coh es co rf
    ; grows_by es c c' [w]
    ; b_to_qbf (List.mem (evt, w) (EventStructure.order_tc es))
    ]
  in
  Qbf.mk_and [
    Qbf.mk_or @@ List.map is_fulfillable (EventStructure.events es)
  ; MM.valid_conf es c
  ; MM.equal q q'
  ; MM.equal rf rf'
  ]

let thread_step es co evt (c,q,rf) (c',q',rf') =
  debug @@ (fun x -> printf "entering promise_step\n");
  Qbf.mk_or [
    promise es co evt (c,q,rf) (c',q',rf')
  ; read    es co evt (c,q,rf) (c',q',rf')
  ; fulfil es co evt (c,q,rf) (c',q',rf')
  ]
                
let promise_step es co (c,q,rf) (c',q',rf') =
  debug @@ (fun () -> printf "entering thread_step");
  let rec step es co (c,q,rf) (c',q',rf') =
    Qbf.mk_or @@ List.map (fun evt -> Qbf.mk_and [
        follows_config es c evt
      ; consistent es (c',q',rf') 0
      ; thread_step es co evt (c,q,rf) (c',q',rf')
      ]) (EventStructure.events es)
  and do_step (c,q,rf) (c', q', rf') n =
    let c'' = MM.fresh_so_var es 1  ~prefix:"c''" in
    let q'' = MM.fresh_so_var es 1  ~prefix:"q''" in
    let rf'' = MM.fresh_so_var es 2 ~prefix:"rf''" in
    match n with
      0 -> Qbf.mk_false()
    | _ ->
      MM.exists c'' @@
      MM.exists q'' @@
      MM.exists rf'' @@
      Qbf.mk_or [
        step es co (c,q,rf) (c',q',rf')
      ; Qbf.mk_and [
          step es co (c,q,rf) (c',q',rf')
        ; do_step (c',q',rf') (c'',q'',rf'') (n-1)
        ]
      ]
  and consistent es (c,q,rf) n =
    let c' = MM.fresh_so_var es 1 ~prefix:"c'" in
    let q' = MM.fresh_so_var es 1 ~prefix:"q'" in
    let rf' = MM.fresh_so_var es 2 ~prefix:"rf'" in
    MM.exists c' @@
    MM.exists q' @@
    MM.exists rf' @@
    do_step (c,q,rf) (c',q',rf') n
  in
  let c' = MM.fresh_so_var es 1 ~prefix:"c'" in
  let q' = MM.fresh_so_var es 1 ~prefix:"q'" in
  let rf' = MM.fresh_so_var es 2 ~prefix:"rf'" in
  MM.exists c' @@
  MM.exists q' @@
  MM.exists rf' @@
  do_step (c,q,rf) (c',q',rf') ((EventStructure.events_number es) + (List.length (EventStructure.writes es)))


let promising es co (c,q,rf) goal =
  debug @@ (fun x -> printf "entering promising\n");
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
        ; Qbf.mk_and [
            promise_step es co (c,q,rf) (c',q',rf')
          ; do_step (c', q', rf') (n-1)
          ]
        ]
    in
    MM.exists c' @@
    MM.exists q' @@
    MM.exists rf' r
  in
  do_step (c,q,rf) ((EventStructure.events_number es) + (List.length (EventStructure.writes es)))

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

