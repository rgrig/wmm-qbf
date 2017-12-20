open PES
open Printf

(* The expected (Configuration, Promises) transitions of the model on the following program:

   if(x == 0)
     y = 1;
   else
     y = 0;

   expect y = 1
*)
(* jctc6*)
    (*
let expected_transitions = [
  ([], [])
; ([], [1])
; ([1], [1])
; ([1], [1;6])
; ([1;2], [1;6])
; ([1;2], [1;6;3])
; ([1;2;3], [1;6;3])
; ([1;2;3;5], [1;6;3])
; ([1;2;3;5;6], [1;6;3])
]


let expected_transitions = [
  ([],[])
; ([],[1])
; ([1],[1])
; ([1;2],[1])
; ([1;2],[1;3])
; ([1;2;3],[1;3])
; ([1;2;3;5],[1;3])
; ([1;2;3;5],[1;3;6])
; ([1;2;3;5;6],[1;3;6])
]
*)

(* jctc4 *)
let expected_transitions = [
  ([],[])
; ([],[1])
; ([1],[1])
; ([1;2],[1])
; ([1;2],[1;3])
; ([1;2;3],[1;3])
; ([1;2;3;6],[1;3])
; ([1;2;3;6],[1;3;7])
; ([1;2;3;6;7],[1;3;7])
]
(*
let expected_transitions = [
  ([],[])
; ([],[1])
; ([1],[1])
; ([1],[1;3])
; ([1;3],[1;3])
; ([1;3;6],[1;3])
; ([1;3;6],[1;3;7])
; ([1;3;6;2],[1;3;7])
; ([1;3;6;2;7],[1;3;7])
]
*)
let last xs = List.hd (List.rev xs)

let promising es conf proms goal =
  (* let writes = EventStructure.writes es in *)
  let rec do_step (conf, proms) evs =
    let conf' = MM.fresh_so_var es 1 in
    let proms' = MM.fresh_so_var es 1 in
    let r = (match evs with
        | [] -> MM.equal conf goal
        | (c', p') :: evs ->
          Qbf.mk_and [
            MM.equals_set conf' c'
          ; MM.equals_set proms' p'
          ; Qbf.mk_or [
              MM.equal conf goal
            ; Qbf.mk_and @@ [
                MM.valid_conf es conf'
              ; promise_step es (conf,proms) (conf',proms')
              ; do_step (conf', proms') evs
              ] (* @ List.map (fun e -> Qbf.mk_implies [MM._in [e] proms] (certifiable es e conf)) writes *)
            ]])
    in
    MM.exists conf' @@ MM.exists proms' @@ r
  in
  do_step (conf, proms) expected_transitions

(* Find out if these 3 are the only quantified variables. Name them
   and check the QCIR. Compare to J+R. *)
let do_decide es target solver_opts =
  let c = MM.fresh_so_var es 1 ~prefix:"conf" in
  let p = MM.fresh_so_var es 1 ~prefix:"proms" in  
  let g = MM.fresh_so_var es 1 ~prefix:"goal" in
  let q = Qbf.mk_and [
      MM.equals_set c []
    ; MM.equals_set p []
    (* Can we make it to the last conf? *)
    ; MM.equals_set g (fst @@ last expected_transitions)
    ; MM.valid_conf es c
    ; MM.valid_conf es g
    ; promising es c p g
    ] in
  let q = MM.exists c
    @@ MM.exists p
    @@ MM.exists g q
  in
  match Config.use_solver () with
    Some (Config.SolveQbf) -> printf "result: %b\n" (Qbf.holds q)
  | Some _ -> failwith "This model requires the Qbf solver."
  | None -> ()
