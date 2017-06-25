module E = EventStructure

(* TODO: optimize validity checks; think sequence, and correctness. *)
let step0 es = MM.intersect_n [ MM.subset; MM.justifies es; MM.valid_rel es ]
let step0tc es = MM.at_most_n es es.E.events_number (step0 es)

let step1 es =
  let justifies = MM.justifies es in
  let step0tc = step0tc es in
  let sequence = MM.sequence es in
  let ae_justifies =
    (fun x y ->
      let z = MM.fresh_configuration es in
      MM.forall z
        (Qbf.mk_implies
          [step0tc x z]
          (sequence step0tc justifies z y))) in
  MM.intersect_n [ MM.subset; ae_justifies; MM.valid_rel es ]
let step1tc es = MM.at_most_n es es.E.events_number (step1 es)
