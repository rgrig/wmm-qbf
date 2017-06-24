module E = EventStructure

let step0 es = MM.intersect (MM.subset) (MM.justifies es)
let step0tc es = MM.at_most_n es es.E.events_number (step0 es)

let step1 es =
  let justifies = MM.justifies es in
  let step0tc = step0tc es in
  let valid = MM.valid es in
  let sequence = MM.sequence es in
  (fun x y ->
    let z = MM.fresh_configuration es in
    MM.forall z
      (Qbf.mk_implies
        [valid z; step0tc x z]
        (sequence step0tc justifies z y)))
let step1tc es = MM.at_most_n es es.E.events_number (step1 es)
