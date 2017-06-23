module E = EventStructure

let step0 es = Mm.intersect (Mm.subset) (Mm.justifies es)
let step0tc es = Mm.bounded_tc es es.E.events_number (step0 es)

let step1 es =
  let justifies = Mm.justifies es in
  let step0tc = step0tc es in
  let valid = Mm.valid es in
  let sequence = Mm.sequence es in
  (fun x y ->
    let z = Mm.fresh_configuration es in
    Mm.forall z
      (Qbf.mk_implies
        [valid z; step0tc x z]
        (sequence step0tc justifies z y)))
let step1tc es = Mm.bounded_tc es es.E.events_number (step1 es)
