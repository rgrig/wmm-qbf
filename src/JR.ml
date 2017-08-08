module E = EventStructure

(* TODO: optimize validity checks; think sequence, and correctness. *)
(* TODO: make names consistent with writeup (and not horrible), e.g. step0 --> AJ *)
(* AJ *) let step0 es = MM.intersect_n [ MM.subset; MM.justifies es; MM.valid_rel es ]
(* AJ^tc_n *) let step0tc es = MM.at_most_n es es.E.events_number (step0 es)

(* AeJ_n*) let step1 es =
  let justifies = MM.justifies es in
  let step0tc = step0tc es in
  let sequence = MM.sequence es in
  let ae_justifies =
    (fun x y ->
      let z = MM.fresh_so_var es 1 in
      MM.forall z
        (Qbf.mk_implies
          [step0tc x z]
          (sequence step0tc justifies z y))) in
(* Query: in the doc, we do not check valid_rel here. *)
  MM.intersect_n [ MM.subset; ae_justifies; MM.valid_rel es ]
(* AeJ^tc_n_n*) let step1tc es = MM.at_most_n es es.E.events_number (step1 es)

(* Comment: the division between the description of the model given here and the
    built-in functions seems less than ideal right now.

     - Do we have to have the model writer ask for a fresh configuration, or could that be
        within the MM.forall function.

     - Also, there are bits buried in MM.ml that the model writer might want to have their
        hands on: we can't write the distinction between bug-fixed J+R and paper J+R at
        the moment.

    Query: Where is the goal represented?
 *)
