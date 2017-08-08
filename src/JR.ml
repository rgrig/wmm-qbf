module E = EventStructure

(* TODO: optimize validity checks; think sequence, and correctness. *)
         
(* Always Justifies *)
let always_justifies es = MM.intersect_n [ MM.subset; MM.justifies es; MM.valid_rel es ]


(* Always Justifies

   There is a proof burden to show that applying that relation n times
   gives totality to the model.
 *)
let always_justifies_tc es = MM.at_most_n es es.E.events_number (always_justifies es)

(* Always Eventually Justifies 

   This relation contains always_justifies which is applied n times.
 *)
let always_eventually_justifies es =
  let justifies = MM.justifies es in
  let aj_tc = always_justifies_tc es in
  let sequence = MM.sequence es in
  let ae_justifies =
    (fun x y ->
      let z = MM.fresh_so_var es 1 in
      MM.forall z
        (Qbf.mk_implies
          [aj_tc x z]
          (sequence aj_tc justifies z y))) in
  (* Query: in the doc, we do not check valid_rel here. *)
  MM.intersect_n [ MM.subset; ae_justifies; MM.valid_rel es ]

(* Always Eventually Justifies Transitively Closed
   
   Similar to Always Justifies there is a proof burden to show that
   appling the relation n times is total.
 *)
let always_eventually_justifies_tc es = MM.at_most_n es es.E.events_number (always_eventually_justifies es)

(* Comment: the division between the description of the model given here and the
    built-in functions seems less than ideal right now.

     - Do we have to have the model writer ask for a fresh configuration, or could that be
        within the MM.forall function.

     - Also, there are bits buried in MM.ml that the model writer might want to have their
        hands on: we can't write the distinction between bug-fixed J+R and paper J+R at
        the moment.

    Query: Where is the goal represented?
     - In JRCheck.ml
 *)
