open JR
open Printf

let acyclic_just es x y =
  Qbf.mk_and [
    MM.justifies es x y
  ; MM.valid_conf es y
  ]
    
let do_decide es can must solver_opts =
  let x = MM.fresh_so_var es 1 in
  let y = MM.fresh_so_var es 1 in

  let q = Qbf.mk_and
    [ MM.equals_set x []
    ; MM.equals_set y target
    ; MM.valid_conf es y
    ; (MM.at_most_n es (EventStructure.events_number es) (acyclic_just es)) x y] in
  let q = MM.exists x (MM.exists y q) in
  match Config.use_solver () with
    Some (Config.SolveQbf) -> printf "result: %b\n" (Qbf.holds q)
  | Some _ -> failwith "This model requires the Qbf solver."
  | None -> ()
