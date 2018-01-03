open PES
open Printf

let do_decide es target =
  let c = MM.fresh_so_var es 1 in
  let p = MM.fresh_so_var es 1 in
  let c' = MM.fresh_so_var es 1 in
  let p' = MM.fresh_so_var es 1 in
  let q = Qbf.mk_and [
      MM.equals_set c []
    ; MM.equals_set p [1]
    ; MM.equals_set c' [1]
    ; MM.equals_set p' [1]
    (* Can we make it to the last conf? *)
    ; promise_read es (c, p) (c', p')
    ] in
  let q = MM.exists c
    @@ MM.exists p
    @@ MM.exists c'
    @@ MM.exists p' q
  in
  match Config.use_solver () with
    Some (Config.SolveQbf) -> printf "result: %b\n" (Qbf.holds q)
  | Some _ -> failwith "This model requires the Qbf solver."
  | None -> ()
