open PES
open Printf

let maybe a f =
  match a with
    Some a' -> f a'
  | None -> ()

let do_decide es target solver_opts =
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
  maybe (Qbf.holds q solver_opts) (printf "result: %b")
