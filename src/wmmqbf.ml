open Printf

module U = Util

let do_one fn =
  let wmm = U.parse fn in
  let n = wmm.Wmm.events in
  let mV prefix bounds at =
    let spec = U.mk_var prefix bounds in
    let get = at spec in
    (spec, get) in
  let empty_set_spec, empty_set = mV "Z" [1,n] U.at1 in
  let execution_set_spec, execution_set = mV "E" [1,n] U.at1 in
  let c_spec, c = mV "c" [0,n; 1,n] U.at2 in
  let d_spec, d = mV "d" [1,n; 1,n] U.at2 in
  let e_spec, e = mV "e" [1,n; 1,n] U.at2 in
  let f_spec, f = mV "f" [1,n; 0,n; 1,n] U.at3 in
  let g_spec, g = mV "g" [1,n; 0,n; 1,n] U.at3 in
  let implies x y = Qbf.mk_and @@
    List.map (fun i -> Qbf.mk_implies (x i) (y i)) (U.range 1 n) in
  let equal x y = Qbf.mk_and [implies x y; implies y x] in
  let justifies = (* justify all: current def 4.2 *)
    let js = Hashtbl.create (List.length wmm.Wmm.reads) in
    let init w = Hashtbl.replace js w [] in
    let add (x, y) = Hashtbl.replace js y (x :: Hashtbl.find js y) in
    List.iter init wmm.Wmm.reads;
    List.iter add wmm.Wmm.justifies;
    (fun write read ->
      let one y xs qs =
        (* XXX: justify new: our attempt at fixing 4.2 *)
        Qbf.mk_implies (read y) (Qbf.mk_or @@ write y :: List.map write xs) :: qs in
      Qbf.mk_and @@ Hashtbl.fold one js []) in
  let valid =
    let ok_order x =
      let one (i, j) = Qbf.mk_implies (x j) (x i) in
      Qbf.mk_and @@ List.map one wmm.Wmm.order in
    let ok_conflicts x =
      let one (i, j) = Qbf.mk_not @@ Qbf.mk_and [x i; x j] in
      Qbf.mk_and @@ List.map one wmm.Wmm.conflicts in
    (fun x -> Qbf.mk_and [ok_order x; ok_conflicts x]) in
  let v1 l h x = List.map (fun k -> valid (x k)) (U.range l h) in
  let v2 l1 h1 l2 h2 x =
    List.concat @@ List.map (fun k -> v1 l2 h2 (x k)) (U.range l1 h1) in
  let transitive_closure rel x ys z =
    (* let n = 1 in (* DBG *) *)
    let rel ys k = Qbf.mk_or [ rel ys k ; equal (ys (k-1)) (ys k) ] in
    Qbf.mk_and @@
    equal x (ys 0)
    :: equal (ys n) z
    :: List.map (rel ys) (U.range 1 n) in
  let step0 fg k = Qbf.mk_and
    [ implies (fg (k - 1)) (fg k)
    ; justifies (fg (k - 1)) (fg k) ] in
  let step1 c k = Qbf.mk_and
    [ implies (c (k - 1)) (c k)
    ; Qbf.mk_implies
        (Qbf.mk_and @@
          transitive_closure step0 (c (k - 1)) (f k) (d k)
          :: v1 1 n (f k))
        (Qbf.mk_and
          [ transitive_closure step0 (d k) (g k) (e k)
          ; justifies (e k) (c k) ])
    ] in
  let is_set x js =
    let one j =
      if List.mem j js
      then x j
      else Qbf.mk_not (x j) in
    Qbf.mk_and @@ List.map one (U.range 1 n) in
  let q = Qbf.mk_and
    [ is_set empty_set []
    ; is_set execution_set wmm.Wmm.execution
    ; transitive_closure step1 empty_set c execution_set ] in
  let q = Qbf.mk_and @@ List.concat
    [ [ q ]
    ; v1 1 n e
    ; v2 1 n 0 n g ] in
  let q = Qbf.mk_implies (Qbf.mk_and (v1 1 n d)) q in
  let q = Qbf.mk_and (q :: v1 0 n c) in

  let q = Qbf.mk_qbf q in
  let q = Qbf.mk_exists (U.var_allnames g_spec) q in
  let q = Qbf.mk_exists (U.var_allnames e_spec) q in
  let q = Qbf.mk_forall (U.var_allnames f_spec) q in
  let q = Qbf.mk_forall (U.var_allnames d_spec) q in
  let q = Qbf.mk_exists (U.var_allnames c_spec) q in
  let q = Qbf.mk_exists (U.var_allnames empty_set_spec) q in
  let q = Qbf.mk_exists (U.var_allnames execution_set_spec) q in

  printf "%a" Qbf.pp_qcir q

let () =
  Arg.parse [] do_one "wmmqbf <infile>"
