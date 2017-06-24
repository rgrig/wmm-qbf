(* Naming conventions:
  x, y, z, ...    configurations
  u, v, q, ...    predicates
  p, q, r, ...    relations
  a, b, c, ...    formulas
  es              event structure
*)

open Printf

module E = EventStructure
module U = Util

type configuration =
  { prefix : string
  ; event_structure : E.t }

let size_of x =
  x.event_structure.E.events_number

let same_es x y =
  x.event_structure = y.event_structure
let name x i =
  let n = size_of x in
  assert (1 <= i);
  assert (i <= n);
  sprintf "%sE%d" x.prefix i
let var x i =
  Qbf.mk_var @@ name x i
let allnames x =
  let n = size_of x in
  List.map (name x) (U.range 1 n)


type predicate = configuration -> Qbf.t
type relation = configuration -> configuration -> Qbf.t

let justifies es =
  let h = Hashtbl.create 0 in
  List.iter (fun j -> Hashtbl.replace h j []) es.E.reads;
  let add (i, j) =
    let is = Hashtbl.find h j in
    Hashtbl.replace h j (i :: is) in
  List.iter add es.E.justifies;
  (fun x y ->
    assert (es = x.event_structure);
    assert (es = y.event_structure);
    let justify_read j =
      let b = Qbf.mk_or @@ List.map (var x) (Hashtbl.find h j) in
      let b = Qbf.mk_or [b; var x j] in (* tweak: justify only new *)
      Qbf.mk_implies [var y j] b in
    Qbf.mk_and @@ List.map justify_read es.E.reads)

let valid_conf es x =
  let downclosed =
    let f (i, j) = Qbf.mk_implies [var x j] (var x i) in
    Qbf.mk_and @@ List.map f es.E.order in
  let no_conflict =
    let f (i, j) = Qbf.mk_not (Qbf.mk_and [var x i; var x j]) in
    Qbf.mk_and @@ List.map f es.E.conflicts in
  Qbf.mk_and [ downclosed; no_conflict ]

let valid_rel es x y =
  Qbf.mk_and [ valid_conf es x; valid_conf es y ]

let fresh_configuration =
  let n = ref 0 in
  (fun es -> incr n; { prefix = sprintf "C%d" !n; event_structure = es } )

let forall x a =
  Qbf.mk_forall (allnames x) a
let exists x a =
  Qbf.mk_exists (allnames x) a
let equals_set x is =
  let n = size_of x in
  let f i =
    if List.mem i is then var x i else Qbf.mk_not (var x i) in
  Qbf.mk_and @@ List.map f (U.range 1 n)

let subset x y =
  assert (same_es x y);
  let n = size_of x in
  let f i = Qbf.mk_implies [var x i] (var y i) in
  Qbf.mk_and @@ List.map f (U.range 1 n)

let flip p x y = p y x
let intersect p q x y = Qbf.mk_and [p x y; q x y]
let union p q x y = Qbf.mk_or [p x y; q x y]

let equal = intersect subset (flip subset)

let sequence es p q = fun x z ->
  let y = fresh_configuration es in
  exists y (Qbf.mk_and [p x y; q y z])

let rec at_most_n es n p =
  if n = 0
  then equal
  else union equal (sequence es p (at_most_n es (n-1) p))

let set_of_model x ms =
  failwith "hcsea"
