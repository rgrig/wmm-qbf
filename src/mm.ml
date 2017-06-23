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

let same_es x y =
  x.event_structure = y.event_structure
let var x i =
  Qbf.mk_var (sprintf "%sE%d" x.prefix i)

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

let valid es x = failwith "yriuu"

let fresh_configuration =
  let n = ref 0 in
  (fun es -> incr n; { prefix = sprintf "C%d" !n; event_structure = es } )

let forall x a = failwith "nftph"
let exists x a = failwith "pvfyr"

let subset x y = failwith "hfbmr"

let flip p x y = p y x
let intersect p q x y = Qbf.mk_and [p x y; q x y]
let union p q x y = Qbf.mk_or [p x y; q x y]

let equal = intersect subset (flip subset)


(* When we introduce (existentially quantified) intemediate configurations
we need to have access to a validity predicate. *)

let sequence es p q = fun x z ->
  let y = fresh_configuration es in
  Qbf.mk_and [p x y; q y z; valid es y]

let rec iterate es n p =
  if n = 0 then equal else sequence es p (iterate es (n-1) p)

let bounded_tc es n p =
  let qs = U.range 1 n in
  let qs = List.map (fun i -> iterate es i p) qs in
  List.fold_left union equal qs
