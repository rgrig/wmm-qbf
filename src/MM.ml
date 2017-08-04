(* Naming conventions:
  x, y, z, ...    configurations
  u, v, q, ...    predicates
  p, q, r, ...    relations
  Rl       ...    quantified relation
  a, b, c, ...    formulas
  es              event structure
*)

open Printf

module E = EventStructure
module U = Util

(* These structures are quantified. They only need a prefix for their
   QBF variables *)
type configuration =
  { prefix : string
  ; event_structure : E.t }
type q_relation =
  { prefix : string
  ; event_structure : E.t }

let size_of (x:configuration) =
  x.event_structure.E.events_number
let same_es (x:configuration) (y:configuration) =
  x.event_structure = y.event_structure
let name (x:configuration) i =
  let n = size_of x in
  assert (1 <= i);
  assert (i <= n);
  sprintf "%sE%d" x.prefix i
let var (x:configuration) i =
  Qbf.mk_var @@ name x i
let allnames (x:configuration) =
  let n = size_of x in
  List.map (name x) (U.range 1 n)

(* TODO: This should be turned round into a working implementation of arity 2 SO
     variables, but it is unlikely to perform well. Radu suggested an encoding of relations
     that uses log(mumble) quantified variables. You should fix this up, make sure you
     understand it, and then implement Radu's suggestion. Make a new memory model
     (a replacement for JR.ml) that uses arity 2 SO variables to test the implementation.  *)
let size_ofr (r:q_relation) =
  r.event_structure.E.events_number
let same_esr (x:q_relation) y =
  x.event_structure = y.event_structure
let namer (x:q_relation) i j =
  let n = size_ofr x in
  assert (1 <= i);
  assert (i <= n);
  assert (j <= n);
  sprintf "%sE%d%d" x.prefix i j
let varr (x:q_relation) i j =
  Qbf.mk_var @@ namer x i j
let allnamesr (x:q_relation) =
  let n = size_ofr x in
  List.map (namer x) (U.range 1 n)


type 'a predicate = 'a -> Qbf.t
type relation = configuration -> configuration -> Qbf.t

let justifies es =
(* TODO (low priority): explain this to Mark. *)
  let h = Hashtbl.create 0 in
  List.iter (fun j -> Hashtbl.replace h j []) es.E.reads;
  let add (i, j) =
    let is = Hashtbl.find h j in
    Hashtbl.replace h j (i :: is) in
  List.iter add es.E.justifies;
  (fun (x:configuration) (y:configuration) ->
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
(* Query: this differs from the definition in the doc. Why? *)
  let no_conflict =
    let f (i, j) = Qbf.mk_not (Qbf.mk_and [var x i; var x j]) in
    Qbf.mk_and @@ List.map f es.E.conflicts in
  Qbf.mk_and [ downclosed; no_conflict ]

let valid_rel es x y =
  Qbf.mk_and [ valid_conf es x; valid_conf es y ]

let fresh_configuration : E.t -> configuration =
  let n = ref 0 in
  (fun es -> incr n; { prefix = sprintf "C%d" !n; event_structure = es } )

let forall (x:configuration) a =
  Qbf.mk_forall (allnames x) a

let exists (x:configuration) a =
  Qbf.mk_exists (allnames x) a

let equals_set x is =
  let n = size_of x in
  let f i =
    if List.mem i is then var x i else Qbf.mk_not (var x i) in
  Qbf.mk_and @@ List.map f (U.range 1 n)
   
let subset (x:configuration) (y:configuration) =
  assert (same_es x y);
  let n = size_of x in
  let f i = Qbf.mk_implies [var x i] (var y i) in
  Qbf.mk_and @@ List.map f (U.range 1 n)

let flip p x y = p y x

let intersect p q x y = Qbf.mk_and [p x y; q x y]
let union p q x y = Qbf.mk_or [p x y; q x y]

let intersect_n ps x y =
  Qbf.mk_and @@ List.map (fun p -> p x y) ps
let union_n ps x y =
  Qbf.mk_or @@ List.map (fun p -> p x y) ps

let equal = intersect subset (flip subset)

let fresh_relation =
  let n = ref 0 in
  (fun es -> incr n; { prefix = sprintf "Rl%d" !n; event_structure = es})

(* reflexive r ≜ ∀x∈Dom. r x x *)
let reflexive es r =
  let n = size_ofr r in
  Qbf.mk_and @@ List.map (fun i -> varr r i i) (U.range 1 n)

let irreflexive es r =
  let n = size_ofr r in
  Qbf.mk_and @@ List.map (fun i -> Qbf.mk_not (varr r i i)) (U.range 1 n)                         
                         
exception Unreachable of string
(* TODO: There's got to be a better way... *)
let map3 (f : 'a -> 'b -> 'c -> 'd) (a: 'a list) (b: 'b list) (c: 'c list) : 'd list =
  let oa, ob, oc = a, b, c in
  let rec inner_map ai bi ci =
    match ai,bi,ci with
      ai::ais, bi::bis, ci::cis -> f ai bi ci :: inner_map (ai::ais) (bi::bis) cis
    | ai::ais, bi::bis, [] -> inner_map (ai::ais) bis oc
    | ai::ais, [], [] -> inner_map ais ob oc
    | [], [], [] -> []
    | _ -> raise (Unreachable "")
  in
  inner_map oa ob oc

(* a ⊆ b *)
let subset_r a b =
  let x = size_ofr a in
  let sub a b = List.flatten (List.map (fun i -> List.map (fun j -> Qbf.mk_implies [varr a i j] (varr b i j)) (U.range 1 x))  (U.range 1 x)) in
  Qbf.mk_and @@ (sub a b)

(* transitive r ≜ ∀x,y,z∈Dom . r x y ∧ r y z → r x z *)
let transitive es r =
  let n = size_ofr r in
  let f x y z = Qbf.mk_implies [Qbf.mk_and [varr r x y; varr r y z]] (varr r x z) in
  Qbf.mk_and @@ map3 f (U.range 1 n) (U.range 1 n) (U.range 1 n)

(* ∃x . y⁺ ⊆ x *)
let trancl es y =
  let x = fresh_relation es in
  let x1 = transitive es x in
  Qbf.mk_and @@ [x1; subset_r y x]

let sequence es p q = fun x z ->
  let (y:configuration) = fresh_configuration es in
  exists y (Qbf.mk_and [p x y; q y z])

let rec at_most_n es n p =
  if n = 0
  then equal
  else union equal (sequence es p (at_most_n es (n-1) p))

let set_of_model x m =
  let p i = List.mem (name x i) m in
  List.filter p (U.range 1 (size_of x))
