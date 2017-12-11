(* Naming conventions:
  x, y, z, ...    configurations
  u, v, q, ...    predicates
  p, q, r, ...    relations
  P, Q, R  ...    quantified relation
  a, b, c, ...    formulas
  es              event structure
*)

open Printf

module E = EventStructure
module U = Util

(* These structures are quantified. They only need a prefix for their
   QBF variables *)
type so_var  =
  { prefix : string
  ; arity : int
  ; event_structure : E.t }

type 'a predicate = 'a -> Qbf.t
type relation = so_var -> so_var -> Qbf.t
exception Bad_arity

let size_of x =
  x.event_structure.E.events_number

let same_es x y =
  x.event_structure = y.event_structure

(* Builds a name from the list of indexes. Indexes are separated by
   underscores *)
let name x is =
  let rec f xs = match xs with
    | [x] -> string_of_int x
    | x::xs -> string_of_int x ^ "_" ^ f xs
    | [] -> ""
  in
  sprintf "%sR%s" x.prefix (f is)

(* Generates a variable string, with indexes from list is *)
let var x is =
  if (x.arity != List.length is) then raise Bad_arity;
  SO.QRel (x.prefix, is)

let _in is x =
  var x is

(* TODO: Should be deprecated, together with [MM.so_var]. *)
(* Builds all the names for a given SO variable, e.g. C01R1_1,
   C01R1_2, ... *)
let allnames x =
  let n = size_of x in
  let rec lists xs i = match i with
    | 0 -> []
    | n -> xs :: lists xs (i - 1)
  in
  let names = U.n_cartesian_product (lists (U.range 1 n) (x.arity)) in
  List.map (name x) names
  
let justifies es =
(* TODO (low priority): explain this to Mark. *)
  let h = Hashtbl.create 0 in
  List.iter (fun j -> Hashtbl.replace h (SO.Const j) []) es.E.reads;
  let add (i, j) =
    let is = Hashtbl.find h (SO.Const j) in
    Hashtbl.replace h (SO.Const j) (i :: is) in
  List.iter add es.E.justifies;
  (fun x y ->
    assert (es = x.event_structure);
    assert (es = y.event_structure);
    let justify_read j =
      let b = SO.Or (List.map (fun i -> var x [SO.Const i]) (Hashtbl.find h (SO.Const j))) in
      let b = SO.Or [b; var x [SO.Const j]] in (* tweak: justify only new *)
      SO.mk_implies [var y [SO.Const j]] b in
    SO.And (List.map justify_read es.E.reads)
  )
  
let valid_conf es x =
  let downclosed =
    let f (i, j) = SO.mk_implies [var x [SO.Const j]] (var x [SO.Const i]) in
    SO.And (List.map f es.E.order)
  in
(* Query: this differs from the definition in the doc. Why? *)
  let no_conflict =
    let f (i, j) = SO.Not (SO.And [var x [SO.Const i]; var x [SO.Const j]]) in
    SO.And (List.map f es.E.conflicts)
  in
  SO.And [ downclosed; no_conflict ]

let compose x rel =
  List.map snd (List.filter (fun (l,r) -> x == l) rel)

let pre_compose x rel =
  List.map fst (List.filter (fun (l,r) -> x == r) rel)

let same_label es x y =
  (* remember that in OCaml `=' does structural equality checking and
     `==' does reference equality checking. This was previously the
     source of a bug. *)
  if List.mem x (EventStructure.reads es) then
    (pre_compose x (EventStructure.justifies es)) = pre_compose y (EventStructure.justifies es)
  else
    (compose x (EventStructure.justifies es)) = compose y (EventStructure.justifies es)
       

let valid_rel es x y =
  SO.And [ valid_conf es x; valid_conf es y ]

let fresh_so_var = 
  let n = ref 0 in
  (fun ?(prefix = "C") es a ->
     incr n; { prefix = sprintf "%s%d" prefix !n; arity = a; event_structure = es } )

let forall x a =
  SO.SoAll (x.prefix, x.arity, a)

let exists x a =
  SO.SoAny (x.prefix, x.arity, a)
  
let equals_set x is =
  let n = size_of x in
  let f i =
    if List.mem i is then var x [SO.Const i] else SO.Not (var x [SO.Const i])
  in
  SO.And (List.map f (U.range 1 n))
  
let writes es w =
  let writes = EventStructure.writes es in
  equals_set w writes

let subset x y =
  assert (same_es x y);
  let n = size_of x in
  let f i = SO.mk_implies [var x [SO.Const i]] (var y [SO.Const i]) in
  SO.And (List.map f (U.range 1 n))

let flip p x y = p y x

let intersect p q x y = SO.And [p x y; q x y]
let union p q x y = SO.Or [p x y; q x y]

let set_union es x e =
  assert (x.arity == 1);
  let n = size_of x in
  let xn = fresh_so_var es 1 in
  let f i = SO.Or [SO.mk_implies [var xn [SO.Const i]] (var x [SO.Const i]); var xn e] in
  let g i = SO.Or [SO.mk_implies [var x [SO.Const i]] (var xn [SO.Const i])] in
  SO.SoAny (xn.prefix, 1,
            SO.And [
              SO.And (List.map f (U.range 1 n))
            ; SO.And (List.map g (U.range 1 n))
            ]
           )
  
let intersect_n ps x y =
  SO.And (List.map (fun p -> p x y) ps)
let union_n ps x y =
  SO.Or (List.map (fun p -> p x y) ps)

let equal = intersect subset (flip subset)

(* reflexive r ≜ ∀x∈Dom. r x x *)
let reflexive es r =
  let n = size_of r in
  SO.And (List.map (fun i -> var r [SO.Const i; SO.Const i]) (U.range 1 n))

let irreflexive es r =
  let n = size_of r in
  SO.And (List.map (fun i -> SO.Not (var r [SO.Const i; SO.Const i])) (U.range 1 n))

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
  let x = size_of a in
  let sub a b =
    let f xs =
      match xs with
        [i;j] -> SO.mk_implies [var a [SO.Const i; SO.Const j]] (var b [SO.Const i; SO.Const j])
      | _ -> raise (U.Runtime_error "") (* compiler warns without this *)
    in
    List.map f (U.n_cartesian_product [(U.range 1 x); (U.range 1 x)])
  in
  SO.And (sub a b)


let sequence es p q = fun x z ->
  assert (x.arity == z.arity);
  let y = fresh_so_var es x.arity in
  SO.SoAny (y.prefix, y.arity, SO.And [p x y; q y z])

(* transitive r ≜ ∀x,y,z ∈ Dom . r x y ∧ r y z → r x z *)
let transitive es r =
  let n = size_of r in
  (* !!! *)
  (*  subset (sequence es r r) r *)
  let f x y z = SO.mk_implies [
      SO.And [var r [SO.Const x; SO.Const y]; var r [SO.Const y; SO.Const z]]
    ]
      (var r [SO.Const x; SO.Const z])
  in
  SO.And (map3 f (U.range 1 n) (U.range 1 n) (U.range 1 n))


(* ∃x . y⁺ ⊆ x *)
let trancl es y =
  let x = fresh_so_var es 2 in
  let x_is_trans = transitive es x in
  SO.SoAny (x.prefix, x.arity, SO.And [x_is_trans; subset_r y x])

let rec at_most_n es n p =
  if n = 0
  then equal
  else union equal (sequence es p (at_most_n es (n-1) p))

let set_of_model x m =
  let p i = List.mem (name x [i]) m in
  List.filter p (U.range 1 (size_of x))
