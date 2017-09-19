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
  Qbf.mk_var @@ name x is

let _in is x =
  var x is

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
  List.iter (fun j -> Hashtbl.replace h j []) es.E.reads;
  let add (i, j) =
    let is = Hashtbl.find h j in
    Hashtbl.replace h j (i :: is) in
  List.iter add es.E.justifies;
  (fun x y ->
    assert (es = x.event_structure);
    assert (es = y.event_structure);
    let justify_read j =
      let b = Qbf.mk_or @@ List.map (fun i -> var x [i]) (Hashtbl.find h j) in
      let b = Qbf.mk_or [b; var x [j]] in (* tweak: justify only new *)
      Qbf.mk_implies [var y [j]] b in
    Qbf.mk_and @@ List.map justify_read es.E.reads)
  
let valid_conf es x =
  let downclosed =
    let f (i, j) = Qbf.mk_implies [var x [j]] (var x [i]) in
    Qbf.mk_and @@ List.map f es.E.order in
(* Query: this differs from the definition in the doc. Why? *)
  let no_conflict =
    let f (i, j) = Qbf.mk_not (Qbf.mk_and [var x [i]; var x [j]]) in
    Qbf.mk_and @@ List.map f es.E.conflicts in
  Qbf.mk_and [ downclosed; no_conflict ]

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
  Qbf.mk_and [ valid_conf es x; valid_conf es y ]

let fresh_so_var = 
  let n = ref 0 in
  (fun ?(prefix = "C") es a -> incr n; { prefix = sprintf "%s%d" prefix !n; arity = a; event_structure = es } )

let forall x a =
  Qbf.mk_forall (allnames x) a

let exists x a =
  Qbf.mk_exists (allnames x) a
  
let equals_set x is =
  let n = size_of x in
  let f i =
    if List.mem i is then var x [i] else Qbf.mk_not (var x [i]) in
  Qbf.mk_and @@ List.map f (U.range 1 n)
  
let writes es w =
  let writes = EventStructure.writes es in
  equals_set w writes

let subset x y =
  assert (same_es x y);
  let n = size_of x in
  let f i = Qbf.mk_implies [var x [i]] (var y [i]) in
  Qbf.mk_and @@ List.map f (U.range 1 n)

let flip p x y = p y x

let intersect p q x y = Qbf.mk_and [p x y; q x y]
let union p q x y = Qbf.mk_or [p x y; q x y]

let set_union es x e =
  assert (x.arity == 1);
  let n = size_of x in
  let xn = fresh_so_var es 1 in
  let f i = Qbf.mk_or @@ [Qbf.mk_implies [var xn [i]] (var x [i]); var xn e] in
  let g i = Qbf.mk_or @@ [Qbf.mk_implies [var x [i]] (var xn [i])] in
  exists xn @@
    Qbf.mk_and [
        Qbf.mk_and @@ List.map f (U.range 1 n)
      ; Qbf.mk_and @@ List.map g (U.range 1 n)
      ]
  
let intersect_n ps x y =
  Qbf.mk_and @@ List.map (fun p -> p x y) ps
let union_n ps x y =
  Qbf.mk_or @@ List.map (fun p -> p x y) ps

let equal = intersect subset (flip subset)

(* reflexive r ≜ ∀x∈Dom. r x x *)
let reflexive es r =
  let n = size_of r in
  Qbf.mk_and @@ List.map (fun i -> var r [i;i]) (U.range 1 n)

let irreflexive es r =
  let n = size_of r in
  Qbf.mk_and @@ List.map (fun i -> Qbf.mk_not (var r [i;i])) (U.range 1 n)

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
        [i;j] -> Qbf.mk_implies [var a [i;j]] (var b [i;j])
      | _ -> raise (U.Runtime_error "") (* compiler warns without this *)
    in
    List.map f (U.n_cartesian_product [(U.range 1 x); (U.range 1 x)])
  in
  Qbf.mk_and @@ (sub a b)


let sequence es p q = fun x z ->
  assert (x.arity == z.arity);
  let y = fresh_so_var es x.arity in
  exists y (Qbf.mk_and [p x y; q y z])

(* transitive r ≜ ∀x,y,z ∈ Dom . r x y ∧ r y z → r x z *)
let transitive es r =
  let n = size_of r in
  (* !!! *)
  (*  subset (sequence es r r) r *)
  let f x y z = Qbf.mk_implies [Qbf.mk_and [var r [x;y]; var r [y;z]]] (var r [x;z]) in
  Qbf.mk_and @@ map3 f (U.range 1 n) (U.range 1 n) (U.range 1 n)


(* ∃x . y⁺ ⊆ x *)
let trancl es y =
  let x = fresh_so_var es 2 in
  let x_is_trans = transitive es x in
  exists x @@ Qbf.mk_and @@ [x_is_trans; subset_r y x]

let rec at_most_n es n p =
  if n = 0
  then equal
  else union equal (sequence es p (at_most_n es (n-1) p))

let set_of_model x m =
  let p i = List.mem (name x [i]) m in
  List.filter p (U.range 1 (size_of x))

(**/**)
(* Section ignored by ocamldoc *)
open OUnit
open EventStructure

let sample_conf = { prefix = "C01"
                  ; arity = 1
                  ; event_structure = { events_number = 4;
                                        reads = [];
                                        justifies = [];
                                        conflicts = [];
                                        order = [] }
                  }

let sample_rel = { prefix = "C02"
                  ; arity = 2
                  ; event_structure = { events_number = 4;
                                        reads = [];
                                        justifies = [];
                                        conflicts = [];
                                        order = [] }
                  }

let test_sizeof = "size of empty ES" >:: (fun () ->
    let x = fresh_so_var { events_number = 4; reads = []; justifies = []; conflicts = []; order = [] } 1 in
    let y = fresh_so_var { events_number = 0; reads = []; justifies = []; conflicts = []; order = [] } 1 in

    assert_equal 4 (size_of x);
    assert_equal 0 (size_of y);
  )

let test_name = "name var" >:: (fun () ->
    assert_equal "C01R1" (name sample_conf [1]);
    assert_equal "C02R1_1" (name sample_rel [1;1]);
  )

(* Naming FO variables matches SO variable arity *)
let test_var = "var" >:: (fun () ->
    assert_raises Bad_arity (fun () -> var sample_rel [1;2;3]);
    assert_raises Bad_arity (fun () -> var sample_rel [1]);
    assert_raises Bad_arity (fun () -> var sample_conf [1;3]);
    assert_raises Bad_arity (fun () -> var sample_conf [1;2;3]);

    (* Checking these do not raise an exception *)
    let _ = var sample_conf [1] in
    let _ = var sample_rel [1;1] in

    ()
  )

let test_subset = "subset" >:: (fun () ->
  let x = subset sample_conf sample_conf in
  assert_equal (Qbf.mk_and
                  [
                    Qbf.mk_implies [var sample_conf [1]] (var sample_conf [1]);
                    Qbf.mk_implies [var sample_conf [2]] (var sample_conf [2]);
                    Qbf.mk_implies [var sample_conf [3]] (var sample_conf [3]);
                    Qbf.mk_implies [var sample_conf [4]] (var sample_conf [4]);
                  ]
               ) x
  )

let test_subset_r = "subset_r" >:: (fun () ->
    let x = subset_r sample_rel sample_rel in
    assert_equal (Qbf.mk_and
                    [
                      Qbf.mk_implies [var sample_rel [1;1]] (var sample_rel [1;1]);
                      Qbf.mk_implies [var sample_rel [1;2]] (var sample_rel [1;2]);
                      Qbf.mk_implies [var sample_rel [1;3]] (var sample_rel [1;3]);
                      Qbf.mk_implies [var sample_rel [1;4]] (var sample_rel [1;4]);

                      Qbf.mk_implies [var sample_rel [2;1]] (var sample_rel [2;1]);
                      Qbf.mk_implies [var sample_rel [2;2]] (var sample_rel [2;2]);
                      Qbf.mk_implies [var sample_rel [2;3]] (var sample_rel [2;3]);
                      Qbf.mk_implies [var sample_rel [2;4]] (var sample_rel [2;4]);

                      Qbf.mk_implies [var sample_rel [3;1]] (var sample_rel [3;1]);
                      Qbf.mk_implies [var sample_rel [3;2]] (var sample_rel [3;2]);
                      Qbf.mk_implies [var sample_rel [3;3]] (var sample_rel [3;3]);
                      Qbf.mk_implies [var sample_rel [3;4]] (var sample_rel [3;4]);

                      Qbf.mk_implies [var sample_rel [4;1]] (var sample_rel [4;1]);
                      Qbf.mk_implies [var sample_rel [4;2]] (var sample_rel [4;2]);
                      Qbf.mk_implies [var sample_rel [4;3]] (var sample_rel [4;3]);
                      Qbf.mk_implies [var sample_rel [4;4]] (var sample_rel [4;4]);
                    ]
                 ) x
  )

let test_flip = "flip" >:: (fun () ->
    let pair = (fun x y -> (x,y)) in
    assert_equal (2,1) (flip pair 1 2)
  )

let sample_conf2 = { prefix = "C03"
                  ; arity = 1
                  ; event_structure = { events_number = 4;
                                        reads = [];
                                        justifies = [];
                                        conflicts = [];
                                        order = [] }
                  }

let test_subset2 = "subset 2" >:: (fun () ->
  let x = subset sample_conf sample_conf2 in
  assert_equal (Qbf.mk_and
                  [
                    Qbf.mk_implies [var sample_conf [1]] (var sample_conf2 [1]);
                    Qbf.mk_implies [var sample_conf [2]] (var sample_conf2 [2]);
                    Qbf.mk_implies [var sample_conf [3]] (var sample_conf2 [3]);
                    Qbf.mk_implies [var sample_conf [4]] (var sample_conf2 [4]);
                  ]
               ) x
  )
                 
let test_equal = "equal" >:: (fun () ->
  let x = equal sample_conf sample_conf2 in
  assert_equal (Qbf.mk_and [
                    Qbf.mk_and [
                        Qbf.mk_implies [var sample_conf [1]] (var sample_conf2 [1]);
                        Qbf.mk_implies [var sample_conf [2]] (var sample_conf2 [2]);
                        Qbf.mk_implies [var sample_conf [3]] (var sample_conf2 [3]);
                        Qbf.mk_implies [var sample_conf [4]] (var sample_conf2 [4]);
                      ];
                      Qbf.mk_and [
                        Qbf.mk_implies [var sample_conf2 [1]] (var sample_conf [1]);
                        Qbf.mk_implies [var sample_conf2 [2]] (var sample_conf [2]);
                        Qbf.mk_implies [var sample_conf2 [3]] (var sample_conf [3]);
                        Qbf.mk_implies [var sample_conf2 [4]] (var sample_conf [4]);
                      ]
                  ]
               ) x
  )

let print fmt a b =
  () (*Format.fprintf fmt "%p\n%p" (a) (b)*)

(* Failing, and I don't understand why *)
let test_union = "union" >:: (fun () ->
    let x = sample_conf in
    let y = sample_conf2 in
    assert_equal (Qbf.mk_or [subset x y; subset y x])
      (union subset subset y x)
  )

let test_same_label = "same_label" >:: (fun () ->
    let es = { events_number = 5;
               reads = [3;5];
               justifies = [(2,3); (2,5); (4,3); (4,5)];
               conflicts = [(2,4)];
               order = [(1,2);(2,3);(1,4);(4,5)] }
    in
    assert_bool "same_label" (same_label es 1 1);
    assert_bool "same label" (same_label es 2 4);
    assert_bool "same label" (not @@ same_label es 2 3)
  )
