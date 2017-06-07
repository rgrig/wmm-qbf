type event = int
type set = event list
type relation = (event * event) list

type t =
  { events : int
  ; justifies : relation
  ; conflicts : relation
  ; order : relation
  ; execution : set }

let empty =
  { events = 0
  ; justifies = []
  ; conflicts = []
  ; order = []
  ; execution = [] }

exception Bad

let check r =
  let c b = if not b then raise Bad in
  let cx x = c (0 <= x); c (x < r.events) in
  let cxx (x, y) = cx x; cx y in
  c (r.events >= 0);
  List.iter cxx r.justifies;
  List.iter cxx r.conflicts;
  List.iter cxx r.order;
  List.iter cx r.execution;
  r
