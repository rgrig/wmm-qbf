type event = int
type set = event list
type relation = (event * event) list

type t =
  { events_number : int
  ; reads : set (* more properly named "events that need justification" *)
  ; justifies : relation
  ; conflicts : relation
  ; order : relation }

let empty =
  { events_number = 0
  ; reads = []
  ; justifies = []
  ; conflicts = []
  ; order = [] }

exception Bad_count of int
exception Bad_event of int
exception Bad_read of int

(* TODO:
  - check that justifies and order are compatible
  - check that order has no cycles
  - check the well-formdness conditions for conflicts (see paper)
  - check that sets represented by lists have no duplicates (?)
*)
let check r =
  let cx x =
    if not (1 <= x && x <= r.events_number) then
      raise (Bad_event x) in
  let cxx (x, y) = cx x; cx y in
  if not (0 <= r.events_number) then raise (Bad_count r.events_number);
  List.iter cxx r.justifies;
  List.iter cxx r.conflicts;
  List.iter cxx r.order;
  List.iter cx r.reads;
  let cj (_, y) =
    if not (List.mem y r.reads) then
      raise (Bad_read y) in
  List.iter cj r.justifies;
  r
