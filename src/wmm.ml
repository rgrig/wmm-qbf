type event = int
type set = event list
type relation = (event * event) list

type t =
  { events : int
  ; reads : set (* more properly named "events that need justification" *)
  ; justifies : relation
  ; conflicts : relation
  ; order : relation
  ; execution : set }

let empty =
  { events = 0
  ; reads = []
  ; justifies = []
  ; conflicts = []
  ; order = []
  ; execution = [] }

exception Bad_count of int
exception Bad_event of int
exception Bad_read of int

let check r =
  let cx x =
    if not (1 <= x && x <= r.events) then
      raise (Bad_event x) in
  let cxx (x, y) = cx x; cx y in
  if not (0 <= r.events) then raise (Bad_count r.events);
  List.iter cxx r.justifies;
  List.iter cxx r.conflicts;
  List.iter cxx r.order;
  List.iter cx r.execution;
  List.iter cx r.reads;
  let cj (_, y) =
    if not (List.mem y r.reads) then
      raise (Bad_read y) in
  List.iter cj r.justifies;
  r
