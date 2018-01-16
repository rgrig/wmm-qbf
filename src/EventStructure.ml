(* Event numbers start at one, not zero. *)
type event = int
type set = event list
type relation = (event * event) list

type t =
  { events_number : int
  ; reads : set (* more properly named "events that need justification" *)
  ; justifies : relation
  ; conflicts : relation
  ; order : relation
  ; sloc : relation
  ; na : set
  ; sc : set
  ; rel : set
  ; acq : set
  ; consume : set
  ; fences : set
  ; ext : relation }

let empty =
  { events_number = 0
  ; reads = []
  ; justifies = []
  ; conflicts = []
  ; order = []
  ; sloc = []
  ; na = []
  ; sc = []
  ; rel = []
  ; acq = []
  ; consume = []
  ; fences = []
  ; ext = [] }

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

let self_justified es xs =
  let all = Hashtbl.create 10 in
  let reads = Hashtbl.create 10 in
  let justified = Hashtbl.create 10 in
  List.iter (fun x -> Hashtbl.replace all x ()) xs;
  List.iter (fun x -> if Hashtbl.mem all x then Hashtbl.add reads x ()) es.reads;
  let arc (x, y) =
    if Hashtbl.mem all x then Hashtbl.replace justified y () in
  List.iter arc es.justifies;
  Hashtbl.fold (fun x () a -> a && Hashtbl.mem justified x) reads true

let get_events es = BatList.range 1 `To (es.events_number)
let get_sloc es = es.sloc
let get_order es = es.order
let get_reads es = es.reads
let get_writes es = List.filter (fun x -> not (List.mem x es.reads)) (get_events es)
let get_justifies es = es.justifies
let get_conflicts es = es.conflicts
let get_events_number es = es.events_number

let order_tc es = GraphHelpers.transitive_closure (get_order es)
