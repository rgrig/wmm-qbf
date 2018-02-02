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
  ; rlx : set
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
  ; rlx = []
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

let check_confusion_free es =
  let ord_flip = List.map (fun (x,y) -> (y,x)) es.order in
  List.iter (fun (a,b) ->
      (* For all pairs in conflict, there should be a mutual predecessor *)
      let pred r = List.filter (fun (p,q) -> p = r) ord_flip in
      let pred_a = List.map snd (pred a) in
      let pred_b = List.map snd (pred b) in
      let mutual = List.filter (fun r -> List.mem r pred_a) pred_b in
      assert (mutual <> [])
    ) es.conflicts

let saturate_conflict es =
  let pc = es.conflicts in
  let later x = List.filter (fun (y,z) -> z = x) es.order in
  (* For all conflict pairs, their "later" conflict pairs are also in conflict *)
  let conflict = List.flatten
      (List.map (fun (x, y) ->
           [(x,y)]
           @ List.map (fun (_,a) -> (x, a)) (later y)
           @ (List.map (fun (_,a) -> (y, a)) (later x))
         ) pc
      )
  in
  let conflict = Util.transitive_closure conflict in
  let conflict = Util.symmetric_closure conflict in
  (* Remove refl edges *)
  let conflict = List.filter (fun (x, y) -> x <> y) conflict in
  { es with conflicts = conflict }

let transitive_order es =
  { es with order = (Util.rtransitive_closure es.order) }

let apply_axioms es =
  let es' = transitive_order es in
  let es'' = saturate_conflict es' in
  check_confusion_free es'';
  es''

let dump filename es accept labels =
  let open Printf in
  let basename = Filename.remove_extension filename in
  let f_c = open_out (basename ^ ".es") in
  let list l = String.concat " " (List.map string_of_int l) in
  let pairs = List.iter (fun (a, b) -> fprintf f_c "  %d %d\n" a b) in
  let groups = List.iter (fun g -> fprintf f_c "  %s\n" (list g)) in  
  let names = List.iter (fun (event, name) -> fprintf f_c "  %d \"%s\"\n" event name) in
  fprintf f_c "events %d\n" es.events_number;
  fprintf f_c "sloc\n";
  pairs es.sloc;
  fprintf f_c "reads %s\n" (list es.reads);
  fprintf f_c "justifies\n";
  pairs es.justifies;
  fprintf f_c "conflicts\n";
  pairs es.conflicts;
  fprintf f_c "order\n";
  pairs es.order;
  fprintf f_c "final\n";
  groups accept;
  fprintf f_c "labels\n";
  names labels;
  close_out f_c

let get_events es = BatList.range 1 `To (es.events_number)
let get_sloc es = es.sloc
let get_order es = es.order
let get_reads es = es.reads
let get_writes es = List.filter (fun x -> not (List.mem x es.reads)) (get_events es)
let get_justifies es = es.justifies
let get_conflicts es = es.conflicts
let get_events_number es = es.events_number

let order_tc es = GraphHelpers.transitive_closure (get_order es)
