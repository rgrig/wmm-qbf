%{
  module ES = EventStructure

  type item =
    | Conflicts of ES.relation
    | Events of int
    | Justifies of ES.relation
    | Order of ES.event list list
    | Reads of ES.set

  let flatten_order xss =
    let rec g ps x = function
      | [] -> ps
      | y :: ys -> g ((x,y) :: ps) y ys in
    let f = function
      | [] -> []
      | x :: xs -> g [] x xs in
    List.concat @@ List.map f xss

  let join xs =
    let f r = function
      | Conflicts xs -> { r with ES.conflicts = xs @ r.ES.conflicts }
      | Events n -> { r with ES.events_number = max n r.ES.events_number }
      | Justifies xs -> { r with ES.justifies = xs @ r.ES.justifies }
      | Order xss -> { r with ES.order = flatten_order xss @ r.ES.order }
      | Reads xs -> { r with ES.reads = xs @ r.ES.reads }
    in
    ES.check @@ List.fold_left f ES.empty xs
%}

%token <int> INT
%token BADKEYWORD
%token CONFLICTS
%token EOF
%token EVENTS
%token JUSTIFIES
%token NL
%token ORDER
%token READS

%start <EventStructure.t> event_structure

%%

event_structure:
  xs=item* EOF { join xs }
;

item:
    v=events { Events v }
  | v=justifies { Justifies v }
  | v=conflicts { Conflicts v }
  | v=order { Order v }
  | v=reads { Reads v }
;

events: v=delimited(EVENTS, INT, NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { v };
reads: v=nl_list(READS,INT,NL*) { v };

nl_list(a,element,b): v=preceded(pair(a,NL*),list(terminated(element,b))) { v };

%%
