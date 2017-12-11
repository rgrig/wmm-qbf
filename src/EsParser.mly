%{
  module ES = EventStructure

  let flatten_order xss =
    let rec g ps x = function
      | [] -> ps
      | y :: ys -> g ((x,y) :: ps) y ys in
    let f = function
      | [] -> []
      | x :: xs -> g [] x xs in
    List.concat @@ List.map f xss
%}

%token <int> INT
%token CONFLICTS
%token EOF
%token EVENTS
%token EXECUTION
%token JUSTIFIES
%token LABELS
%token NL
%token ORDER
%token READS
%token QUOTED_STRING

%start <EventStructure.t * EventStructure.set option> top

%%

top:
  es=event_structure t=target? EOF { (es, t) }
;

event_structure:
  e=events
  r=reads
  _=option(labels)
  j=justifies
  c=conflicts
  o=order
  { ES.check
    { ES.events_number=e; justifies=j; conflicts=c; order=o; reads=r } }
;

events: v=delimited(EVENTS, INT, NL*) { v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
labels: nl_list(LABELS,pair(INT, QUOTED_STRING),NL*) {};
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { flatten_order v };
reads: v=nl_list(READS,INT,NL*) { v };
target: v=nl_list(EXECUTION,INT,NL*) { v };

nl_list(a,element,b): v=preceded(pair(a,NL*),list(terminated(element,b))) { v };

%%
