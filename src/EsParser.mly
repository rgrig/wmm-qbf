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
%token JUSTIFIES
%token SLOC
%token LABELS
%token NL
%token ORDER
%token READS
%token QUOTED_STRING
%token CAN
%token MUST

%start <EventStructure.t * EventStructure.set * EventStructure.set> top

%%

top:
  es=event_structure mustExecute=mustExec canExecute=canExec EOF
  { es, canExecute, mustExecute }
;

event_structure:
  e=events
  s=option(sloc)
  r=reads
  _=option(labels)
  j=justifies
  c=conflicts
  o=order
  { ES.check
    { ES.events_number=e
    ; justifies=j
    ; conflicts=c
    ; order=o
    ; reads=r
    ; sloc=(
      match s with
        None -> []
      | Some s -> s
      )
    }
  }
;

events: v=delimited(EVENTS, INT, NL*) { v };
sloc: v=nl_list(SLOC,nonempty_list(INT),NL+) { flatten_order v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
labels: nl_list(LABELS,pair(INT, QUOTED_STRING),NL*) {};
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { flatten_order v };
reads: v=nl_list(READS,INT,NL*) { v };
mustExec: v=nl_list(MUST,INT,NL*) { v };
canExec: v=nl_list(CAN,INT,NL*) { v };

nl_list(a,element,b): v=preceded(pair(a,NL*),list(terminated(element,b))) { v };

%%
