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

  let some_or_empty = function
    Some l -> l
  | None -> []
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
%token FINAL
%token EXECUTION
%token SEQUENTIALLY_CONSISTENT
%token RELAXED
%token RELEASE
%token ACQUIRE
%token CONSUME
%token NON_ATOMIC
%token FENCE
%token EXT
%token RMW

%start <EventStructure.t * EventStructure.set list> top

%%

top:
  es=event_structure
  final=option(final)
  target=option(target)
  EOF
  {
  match target with
    None -> es, Util.from_some final
  | Some t -> es, (List.map (fun f -> [f]) t)
  }
;

event_structure:
  e=events
  s=option(sloc)
  r=reads
  nas=option(na)
  scs=option(sc)
  rels=option(rel)
  acqs=option(acq)
  rlxs=option(rlx)
  consumes=option(consume)
  fences=option(fence)
  exts=option(ext)
  rmws=option(rmw)
  _labels=option(labels)
  j=justifies
  c=conflicts
  o=order
  { ES.check
    { ES.events_number=e
    ; justifies=j
    ; conflicts=c
    ; order=o
    ; reads=r
    ; writes=[] (* TODO: writes = events \ reads *)
    ; sloc=(some_or_empty s)
    ; na=(some_or_empty nas)
    ; sc=(some_or_empty scs)
    ; rel=(some_or_empty rels)
    ; acq=(some_or_empty acqs)
    ; rlx=(some_or_empty rlxs)
    ; consume=(some_or_empty consumes)
    ; fences=(some_or_empty fences)
    ; ext=(some_or_empty exts)
    ; rmw=(some_or_empty rmws)
    }
  }
;

events: v=delimited(EVENTS, INT, NL*) { v };
sloc: v=nl_list(SLOC,nonempty_list(INT),NL+) { flatten_order v };
final: v=nl_list(FINAL,nonempty_list(INT),NL+) { v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
labels: nl_list(LABELS,pair(INT, QUOTED_STRING),NL*) {};
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { flatten_order v };
reads: v=nl_list(READS,INT,NL*) { v };
target: v=nl_list(EXECUTION,INT,NL*) { v };
na: v=nl_list(NON_ATOMIC,INT,NL*) { v };
sc: v=nl_list(SEQUENTIALLY_CONSISTENT,INT,NL*) { v };
rel: v=nl_list(RELEASE,INT,NL*) { v };
acq: v=nl_list(ACQUIRE,INT,NL*) { v };
rlx: v=nl_list(RELAXED,INT,NL*) { v };	
consume: v=nl_list(CONSUME,INT,NL*) { v };
fence: v=nl_list(FENCE,INT,NL*) { v };
ext: v=nl_list(EXT,nonempty_list(INT),NL+) { flatten_order v };
rmw: v=nl_list(RMW,nonempty_list(INT),NL+) { flatten_order v };



nl_list(a,element,b): v=preceded(pair(a,NL*),list(terminated(element,b))) { v };

%%
