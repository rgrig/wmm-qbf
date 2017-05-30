%{
  type item =
    | Conflicts of Wmm.relation
    | Events of int
    | Execution of Wmm.set
    | Justifies of Wmm.relation
    | Order of Wmm.event list list

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
      | Conflicts xs -> { r with Wmm.conflicts = xs @ r.Wmm.conflicts }
      | Events n -> { r with Wmm.events = max n r.Wmm.events }
      | Execution xs -> { r with Wmm.executions = xs :: r.Wmm.executions }
      | Justifies xs -> { r with Wmm.justifies = xs @ r.Wmm.justifies }
      | Order xss -> { r with Wmm.order = flatten_order xss @ r.Wmm.order } in
    Wmm.check @@ List.fold_left f Wmm.empty xs
%}

%token <int> INT
%token CONFLICTS
%token EOF
%token EVENTS
%token EXECUTIONS
%token JUSTIFIES
%token NL
%token ORDER

%start <Wmm.t> wmm

%%

wmm:
  xs=item* EOF { join xs }
;

item:
    v=events { Events v }
  | v=justifies { Justifies v }
  | v=conflicts { Conflicts v }
  | v=order { Order v }
  | v=execution { Execution v }
;

events: v=delimited(EVENTS, INT, NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { v };
execution: v=nl_list(EXECUTIONS,INT,NL*) { v };

nl_list(a,element,b): v=preceded(a,list(terminated(element,b))) { v };

%%
