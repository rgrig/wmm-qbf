%{
  type item =
    | Conflicts of Wmm.relation
    | Events of int
    | Execution of Wmm.set
    | Justifies of Wmm.relation
    | Order of Wmm.event list list

  let join _ = failwith "todo"
%}

%token <int> INT
%token CONFLICTS
%token EOF
%token EVENTS
%token EXECUTION
%token JUSTIFIES
%token NL
%token ORDER

%start <Wmm.t> question

%%

question:
  xs=item* EOF { join xs }
;

item:
    v=events { Events v }
  | v=justifies { Justifies v }
  | v=conflicts { Conflicts v }
  | v=order { Order v }
  | v=execution { Execution v}
;

events: v=delimited(EVENTS, INT, NL*) { v };
justifies: v=nl_list(JUSTIFIES,pair(INT,INT),NL*) { v };
conflicts: v=nl_list(CONFLICTS,pair(INT,INT),NL*) { v };
order: v=nl_list(ORDER,nonempty_list(INT),NL+) { v };
execution: v=nl_list(EXECUTION,INT,NL*) { v };

nl_list(a,element,b): v=preceded(a,list(terminated(element,b))) { v };

%%
