%{

open ModelAst

let do_op _ =
  failwith "todo"

let pp _ =
  failwith "letoj"

%}

%token EOF
%token <string> VAR
%token <string> TAG
%token <string> STRING
%token <string> LATEX
%token INCLUDE
%token LPAR RPAR BEGIN END LACC RACC LBRAC RBRAC
%token EMPTY UNDERSCORE SUBSET
%token WITHCO WITHOUTCO WITHINIT WITHOUTINIT
%token WITHSC WITHOUTSC
%token ALT SEMI UNION INTER COMMA DIFF PLUSPLUS
%token STAR PLUS OPT INV COMP HAT
%token LET REC AND WHEN ACYCLIC IRREFLEXIVE TESTEMPTY EQUAL
%token SHOW UNSHOW AS FUN IN PROCEDURE CALL FORALL DO FROM
%token TRY INSTRUCTIONS DEFAULT IF THEN ELSE YIELD COMPAT
%token REQUIRES FLAG
%token ARROW
%token ENUM DEBUG MATCH WITH
%type <unit> main
%start main

/* Precedences */
%right COMMA
%left prec_app
%right UNION
%right PLUSPLUS
%right SEMI
%left DIFF
%right INTER
%nonassoc STAR PLUS OPT INV COMP
%nonassoc HAT
%%

main:
| identity options topins_list EOF { () }

identity:
| VAR { $1 }
| STRING { $1 }
|  { "Unknown" }

options:
| WITHCO options { ModelOption.set_enumco true $2 }
| WITHOUTCO options { ModelOption.set_enumco false $2 }
| WITHINIT options { ModelOption.set_init true $2 }
| WITHOUTINIT options { ModelOption.set_init false $2 }
| WITHSC options { ModelOption.set_enumsc true $2 }
| WITHOUTSC options { ModelOption.set_enumsc false $2 }
|    { ModelOption.default }

topins_list:
| { [] }
| topins topins_list { $1 :: $2 }

ins_list:
| { [] }
| ins ins_list { $1 :: $2 }

in_opt:
|    { () }
| IN { () }

ins_clause:
| TAG ARROW ins_list { $1,$3 }

ins_clause_list:
| ins_clause { [$1],None }
| UNDERSCORE ARROW ins_list { [],Some $3 }
| ins_clause ALT ins_clause_list
    {
     let cls,d = $3 in
     $1 :: cls, d
    }


topins:
| ENUM VAR EQUAL altopt alttags { Enum ($2,$5) }
| ins { $1 }


ins:
| LET pat_bind_list in_opt { Let ($2) }
| LET REC pat_bind_list  in_opt { Rec ($3,None) }
| LET REC pat_bind_list WHEN app_test in_opt { Rec ($3,Some $5) }
| MATCH exp WITH altopt ins_clause_list END
    {
     let cls,d = $5 in
     InsMatch ($2,cls,d)
    }
| deftest { $1 }
| SHOW exp AS VAR { ShowAs ($2, $4) }
| SHOW var_list { Show ($2) }
| UNSHOW var_list { UnShow ($2) }
| LATEX { Latex ($1) }
| INCLUDE STRING { Include ($2) }
| PROCEDURE VAR LPAR formals RPAR EQUAL ins_list END
   { Procedure ($2,Ptuple $4,$7,IsNotRec) }
| PROCEDURE VAR VAR EQUAL ins_list END
   { Procedure ($2,Pvar $3,$5,IsNotRec) }

| PROCEDURE REC VAR LPAR formals RPAR EQUAL ins_list END
   { Procedure ($3,Ptuple $5,$8,IsRec) }
| PROCEDURE REC VAR VAR EQUAL ins_list END
   { Procedure ($3,Pvar $4,$6,IsRec) }

| CALL VAR simple optional_name { Call ($2,$3,$4) }
| DEBUG exp { Debug ($2) }
| FORALL VAR IN exp DO ins_list END
    { Forall ($2,$4,$6) }
| WITH VAR FROM exp
    { WithFrom ($2,$4) }


//Bell file declarations
| INSTRUCTIONS VAR LBRAC exp_list RBRAC  {Events($2,$4,false)}
| DEFAULT VAR LBRAC exp_list RBRAC  {Events($2,$4,true)}


altopt:
| ALT  { () }
|      { () }

alttags:
| TAG { [$1] }
| TAG ALT alttags { $1 :: $3 }

deftest:
| test_type app_test { Test ($2,$1) }


app_test:
| test exp optional_name { (pp (),$1,$2,$3) }

test_type:
|          { Check }
| REQUIRES { UndefinedUnless }
| FLAG     { Flagged }

optional_name:
|        { None }
| AS VAR { Some $2 }

do_test:
| ACYCLIC { Acyclic }
| IRREFLEXIVE { Irreflexive }
| TESTEMPTY { TestEmpty }

test:
| do_test { Yes $1 }
| COMP do_test { No $2}

var_list:
| VAR { [$1] }
| VAR comma_opt var_list { $1 :: $3 }

comma_opt:
/* |       { () } */
| COMMA { () }

bind:
| VAR EQUAL exp { (Pvar $1,$3) }
| LPAR formals RPAR EQUAL exp { (Ptuple $2,$5) }
pat_bind:
| bind { $1 }
| VAR VAR EQUAL exp
   { (Pvar $1,Fun (Pvar $2,$4,$1,ModelAstUtils.free_body [$2] $4)) }
| VAR LPAR formals RPAR EQUAL exp
   { (Pvar $1,Fun (Ptuple $3,$6,$1,ModelAstUtils.free_body $3 $6)) }

pat_bind_list:
| pat_bind { [$1] }
| pat_bind AND pat_bind_list { $1 :: $3 }


formals:
|          { [] }
| formalsN { $1 }

formalsN:
| VAR                { [$1] }
| VAR COMMA formalsN { $1 :: $3 }

exp_list:
| { [] }
| exp_listN { $1 }

exp_listN:
| exp {[$1]}
| exp COMMA exp_listN { $1 :: $3}

exp:
| LET pat_bind_list IN exp { Bind ($2,$4) }
| LET REC pat_bind_list IN exp { BindRec ($3,$5) }
| FUN VAR ARROW exp
    { Fun (Pvar $2,$4,"*fun*",ModelAstUtils.free_body [$2] $4) }
| FUN LPAR formals RPAR ARROW exp
    { Fun (Ptuple $3,$6,"*fun*",ModelAstUtils.free_body $3 $6) }
| TRY exp WITH exp
    { Try ($2,$4) }
| IF cond THEN exp ELSE exp
    { If ($2,$4,$6) }
| MATCH exp WITH altopt clause_list END
    {
     let cls,d = $5 in
     Match ($2,cls,d)
    }
| MATCH exp WITH altopt set_clauses END
    {
     let e,f = $5 in
     MatchSet ($2,e,f)
   }
| base { $1 }

cond:
| exp EQUAL exp  { Eq ($1,$3) }
| exp SUBSET exp { Subset ($1,$3) }

simple:
| EMPTY { Konst (Empty RLN) }
| TAG  { Tag ($1) }
| LACC args RACC { ExplicitSet ($2) }
| UNDERSCORE  { Konst (Universe SET) }
| LPAR RPAR { Op (Tuple,[]) }
| LPAR tupleargs RPAR { Op (Tuple,$2) }
| LPAR exp RPAR { $2 }
| BEGIN exp END { $2 }
| LBRAC exp RBRAC { Op1 (ToId,$2) }
 
tupleargs:
| exp COMMA tupleend { $1 :: $3 }

tupleend:
| exp { [$1] }
| exp COMMA tupleend { $1 :: $3 }

base:
| simple { $1 }
| exp0 { $1 }
| base STAR base {Op (Cartesian, [$1; $3])}
| base STAR { Op1(Star,$1) }
| base PLUS { Op1(Plus,$1) }
| base OPT { Op1(Opt,$1) }
| base HAT INV { Op1(Inv,$1) }
| base SEMI base { do_op Seq $1 $3 }
| base UNION base { do_op Union $1 $3 }
| base PLUSPLUS base { Op ( Add, [$1; $3]) }
| base DIFF base { Op (Diff, [$1; $3;]) }
| base INTER base {  Op (Inter, [$1; $3;]) }
| COMP base { Op1 (Comp, $2) }

empty_clause:
| LACC RACC ARROW exp { $4 }

element_clause2:
| VAR PLUSPLUS VAR ARROW exp { EltRem ($1, $3, $5) }

element_clause3:
| VAR UNION VAR PLUSPLUS VAR ARROW exp { PreEltPost ($1,$3,$5,$7) }

element_clause:
| element_clause2 { $1 }
| element_clause3 { $1 }

set_clauses:
| empty_clause ALT element_clause { $1, $3 }
| element_clause ALT empty_clause { $3, $1 }

clause:
| TAG ARROW exp { $1,$3 }

clause_list:
| clause { [$1],None }
| UNDERSCORE ARROW exp { [],Some $3 }
| clause ALT clause_list
    {
     let cls,d = $3 in
     $1 :: cls, d
    }


exp0:
| VAR                 { Var ($1) }
| exp0  arg %prec prec_app   { App ($1,$2) }

arg:
| VAR { Var ($1) }
| simple { $1 }


args:
| { [] }
| argsN { $1 }

argsN:
| exp            { [ $1 ] }
| exp COMMA argsN { $1 :: $3 }


