%token EOF
%token <int> INT
%token <int> REGISTER
%token <int> THREAD
%token <string> WORD
%token SEMICOLON
%token DOT
%token COMMA
%token PIPE
%token COLON
%token PLUS
(* TODO: Remove.
%token BRANCH
%token READ
%token WRITE
%token FENCE
%token RMW
%token MOV
%token ADD
%token AND
%token EQUAL
%token NOT_EQUAL
*)
%token ROUNDL
%token ROUNDR
%token SQUAREL
%token SQUARER
%token CURLYL
%token CURLYR

%nonassoc SEMICOLON

(* HACK. *)
%start <string> parse

%%

parse:
| CURLYL CURLYR w=WORD EOF { "Word: " ^ w }


(*
%start <TODO> parse

%%

(* Parser for litmus tests written in LISA (Litmus Instruction Set Architecture). *)
parse:
| TODOsetup thread_list instruction_sequence TODOconditions EOF	{ TODO }

(* List of thread names. *)
thread_list:
| t=THREAD SEMICOLON											{ [t] }
| t=THREAD PIPE ts=thread_list									{ t::ts }

(* List of groups of instructions, one entry for each line down the program. *)
instruction_sequence:
| i=instruction_strata SEMICOLON								{ [i] }
| i=instruction_strata SEMICOLON is=instruction_sequence		{ i::is }

(* List of instructions that happen on the same line, one entry for each column. *)
instruction_strata:
| i=instruction													{ [i] }
| i=instruction PIPE is=instruction_strata						{ i::is }

(* A single instruction, which can be left empty. *)
instruction:
| (* Empty *)													{ NoOp }
| l=WORD COLON i=instruction									{ Label (l, i) }
(* TODO: Make sure symbolic registers aren't needed. *)
| (WORD "r") l=annotations dst=REGISTER src=address				{ Read (l, src, dst) }
| (WORD "w") l=annotations dst=address src=expression			{ Write (l, src, dst) }
| (WORD "f") l=annotations f=fence_labels						{ Fence (l, f) }
| (WORD "rmw") l=annotations REGISTER operation address			{ TODO }
| (WORD "b") l=annotations REGISTER WORD							{ TODO }
| (WORD "b") l=annotations WORD									{ TODO }
| (WORD "mov") REGISTER operation								{ TODO }

(* Extra tags for things like C++ memory order stuff. *)
annotations:
| SQUAREL SQUARER ->											{ [] }
| SQUAREL annotation_list SQUARER ->							{ $2 }

(* List of tag names inside the brackets of annotations. *)
annotation_list:
| WORD ->														{ [$1] }
| WORD COMMA annotation_list ->									{ $1 :: $3 }

(* TODO: expression. *)
(* TODO: fence_labels. *)
(* TODO: operation. *)

(* TODO: Make sure these are handled after being moved from tokens to identifiers.
| "add"					{ ADD }
| "and"					{ AND }
| "eq"					{ EQUAL }
| "ne"					{ NOT_EQUAL }
*)
*)
