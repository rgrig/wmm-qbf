%token EOF
%token <int> INT
%token <int> REGISTER
%token <int> THREAD
%token <string> VARIABLE
%token SEMICOLON
%token SEMICOLON
%token DOT
%token COMMA
%token PIPE
%token COLON
%token PLUS
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
%token ROUNDL
%token ROUNDR
%token SQUAREL
%token SQUARER
%token CURLYL
%token CURLYR

%nonassoc SEMICOLON

%start <TODO> parse

%%

(* Parser for litmus tests written in LISA (Litmus Instruction Set Architecture). *)
parse:
| TODOsetup thread_list instruction_sequence TODOconditions EOF	{ TODO }

(* List of thread names. *)
thread_list:
| THREAD SEMICOLON												{ [$1] }
| THREAD PIPE thread_list										{ $1 :: $3 }

(* List of groups of instructions, one entry for each line down the program. *)
instruction_sequence:
| instruction_strata SEMICOLON									{ [$1] }
| instruction_strata SEMICOLON instruction_sequence				{ $1 :: $3 }

(* List of instructions that happen on the same line, one entry for each column. *)
instruction_strata:
| instruction													{ [$1] }
| instruction PIPE instruction_strata							{ $1 :: $3 }

(* A single instruction, which can be left empty. *)
instruction:
|																{ NoOp }
(* TODO: Handle case where NAME is consumed by READ or something. *)
(* TODO: Don't allow `label: label: label: instruction`?
| NAME COLON instruction										{ Label ($1, $3) }
(* TODO: Make sure symbolic registers aren't needed. *)
| READ annotations REGISTER address								{ TODO }
| WRITE annotations address expression							{ TODO }
| FENCE annotations fence_labels								{ TODO }
| RMW annotations REGISTER operation address					{ TODO }
| BRANCH annotations REGISTER NAME								{ TODO }
| BRANCH annotations NAME										{ TODO }
| MOV REGISTER operation										{ TODO }

(* Extra tags for things like C++ memory order stuff. *)
annotations:
| SQUAREL SQUARER -> { [] }
| SQUAREL annotation_list SQUARER -> { $2 }

(* List of tag names inside the brackets of annotations. *)
annotation_list:
| NAME -> { [$1] }
| NAME COMMA annotation_list -> { $1 :: $3 }

(* TODO: expression. *)
(* TODO: fence_labels. *)
(* TODO: operation. *)
