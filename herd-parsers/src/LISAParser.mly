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
| CURLYL CURLYR w=WORD EOF when w = "a" { "Word: " ^ w }


(*
%start <TODO> parse

%%

(* Parser for litmus tests written in LISA (Litmus Instruction Set Architecture). *)
parse:
| CURLYL setup CURLYR thread_list instruction_sequence TODOconditions EOF	{ TODO }

(* List of initial states. *)
setup:
| TODO
| TODO COMMA setup

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
| w=WORD														{ match w with
																  | "b" -> instruction_branch
																  | "f" -> instruction_fence
																  | "mov" -> instruction_mov
																  | "r" -> instruction_read
																  | "rmw" -> instruction_rmw
																  | "w" -> instruction_write
																  | _ -> raise Error (Printf.sprintf
																    "invalid instruction: %s", w)

(* Parameters for branch. *)
instruction_branch:
| a=annotations condition=REGISTER to=WORD						{ Branch (a, condition, to) }
| a=annotations to=WORD											{ Jump (a, to) }

(* Parameters for fence. *)
instruction_fence:
| a=annotations labels=fence_labels								{ Fence (a, labels) }

(* Parameters for mov. *)
instruction_mov:
| a=annotations to=REGISTER value=operation						{ Mov (a, to, value) }

(* Parameters for read. *)
instruction_read:
(* TODO: Herd seems to accept several odd things as source, support them? *)
(* TODO: Check we don't need "symbolic registers" (what are they anyway?) *)
| a=annotations to=REGISTER from=WORD							{ Read (a, to, from) }

(* Parameters for read-modify-write. *)
instruction_rmw:
(* TODO: Herd's implementation is more limited that the specification. *)
(* TODO: Herd seems to accept several odd things as destination, support them? *)
| a=annotations using=REGISTER value=operation to=WORD			{ RMW (a, to, using, value) }

(* Parameters for write. *)
instruction_write:
(* TODO: Herd seems to accept several odd things as destination, support them? *)
| a=annotations to=WORD from=REGISTER							{ WriteFromRegister(a, to, from) }
(* TODO: Values can also be "meta", work out what that means. *)
| a=annotations to=WORD value=INT								{ WriteFromImmediate(a, to, value) }

(* Extra tags for things like C++ memory order stuff. *)
annotations:
| SQUAREL word_list SQUARER ->									{ $2 }

(* TODO: Accepts trailing commas that Herd doesn't, does this matter? *)
word_list:
| (* Empty. *)													{ [] }
| WORD ->														{ [$1] }
| WORD COMMA word_list ->		  								{ $1 :: $3 }

(* Sets of labels that a fence applies between (optional). *)
fence_labels:
| (* Empty. *)													{ None }
| CURLYL start=word_list CURLYR CURLYL end=word_list CURLYR		{ Some (start, end) }

(* Calculated expression. *)
operation:
| value=value													{ Value (value) }
| ROUNDL op=WORD a=value b=value ROUNDR							{ match word with
																  | "add" -> Add(a, b)
																  | "xor" -> Xor(a, b)
																  | "and" -> And(a, b)
																  | "eq" -> Equal(a, b)
																  | "ne" | "neq" -> NotEqual(a, b)
																  | _ -> raise Error (Printf.printf
																    "Expected operation, found \"%s\"" word)

(* Any data. *)
(* TODO: Herd seems to accept whatever "Constant.Symbolic" is here, support that too? *)
value:
| name=REGISTER													{ Register (name) }
| value=INT														{ Immediate (value) }
*)
