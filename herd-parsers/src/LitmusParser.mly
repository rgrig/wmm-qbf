{
  (* Take a list of lines (which contain parallel instructions) and return a list of threads. *)
  (* (Threads are sequences of instructions) *)
  let lines_to_threads (lines : instruction list list) : instruction list list =
    (* TODO. *)
}

%token EOF
%token <int> INT
%token <int> REGISTER
%token <int> PROCESS
%token <string> WORD (* See the word rule. *)
%token BRACNH
%token FENCE
%token MOV
%token READ
%token RMW
%token WRITE
%token ASTERISK
%token ASSIGN
%token AMPERSAND
%token COLON
%token SEMICOLON
%token DOT
%token COMMA
%token PIPE
%token ROUNDL
%token ROUNDR
%token SQUAREL
%token SQUARER
%token CURLYL
%token CURLYR
%token NOT
%token AND
%token OR
%token EQUAL
%token NOT_EQUAL
%token IMPLIES

%left OR
%left AND
%right IMPLIES
%nonassoc NOT
%nonassoc SEMICOLON

%start <litmus> parse

%%

(* Parser entrypoint, expects header to have been handled first. *)
parse:
| CURLYL setup=setup CURLYR titles=titles lines=program condition=condition
  { litmus { setup; titles; processes=lines_to_threads lines; condition } }

(* Initial state of virtual machine. *)
setup:
| list=separated_list(SEMICOLON, setup_item) SEMICOLON? { list }

setup_item:
| l=setup_location                                       { l, Literal 0 }
| l=setup_location ASSIGN value=INT                      { l, Literal value }
| l=setup_location ASSIGN name=word                      { l, Variable { name=name } }
| ASTERISK l=setup_location                              { l, Address 0 }
| ASTERISK l=setup_location ASSIGN ASTERISK? address=INT { l, Address address }
| ASTERISK l=setup_location ASSIGN ASTERISK? name=word   { l, VariableAddress { name=name } }

setup_location:
| p=PROCESS COLON r=register { Register { process=p; register=r; } }
| p=INT COLON r=register     { Register { process=p; register=r; } }
| name=word                  { Variable { name=name; } }

(* Program threads. *)
titles:
| list=separated_list(PIPE, PROCESS) SEMICOLON { list }

program:
| list=separated_list(SEMICOLON, line) SEMICOLON { list }

line:
| list=separated_list(PIPE, instruction) { list }

instruction:
| label=label
  { { instruction=Nop; label, tags=[] } }
| label=label BRANCH tags=tags jump_to=word
  { { instruction=Branch { condition=None; jump_to; }; label; tags; } }
| label=label BRANCH tags=tags r=register jump_to=word
  { { instruction=Branch { condition=Some r; jump_to; }; label; tags; } }
| label=label FENCE tags=tags
  { { instruction=Fence { range=None; }; label; tags; } }
| label=label FENCE tags=tags CURLYL from=labels CURLYR CURLYL to=labels CURLYR
  { { instruction=Fence { range=Some (from, to); }; label; tags; } }
| label=label MOV tags=tags destination=register value=operation
  { { instruction=Mov { destination; value; }; label; tags; } }
| label=label READ tags=tags destination=register source=address
  { { instruction=Read { destination; source; }; label; tags; } }
| label=label RMW tags=tags destination=register value=operation address=address
  { { instruction=RMW { destination; value; address; }; label; tags; } }
| label=label WRITE tags=tags destination=address source=register
  { { instruction=WriteRegister { destination; source; }; label; tags; } }
| label=label WRITE rags=tags destination=address value=INT
  { { instruction=WriteImmediate { destination; value; }; label; tags; } }

address:

tags:
| (* Empty. *)                                     { [] }
| SQUAREL list=separated_list(COMMA, word) SQUARER { list }

operation:

operation_value:
| value=INT
| register=register
| name=word
| register=register PLUS 

labels:
| list=separated_list(COMMA, word) { list }

label:
| (* Empty. *)    { None }
| name=word COLON { Some name }

(* Required final state. *)
condition:

(* Convenience for packaging register information into something useful. *)
(* Sets the process to zero on the assumption it will be set later. *)
register process:
| register=REGISTER { { process=0; register; } }

(* Rule for identifiers because excluding single letter keywords would be horrible. *)
word:
| BRANCH    { "b" }
| FENCE     { "f" }
| READ      { "r" }
| WRITE     { "w" }
| word=WORD { word }
