(** Syntax tree of model definitions *)

type set_or_rln = SET | RLN
  [@@deriving show]

type op2 =
  | Union (** applies to sets or relations *)
  | Inter (** applies to sets or relations *)
  | Diff  (** applies to sets or relations *)
  | Seq   (** sequential composition of relations *)
  | Cartesian (** build a relation from two sets *)
  | Add   (** add element to a set *)
  | Tuple (** Build a tuple *)
  [@@deriving show]

type op1 =
  | Plus | Star | Opt
  | Comp (** Set or relation complement *)
  | Inv  (** Relation inverse *)
  | ToId (** Lift set to id relation (ie toido(S) = (S * S) & id *)
  [@@deriving show]

type konst = Empty of set_or_rln | Universe of set_or_rln
  [@@deriving show]
type var = string [@@deriving show]
type tag = string [@@deriving show]
type varset = Util.StringSet.t

type vs = string list [@@deriving show] (* hack *)
let pp_varset f x = pp_vs f (Util.StringSet.elements x)

type scope = Device | Kernel | Work_Group | Sub_Group | Work_Item
  [@@deriving show]

type exp =
  | Konst of konst
  | Tag of tag
  | Var of var
  | Op1 of op1 * exp
  | Op of op2 * exp list
  | App of exp * exp
  | Bind of binding list * exp
  | BindRec of binding list * exp
  | Fun of pat * exp * var (* name *) * varset (* free vars *)
  | ExplicitSet of exp list
  | Match of exp * clause list * exp option
  | MatchSet of exp * exp * set_clause
  | Try of exp * exp
  | If of cond * exp * exp
  [@@deriving show]

and set_clause =
  | EltRem of string * string * exp
  | PreEltPost of string * string * string * exp
  [@@deriving show]


and pat =
  | Pvar of var
  | Ptuple of var list
  [@@deriving show]

and cond =
  | Eq of exp * exp
  | Subset of exp * exp
  [@@deriving show]

and clause =
  string * exp
  [@@deriving show]

and binding =
  pat * exp
  [@@deriving show]

type do_test = Acyclic | Irreflexive | TestEmpty
  [@@deriving show]
type test = Yes of do_test | No of do_test
  [@@deriving show]
type test_type = Flagged | UndefinedUnless | Check
  [@@deriving show]
type app_test = test * exp * string option
  [@@deriving show]
type is_rec = IsRec | IsNotRec
  [@@deriving show]

type ins =
  | Let of binding list
  | Rec of binding list * app_test option
  | InsMatch of exp * insclause list * ins list option
  | Test of app_test * test_type
  | UnShow of string list
  | Show of string list
  | ShowAs of exp * string
  | Latex of string
  | Include of string (* file name, interpreter will read/parse file... *)
  | Procedure of var * pat * ins list * is_rec
  | Call of var * exp * string option (* optional name, for skip *)
  | Enum of var * tag list
  | Forall of var * exp * ins list
  | Debug of exp
  | WithFrom of var * exp (* set of relations *)
(*For bell files*)
  | Events of var * exp list * bool (* define default *)
  [@@deriving show]


and insclause =
  string * ins list
  [@@deriving show]


(** Name X model definition *)
type t =
  ModelOption.t * string * ins list
  [@@deriving show]
