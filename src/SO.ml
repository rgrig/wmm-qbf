module U = Util

type element = int
  [@@deriving show]
type fo_var = string * int
  [@@deriving show]
type so_var = string * int
  [@@deriving show]
type rel_sym = string * int
  [@@deriving show] (* same as so_var *)
type relation = int list list
  [@@deriving show]

module RelMap = Map.Make (String)

type structure =
  { size : int
  ; relations : relation RelMap.t }

type term =
  | Var of fo_var
  | Const of element

type formula =
  | CRel of rel_sym * term list
  | QRel of so_var * term list
  | FoAny of fo_var * formula
  | FoAll of fo_var * formula
  | SoAny of so_var * formula
  | SoAll of so_var * formula
  | And of formula list
  | Or of formula list
  | Not of formula

let show_term = function
    Var (n, a) -> n
  | Const e -> string_of_int e

let rec show_formula = function
  | CRel (rel,ts) | QRel (rel, ts) ->
     Format.sprintf "%s(%s)" (fst rel) (U.map_concat ", " show_term ts)
  | FoAny (var, f) | SoAny (var, f) ->
     Format.sprintf "∃%s . %s" (fst var) (show_formula f)
  | FoAll (var, f) | SoAll (var, f) ->
     Format.sprintf "∀%s . %s" (fst var) (show_formula f)
  | And fs ->
     Format.sprintf "(%s)" (U.map_concat " ∧ " show_formula fs)
  | Or fs ->
     Format.sprintf "(%s)" (U.map_concat " ∧ " show_formula fs)
  | Not f ->
     "¬ " ^ (show_formula f)

let pp_formula fmt f =
  Format.fprintf fmt "%s" (show_formula f)
  
let mk_fresh_name =
  let id = ref 0 in
  function () -> incr id
         
(* p₁ ∧ p₂ ∧ pₙ → q  ⇔  ¬p₁ ∨ ¬p₂ ∨ ¬pₙ ∨ q *)         
let mk_implies prems conclusion =
  Or (conclusion :: List.map (fun p -> Not p) prems)
