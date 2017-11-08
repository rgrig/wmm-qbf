type element = int
type fo_var = string
type so_var = string
type rel_sym = string (* same as so_var *)
type relation = int list list

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
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
