open Printf

type variable = string

type formula =
  | Var of variable
  | Not of formula
  | And of formula list
  | Or of formula list

type quantifier = Exists | Forall

type t = (quantifier * variable list) list * formula

let mk_var v = Var v
let mk_implies f g = Or [Not f; g]
let mk_and xs = And xs
let mk_or xs = Or xs
let mk_not x = Not x

let mk_qbf f = ([], f)
let mk_exists xs (qs, f) = ((Exists, xs) :: qs, f)
let mk_forall xs (qs, f) = ((Forall, xs) :: qs, f)

let normalize_quantifiers qs =
  let rec f xss q ys = function
    | [] -> (q, ys) :: xss
    | (qq, zs) :: zss ->
        if q = qq
        then f xss q (zs @ ys) zss
        else f ((q, ys) :: xss) qq zs zss in
  (match qs with
  | [] -> []
  | (q, xs) :: qs -> List.rev (f [] q xs qs))

let rec pp_list_sep sep pp_x f = function
  | [] -> ()
  | [x] -> pp_x f x
  | x :: ((_ :: _) as xs) ->
      fprintf f (format_of_string "%a%s%a") pp_x x sep (pp_list_sep sep pp_x) xs

let pp_list pp_x = pp_list_sep "" pp_x

let add_aux e =
  let g : unit -> variable =
    let i = ref 0 in
    (fun () -> incr i;  sprintf "T%d" !i) in
  let cs = ref [] in
  let add_clause op vs =
    let w = g () in
    cs := (w, op, vs) :: !cs; (true, w) in
  let neg (b, x) = (not b, x) in
  let rec go_op op es =
    add_clause op (List.map go es)
  and go = function
    | Var x -> (true, x)
    | Not e -> neg (go e)
    | And es -> go_op "and" es
    | Or es -> go_op "or" es in
  let b, v = go e in
  assert b;
  (v, List.rev !cs)

let pp_formula f e =
  let v, cs = add_aux e in
  let pp_v f (b, v) =
    if not b then fprintf f "-";
    fprintf f "%s" v in
  let pp_c f (w, op, vs) =
    fprintf f "%s = %s(%a)\n" w op (pp_list_sep "," pp_v) vs in
  fprintf f "output(%s)\n%a" v (pp_list pp_c) cs

let pp_string f = fprintf f "%s"

let pp_qcir f (qs, e) =
  let str_of_q = function
    | Exists -> "exists"
    | Forall -> "forall" in
  let pp_q f (q, vs) =
    fprintf f "%s(%a)\n" (str_of_q q) (pp_list_sep "," pp_string) vs in
  let qs = normalize_quantifiers qs in (* workaround for QFUN bug *)
  fprintf f "#QCIR-G14\n%a%a" (pp_list pp_q) qs pp_formula e

