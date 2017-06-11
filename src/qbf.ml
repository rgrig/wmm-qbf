open Printf

type variable = string

type t =
  | Var of variable
  | Not of t
  | And of t list
  | Or of t list
  | All of variable * t
  | Any of variable * t

let mk_var v = Var v
let mk_implies f g = Or [Not f; g]
let mk_and xs = And xs
let mk_or xs = Or xs
let mk_not x = Not x

let rec pp_list_sep sep pp_x f = function
  | [] -> ()
  | [x] -> pp_x f x
  | x :: ((_ :: _) as xs) ->
      fprintf f "%a%s%a" pp_x x sep (pp_list_sep sep pp_x) xs

let pp_t f e =
  let i = ref 0 in
  let g () = incr i; (true, sprintf "g%d" !i) in
  let neg (b, x) = (not b, x) in
  let pp_var f (b, x) =
    fprintf f "%s%s" (if b then "" else "-") x in
  let rec go_op op es =
    let vs = List.map go es in
    let w = g () in
    fprintf f "%a = %s(%a)\n" pp_var w op (pp_list_sep "," pp_var) vs;
    w
  and go = function
    | Var x -> (true, x)
    | Not e -> neg (go e)
    | And es -> go_op "and" es
    | Or es -> go_op "or" es
    | _ -> failwith "todo" in
  let o = go e in
  fprintf f "output(%a)\n" pp_var o
