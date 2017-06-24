open Printf

module U = Util

type variable = string
  [@@deriving show] (* DBG *)
type model = variable list
  [@@deriving show] (* DBG *)
type qid = int (* quantifier id *)
  [@@deriving show] (* DBG *)

type t =
  | Var of variable
  | Not of t
  | And of t list
  | Or of t list
  | Exists of variable list * t * qid
  | Forall of variable list * t * qid
  [@@deriving show] (* DBG *)

let last_qid = ref 0
let fresh_qid () = incr last_qid; !last_qid

let mk_var v = Var v
let mk_and ps = And ps
let mk_or ps = Or ps
let mk_not = function Not p -> p | p -> Not p
let mk_exists vs p = Exists (vs, p, fresh_qid ())
let mk_forall vs p = Forall (vs, p, fresh_qid ())

let mk_implies ps q = mk_or (q :: List.map mk_not ps)

(* {{{ Helpers for preprocess. *)

let simple_quantifiers p =
  let module S = Set.Make (String) in
  let all_quantified p =
    let rec f xs = function
      | Var v -> S.mem v xs
      | Not p -> f xs p
      | And ps | Or ps -> List.for_all (f xs) ps
      | Exists (vs, p, _) | Forall (vs, p, _) ->
          let xs = S.union xs (S.of_list vs) in
          f xs p in
    f S.empty p in
  let no_repeated_quantifiers p =
    let exception Repeated in
    let rec f xs = function
      | Var _ -> xs
      | Not p -> f xs p
      | And ps | Or ps -> List.fold_left f xs ps
      | Exists (vs, p, _) | Forall (vs, p, _) ->
          let chk xs v =
            if S.mem v xs then raise Repeated;
            S.add v xs in
          let xs = List.fold_left chk xs vs in
          f xs p in
    try ignore (f S.empty p); true with Repeated -> false in
  all_quantified p && no_repeated_quantifiers p

(* PRE: simple_quantifiers;  POST: returns a tree *)
let quant_deps p =
  let g = Hashtbl.create 101 in
  let rec f lq = function
    | Var _ -> ()
    | Not p -> f lq p
    | And ps | Or ps -> List.iter (f lq) ps
    | Exists (_, p, q) | Forall (_, p, q) ->
        let link lq =
          let qs = try Hashtbl.find g lq with Not_found -> [] in
          Hashtbl.replace g lq (q :: qs) in
        U.option () link lq;
        f (Some q) p in
  f None p; g

(* PRE: simple_quantifiers *)
let prenex =
  let rec u_not = function
    | Exists (vs, p, q) -> Forall (vs, u_not p, q)
    | Forall (vs, p, q) -> Exists (vs, u_not p, q)
    | p -> mk_not p in
  let add_exists vs q cont r = cont (Exists (vs, r, q)) in
  let add_forall vs q cont r = cont (Forall (vs, r, q)) in
  let rec u_andor op qs ps = function
    | [] -> qs (op ps)
    | Exists (vs, p, q) :: rs -> u_andor op (add_exists vs q qs) ps (p :: rs)
    | Forall (vs, p, q) :: rs -> u_andor op (add_forall vs q qs) ps (p :: rs)
    | r :: rs -> u_andor op qs (r :: ps) rs in
  let rec top = function
    | Var v as p -> p
    | Not p -> u_not (top p)
    | And ps -> u_andor mk_and U.id [] (List.map top ps)
    | Or ps -> u_andor mk_or U.id [] (List.map top ps)
    | Exists (vs, p, q) -> Exists (vs, top p, q)
    | Forall (vs, p, q) -> Forall (vs, top p, q)
  in
  top

let que_empty = ([], [])
let que_push z (xs, ys) = (xs, z :: ys)
let que_pop = function
  | ([], []) -> failwith "INTERNAL(pdbgg): pop from empty queue"
  | ([], y :: ys) -> (y, (List.rev ys, []))
  | (x :: xs, ys) -> (x, (xs, ys))

(* PRE: simple_quantifiers p && prenex p && is_tree deps *)
let optimize_quants deps p =
  let quants = Hashtbl.create 101 in
  let addq t vs q =
    assert (not (Hashtbl.mem quants q));
    Hashtbl.add quants q (t, vs) in
  let rec matrix = function
    | Exists (vs, p, q) -> addq true vs q; matrix p
    | Forall (vs, p, q) -> addq false vs q; matrix p
    | p -> p in
  let m = matrix p in
  let preq t vs q cont p =
    cont (if t then Exists (vs, p, q) else Forall (vs, p, q)) in
  let rec bfs pre t now nxt =
    if now = que_empty && nxt = que_empty then pre m
    else if now = que_empty then bfs pre (not t) nxt now
    else begin
      let q, now = que_pop now in
      let qt, qvs = Hashtbl.find quants q in
      if qt = t then begin
        let children = try Hashtbl.find deps q with Not_found -> [] in
        let now = List.fold_left (U.flip que_push) now children in
        bfs (preq qt qvs q pre) t now nxt
      end else bfs pre t now (que_push q nxt)
    end in
  let que_one x = que_push x que_empty in
  (match p with
  | Exists (_, _, q) -> bfs U.id true (que_one q) que_empty
  | Forall (_, _, q) -> bfs U.id false (que_one q) que_empty
  | p -> p)


(* }}} Helpers for preprocess. *)

let preprocess p =
  assert (simple_quantifiers p); (* Other cases are not needed, I think. *)
  let deps = quant_deps p in
  let p = prenex p in
  let p = optimize_quants deps p in
  p

let holds _ = failwith "wqqsh"

let models p =
  printf "%s\n" (show p);
  let p = preprocess p in
  printf "%s\n" (show p);
  failwith "rhqmb"

(* OLD

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

let pp_int f x = fprintf f "%d" x

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

*)
