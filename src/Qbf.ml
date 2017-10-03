open Printf

module U = Util
module R = RunSolver

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

(* No idea why PPX isn't doing the lifting for me. Probably because
   I've messed up the compile options *)
let show_variable v = v
let rec show_t t =
  match t with
    Var v -> v
  | Not t -> "¬" ^ (show_t t)
  | And [] -> "True"
  | Or [] -> "False"
  | And ts -> String.concat "∧" (List.map show_t ts)
  | Or ts -> String.concat "∨" (List.map show_t ts)
  | Exists (ts, t, q) ->
    "∃" ^ (String.concat "," (List.map show_variable ts)) ^ ". " ^ (show_t t)
  | Forall (ts, t, q) -> "∀" ^ show_t t ^ ". " ^ (show_t t)

let last_qid = ref 0
let fresh_qid () = incr last_qid; !last_qid

(* TODO: add small simplifications in these constructors *)
(* Do we need these functions? Is it really better than having the
   constructors? *)
let mk_var v = Var v
let mk_and ps = And ps
let mk_or ps = Or ps
(* An and gate with zero inputs represents the constant true. *)
let mk_true () = And []
(* An or gate with zero inputs represents the constant false. *)
let mk_false () = Or []
let mk_not = function Not p -> p | p -> Not p
let mk_exists vs p = Exists (vs, p, fresh_qid ())
let mk_forall vs p = Forall (vs, p, fresh_qid ())

(* p₁ ∧ p₂ ∧ pₙ → q  ⇔  ¬p₁ ∨ ¬p₂ ∨ ¬pₙ ∨ q *)
let mk_implies ps q = mk_or (q :: List.map mk_not ps)

(* {{{ Helpers for preprocess. *)

let simple_quantifiers p =
  let module S = Set.Make (String) in
  let all_quantified p =
    let rec f xs = function
      | Var v -> if S.mem v xs then true else (Printf.printf "%s not quantified\n" v; false)
      | Not p -> f xs p
      | And ps | Or ps -> List.for_all (f xs) ps
      | Exists (vs, p, _) | Forall (vs, p, _) ->
          let xs = S.union xs (S.of_list vs) in
          f xs p in
    f S.empty p
  in
  let no_repeated_quantifiers p =
    let exception Repeated in
    let rec f xs = function
      | Var _ -> xs
      | Not p -> f xs p
      | And ps | Or ps -> List.fold_left f xs ps
      | Exists (vs, p, _) | Forall (vs, p, _) ->
          let chk xs v =
            if S.mem v xs then
                begin
                  Printf.printf "%s repeated\n" v;
                  raise Repeated;
                end;
            S.add v xs in
          let xs = List.fold_left chk xs vs in
          f xs p in
    try ignore (f S.empty p); true with Repeated -> false
  in
  let repeats = no_repeated_quantifiers p in
  let all_quant = all_quantified p in
  if not repeats then
    Printf.printf "Repeated quantifiers.\n"
  else ();
  if not all_quant then
    Printf.printf "Not all variables are quantified.\n"
  else ();
  repeats && all_quant

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
    if now = Que.empty && nxt = Que.empty then pre m
    else if now = Que.empty then bfs pre (not t) nxt now
    else begin
      let q, now = Que.pop now in
      let qt, qvs = Hashtbl.find quants q in
      if qt = t then begin
        let children = try Hashtbl.find deps q with Not_found -> [] in
        let now = List.fold_left (U.flip Que.push) now children in
        bfs (preq qt qvs q pre) t now nxt
      end else bfs pre t now (Que.push q nxt)
    end in
  let que_one x = Que.push x Que.empty in
  (match p with
  | Exists (_, _, q) -> bfs U.id true (que_one q) Que.empty
  | Forall (_, _, q) -> bfs U.id false (que_one q) Que.empty
  | p -> p)


(* }}} Helpers for preprocess. *)

let preprocess p =
  assert (simple_quantifiers p); (* Other cases are not needed, I think. *)
  let deps = quant_deps p in
  let p = prenex p in
  let p = optimize_quants deps p in
  p

let to_clauses p =
  let g : unit -> variable =
    let i = ref 0 in
    (fun () -> incr i;  sprintf "T%d" !i) in
  let cs = ref [] in
  let add_clause op vs ps =
    let v = g () in
    cs := (v, op, vs, ps) :: !cs; (true, v) in
  let neg (b, x) = (not b, x) in
  let rec go_op op ps =
    add_clause op None (List.map go ps)
  and go_q q vs p =
    add_clause q (Some vs) [go p]
  and go = function
    | Var x -> (true, x)
    | Not p -> neg (go p)
    | And es -> go_op "and" es
    | Or es -> go_op "or" es
    | Exists (vs, p, _) -> go_q "exists" vs p
    | Forall (vs, p, _) -> go_q "forall" vs p in
  let b, v = go p in
  assert b;
  (v, List.rev !cs)

(* Hideous printing functions that print into a buffer instead. *)
let buffer_string buffer x = bprintf buffer "%s" x
let rec buffer_list_sep separator buffer_x buffer = function
  | [] -> ()
  | [x] -> buffer_x buffer x
  | x :: ((_ :: _) as xs) ->
  bprintf buffer "%a%s%a" buffer_x x separator (buffer_list_sep separator buffer_x) xs
let buffer_list buffer_x = buffer_list_sep "" buffer_x

let to_buffer buffer p =
  let top, clauses = to_clauses p in
  let buffer_v buffer (b, v) =
    if not b then bprintf buffer "-";
    bprintf buffer "%s" v in
  let buffer_vs buffer = function
    | None -> ()
    | Some vs -> bprintf buffer "%a;" (buffer_list_sep "," buffer_string) vs in
  let buffer_c buffer (w, op, vs, ps) =
    bprintf buffer "%s = %s(%a%a)\n" w op buffer_vs vs (buffer_list_sep "," buffer_v) ps in
  bprintf buffer "output(%s)\n%a" top (buffer_list buffer_c) clauses

let qcir_to_buffer buffer p =
  let rec pm qs = function
    | Exists (vs, p, _) -> pm ((true, vs) :: qs) p
    | Forall (vs, p, _) -> pm ((false, vs) :: qs) p
    | p -> (List.rev qs, p) in
  let prefix, matrix = pm [] p in
  let buffer_q buffer (t, vs) =
    let t = if t then "exists" else "forall" in
    bprintf buffer "%s(%a)\n" t (buffer_list_sep "," buffer_string) vs in
  bprintf buffer "#QCIR-G14\n%a%a" (buffer_list buffer_q) prefix to_buffer matrix


let build_query_string p =
  let p = preprocess p in
  let qcir = Buffer.create 16 in
  qcir_to_buffer qcir p;
  Buffer.contents qcir

let call_solver options parse p (debug, use_solver) =
  let query = build_query_string p in
  if debug then printf "%s\n" query;
  (* Discard the return code *)
  (* TODO: Handle solver errors? *)
  if use_solver
  then
    let out = R.run_solver options query in
    Some (parse out)
  else
    None

let holds = call_solver [||] Results.parse_answer
let models p debug =
  (* We really can't do enum if the user turns off the solver *)
  match call_solver [|"-e"|] Results.parse_models p (debug, true) with
    Some r -> r
  | None -> raise (Util.Runtime_error "solver returned no response")
