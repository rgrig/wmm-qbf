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

(* TODO: add small simplifications in these constructors *)
(* Do we need these functions? Is it really better than having the
   constructors? *)
let mk_var v = Var v
let mk_and ps = And ps
let mk_or ps = Or ps
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

(* "hp" stands for hideous printing: the pretty one is done by @@deriving *)
let hp f p =
  let top, clauses = to_clauses p in
  let hp_v f (b, v) =
    if not b then fprintf f "-";
    fprintf f "%s" v in
  let hp_vs f = function
    | None -> ()
    | Some vs -> fprintf f "%a;" (U.hp_list_sep "," U.hp_string) vs in
  let hp_c f (w, op, vs, ps) =
    fprintf f "%s = %s(%a%a)\n" w op hp_vs vs (U.hp_list_sep "," hp_v) ps in
  fprintf f "output(%s)\n%a" top (U.hp_list hp_c) clauses

let hp_qcir f p =
  let rec pm qs = function
    | Exists (vs, p, _) -> pm ((true, vs) :: qs) p
    | Forall (vs, p, _) -> pm ((false, vs) :: qs) p
    | p -> (List.rev qs, p) in
  let prefix, matrix = pm [] p in
  let hp_q f (t, vs) =
    let t = if t then "exists" else "forall" in
    fprintf f "%s(%a)\n" t (U.hp_list_sep "," U.hp_string) vs in
  fprintf f "#QCIR-G14\n%a%a" (U.hp_list hp_q) prefix hp matrix

let run_solver options in_name out_name =
  let cmd = sprintf "qfun-enum %s -a -i64 %s > %s" options in_name out_name in
  Sys.command cmd

let re_model_line = Str.regexp "^v.*$"
let re_var = Str.regexp "\\+\\([a-zA-Z0-9_]+\\)"
let parse_models fn =
  let sol = open_in fn in
  let r = ref [] in
  let rec loop () =
    let line = input_line sol in
    if Str.string_match re_model_line line 0 then begin
      let xs = ref [] in
      let rec get i =
        ignore (Str.search_forward re_var line i);
        xs := Str.matched_group 1 line :: !xs;
        get (Str.match_end ()) in
      try get 0 with Not_found -> ();
      r := !xs :: !r
    end;
    loop () in
  try loop () with End_of_file -> (close_in sol; !r)

let re_yes_answer = Str.regexp "^s cnf 1"
let parse_answer fn =
  let sol = open_in fn in
  let rec loop () =
    let line = input_line sol in
    Str.string_match re_yes_answer line 0 || loop () in
  try loop () with End_of_file -> (close_in sol; false)

let call_solver options parse fn p =
  let p = preprocess p in
  let qcir_fn = sprintf "%s.qcir" fn in
  let out_fn = sprintf "%s.out" fn in
  let qcir = open_out qcir_fn in
  hp_qcir qcir p;
  close_out qcir;
  (* Discard the return code *)
  (* TODO: What is the output if the solver returns non-zero. Is it
     worth parsing it? *)
  let _ = run_solver options qcir_fn out_fn in
  parse out_fn

let holds = call_solver "" parse_answer
let models = call_solver "-e" parse_models

