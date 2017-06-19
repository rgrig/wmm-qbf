open Printf

exception Parsing_failed of string

let parse fn =
  let f = open_in fn in
  let lexbuf = Lexing.from_channel f in
  try
    let r = WmmParser.wmm WmmLexer.token lexbuf in
    close_in_noerr f;
    r
  with
    | WmmParser.Error ->
        (match Lexing.lexeme_start_p lexbuf with
        { Lexing.pos_lnum=line; Lexing.pos_bol=c0;
          Lexing.pos_fname=_; Lexing.pos_cnum=c1} ->
            let msg = sprintf "%s:%d:%d: parse error" fn line (c1-c0+1) in
            raise (Parsing_failed msg))

let range i k =
  let rec loop xs k = if k < i then xs else loop (k :: xs) (k - 1) in
  loop [] k

type var =
  { prefix : string
  ; bounds : (int * int) list }

let mk_var prefix bounds = { prefix; bounds }

let var_name prefix ds =
  let name = Buffer.create 10 in
  Printf.bprintf name "%s" prefix;
  let app x = Printf.bprintf name "_%d" x in
  List.iter app ds;
  Buffer.contents name

let var_at {prefix; bounds} cs =
  let chk (a, c) b = assert (a <= b && b <= c) in
  List.iter2 chk bounds cs;
  Qbf.mk_var (var_name prefix cs)

let at1 x = assert (List.length x.bounds = 1); (fun d1 -> var_at x [d1])
let at2 x = assert (List.length x.bounds = 2); (fun d1 d2 -> var_at x [d1;d2])
let at3 x = assert (List.length x.bounds = 3); (fun d1 d2 d3 -> var_at x [d1;d2;d3])

let curry2 f x y = f (x, y)
let uncurry2 f (x, y) = f x y

let rec cross = function
  | [] -> [[]]
  | xs :: xss ->
      let yss = cross xss in
      let pre x = List.map (fun ys -> x :: ys) yss in
      List.concat (List.map pre xs)

let var_allnames {prefix; bounds} =
  let ds = List.map (uncurry2 range) bounds in
  List.map (var_name prefix) (cross ds)

type context =
  { n : int
  ; c_spec : var
  ; d_spec : var
  ; e_spec : var
  ; f_spec : var
  ; g_spec : var }

let mk_context n =
  { n = n
  ; c_spec = mk_var "c" [0,n; 1,n]
  ; d_spec = mk_var "d" [1,n; 1,n]
  ; e_spec = mk_var "e" [1,n; 1,n]
  ; f_spec = mk_var "f" [1,n; 0,n; 1,n]
  ; g_spec = mk_var "g" [1,n; 0,n; 1,n] }

let implies ctx x y = Qbf.mk_and @@
  List.map (fun i -> Qbf.mk_implies (x i) (y i)) (range 1 ctx.n)

let equal ctx x y = Qbf.mk_and [implies ctx x y; implies ctx y x]

let justifies wmm = (* justify: def 4.2 *)
  let js = Hashtbl.create (List.length wmm.Wmm.reads) in
  let init w = Hashtbl.replace js w [] in
  let add (x, y) = Hashtbl.replace js y (x :: Hashtbl.find js y) in
  List.iter init wmm.Wmm.reads;
  List.iter add wmm.Wmm.justifies;
  (fun write read ->
    let one y xs qs =
      (* XXX our attempt at fixing 4.2: only justify new *)
      Qbf.mk_implies (read y) (Qbf.mk_or @@ write y :: List.map write xs) :: qs in
    Qbf.mk_and @@ Hashtbl.fold one js [])

let valid wmm =
  let ok_order x =
    let one (i, j) = Qbf.mk_implies (x j) (x i) in
    Qbf.mk_and @@ List.map one wmm.Wmm.order in
  let ok_conflicts x =
    let one (i, j) = Qbf.mk_not @@ Qbf.mk_and [x i; x j] in
    Qbf.mk_and @@ List.map one wmm.Wmm.conflicts in
  (fun x -> Qbf.mk_and [ok_order x; ok_conflicts x])

let valid1 wmm l h x = List.map (fun k -> valid wmm (x k)) (range l h)
let valid2 wmm l1 h1 l2 h2 x =
  List.concat @@ List.map (fun k -> valid1 wmm l2 h2 (x k)) (range l1 h1)

let transitive_closure ctx rel x ys z =
  let rel ys k = Qbf.mk_or [ rel ys k; equal ctx (ys (k-1)) (ys k) ] in
  Qbf.mk_and @@
  equal ctx x (ys 0)
  :: equal ctx (ys ctx.n) z
  :: List.map (rel ys) (range 1 ctx.n)

(*
(* FIXME: change the above with the below. But, first see FIXME on step1 *)
let transitive_closure ctx rel x ys z =
  let rel a b = Qbf.mk_or [ rel a b; equal ctx a b ] in
  let relk k = rel (ys (k - 1)) (ys k) in
  Qbf.mk_and @@
  equal ctx x (ys 0)
  :: equal ctx (ys ctx.n) z
  :: List.map relk (range 1 ctx.n)
*)

(* FIXME the [k] argument is an annoying hack *)
let step0 wmm ctx fg k = Qbf.mk_and (* ≾ in def 4.2 *) 
  [ implies ctx (fg (k - 1)) (fg k)
  ; justifies wmm (fg (k - 1)) (fg k) ]

let step1 wmm ctx c k =
  let step0 = step0 wmm ctx in
(*   let c = at2 ctx.c_spec in *)
  let d = at2 ctx.d_spec in
  let e = at2 ctx.e_spec in
  let f = at3 ctx.f_spec in
  let g = at3 ctx.g_spec in
  Qbf.mk_and (* ⊑ in def 4.3 *)
  [ implies ctx (c (k - 1)) (c k)
  ; Qbf.mk_implies
      (Qbf.mk_and @@
        transitive_closure ctx step0 (c (k - 1)) (f k) (d k)
        :: valid1 wmm 1 ctx.n (f k))
      (Qbf.mk_and
        [ transitive_closure ctx step0 (d k) (g k) (e k)
        ; justifies wmm (e k) (c k) ])
  ]

let add_validity wmm ctx q =
  let c = at2 ctx.c_spec in
  let d = at2 ctx.d_spec in
  let e = at2 ctx.e_spec in
  let g = at3 ctx.g_spec in
  let q = Qbf.mk_and @@ List.concat
    [ [ q ]
    ; valid1 wmm 1 ctx.n e
    ; valid2 wmm 1 ctx.n 0 ctx.n g ] in
  let q = Qbf.mk_implies (Qbf.mk_and (valid1 wmm 1 ctx.n d)) q in
  let q = Qbf.mk_and (q :: valid1 wmm 0 ctx.n c) in
  q

let add_quantifiers ctx q =
  let q = Qbf.mk_qbf q in
  let q = Qbf.mk_exists (var_allnames ctx.g_spec) q in
  let q = Qbf.mk_exists (var_allnames ctx.e_spec) q in
  let q = Qbf.mk_forall (var_allnames ctx.f_spec) q in
  let q = Qbf.mk_forall (var_allnames ctx.d_spec) q in
  let q = Qbf.mk_exists (var_allnames ctx.c_spec) q in
  q

let is_set ctx x js =
  let x = at1 x in
  let one j =
    if List.mem j js
    then x j
    else Qbf.mk_not (x j) in
  Qbf.mk_and @@ List.map one (range 1 ctx.n)

