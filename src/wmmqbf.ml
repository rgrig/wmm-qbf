open Printf
open WmmParser

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

let mkV prefix bounds xs =
  let chk (a, c) b = assert (a <= b && b <= c) in
  List.iter2 chk bounds xs;
  let name = Buffer.create 10 in
  Printf.bprintf name "%s" prefix;
  let app x = Printf.bprintf name "_%d" x in
  List.iter app xs;
  Qbf.mk_var (Buffer.contents name)

let mkV1 prefix (l1, h1) x1 =
  mkV prefix [(l1, h1)] [x1]
let mkV2 prefix (l1, h1) (l2, h2) x1 x2 =
  mkV prefix [(l1, h1); (l2, h2)] [x1; x2]
let mkV3 prefix (l1, h1) (l2, h2) (l3, h3) x1 x2 x3 =
  mkV prefix [(l1, h1); (l2, h2); (l3, h3)] [x1; x2; x3]

let range i k =
  let r = ref [] in
  for j = k downto i do r := j :: !r done;
  !r


let do_one fn =
  let wmm = parse fn in
  let n = wmm.Wmm.events in
  let empty_set = mkV1 "Z" (1,n) in
  let execution_set = mkV1 "E" (1,n) in
  let c = mkV2 "c" (0,n) (1,n) in
  let d = mkV2 "d" (1,n) (1,n) in
  let e = mkV2 "e" (1,n) (1,n) in
  let f = mkV3 "f" (1,n) (0,n) (1,n) in
  let g = mkV3 "g" (1,n) (0,n) (1,n) in
  let implies x y = Qbf.mk_and @@
    List.map (fun i -> Qbf.mk_implies (x i) (y i)) (range 1 n) in
  let equal x y = Qbf.mk_and [implies x y; implies y x] in
  let justifies =
    let js = Hashtbl.create (List.length wmm.Wmm.reads) in
    let init w = Hashtbl.replace js w [] in
    let add (x, y) = Hashtbl.replace js y (x :: Hashtbl.find js y) in
    List.iter init wmm.Wmm.reads;
    List.iter add wmm.Wmm.justifies;
    (fun write read ->
      let one y xs qs =
        Qbf.mk_implies (read y) (Qbf.mk_or @@ List.map write xs) :: qs in
      Qbf.mk_and @@ Hashtbl.fold one js []) in
  let transitive_closure rel x ys z = Qbf.mk_and @@
    equal x (ys 0)
    :: Qbf.mk_or (List.map (fun k -> equal (ys k) z) (range 0 n))
    :: List.map (rel ys) (range 1 n) in
  let step0 fg k = Qbf.mk_and
    [ implies (fg (k - 1)) (fg k)
    ; justifies (fg (k - 1)) (fg k) ] in
  let step1 c k = Qbf.mk_and
    [ implies (c (k - 1)) (c k)
    ; Qbf.mk_implies
        (transitive_closure step0 (c (k - 1)) (f k) (d k))
        (Qbf.mk_and
          [ transitive_closure step0 (d k) (g k) (e k)
          ; justifies (e k) (c k) ])
    ] in
  let valid =
    let ok_order x =
      let one (i, j) = Qbf.mk_implies (x j) (x i) in
      Qbf.mk_and @@ List.map one wmm.Wmm.order in
    let ok_conflicts x =
      let one (i, j) = Qbf.mk_not @@ Qbf.mk_and [x i; x j] in
      Qbf.mk_and @@ List.map one wmm.Wmm.conflicts in
    (fun x -> Qbf.mk_and [ok_order x; ok_conflicts x]) in
  let v1 l h x = List.map (fun k -> valid (x k)) (range l h) in
  let v2 l1 h1 l2 h2 x =
    List.concat @@ List.map (fun k -> v1 l2 h2 (x k)) (range l1 h1) in
  let is_set x js =
    let one j =
      if List.mem j js
      then x j
      else Qbf.mk_not (x j) in
    Qbf.mk_and @@ List.map one (range 1 n) in
  let q = Qbf.mk_and
    [ is_set empty_set []
    ; is_set execution_set wmm.Wmm.execution
    ; transitive_closure step1 empty_set c execution_set ] in
  let q = Qbf.mk_and @@ List.concat
    [ [ q ]
    ; v1 1 n e
    ; v2 1 n 0 n f
    ; v2 1 n 0 n g ] in
  let q = Qbf.mk_implies (Qbf.mk_and (v1 1 n d)) q in
  let q = Qbf.mk_and (q :: v1 0 n c) in
  Qbf.pp_t stdout q;
  (* FIXME HACK *)
  let d0 x =
    List.map x (range 1 n) in
  let d1 l1 h1 x =
    let one k = List.map (x k) (range 1 n) in
    List.concat @@ List.map one (range l1 h1) in
  let d2 l1 h1 l2 h2 x =
    let one x = List.map x (range 1 n) in
    let two x = List.concat @@ List.map (fun k -> one (x k)) (range l2 h2) in
    List.concat @@ List.map (fun k -> two (x k)) (range l1 h1) in
  let pp_var f = function
    | Qbf.Var x -> fprintf f "%s" x
    | _ -> failwith "(ltqsi)" in
  printf "\n===\n";
  printf "exists(%a)\n" (Qbf.pp_list_sep "," pp_var)
    (List.concat [d1 0 n c; d0 empty_set; d0 execution_set]);
  printf "forall(%a)\n" (Qbf.pp_list_sep "," pp_var) (d1 1 n d);
  printf "exists(%a)\n" (Qbf.pp_list_sep "," pp_var)
    (List.concat [d1 1 n e; d2 1 n 0 n f; d2 1 n 0 n g]);
  ()

let () =
  Arg.parse [] do_one "wmmqbf <infile>"
