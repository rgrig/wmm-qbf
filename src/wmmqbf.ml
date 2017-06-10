open Format
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
            let msg = sprintf "@[%s:%d:%d: parse error@]" fn line (c1-c0+1) in
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
  let c = mkV2 "c" (0,n) (1,n) in
  let d = mkV2 "d" (1,n) (1,n) in
  let e = mkV2 "e" (1,n) (1,n) in
  let f = mkV3 "f" (1,n) (0,n) (1,n) in
  let g = mkV3 "g" (1,n) (0,n) (1,n) in
  let justifies _ _ =
    Qbf.mk_and [] in (* TODO *)
  let implies x y = Qbf.mk_and @@
    List.map (fun i -> Qbf.mk_implies (x i) (y i)) (range 1 n) in
  let equal x y = Qbf.mk_and [implies x y; implies y x] in
  let small_step x j = Qbf.mk_and
    [ implies (x (j - 1)) (x j)
    ; justifies (x (j - 1)) (x j)] in
  let before alpha x omega = Qbf.mk_and @@
    equal alpha (x 0)
    :: equal (x n) omega
    :: List.map (small_step x) (range 1 n) in
  let step k = Qbf.mk_and @@
    [ equal (c (k-1)) (f k 0)
    ; equal (f k n) (d k)
    ; Qbf.mk_implies
      (before (c (k - 1)) (f k) (d k))
      (before (d k) (g k) (e k)) ] (* TODO: add  Ek -> Ck *)
  in
  let q = Qbf.mk_and @@ List.map step (range 1 n) in
  Qbf.pp_t stdout q;
  ()

let () =
  Arg.parse [] do_one "wmmqbf <infile>"
