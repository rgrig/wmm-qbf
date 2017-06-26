open Printf

module E = EventStructure
module U = Util

(* {{{ Globals. *)

let enum_mode = ref false

(* }}} Globals. *)

let sname_of xs =
  let b = Buffer.create 10 in
  let xs = List.sort compare xs in
  let rec loop = function
    | [] -> ()
    | x :: xs -> bprintf b ",%d" x; loop xs in
  let f = function
    | [] -> bprintf b "START"
    | x :: xs -> bprintf b "%d" x; loop xs in
  f xs;
  Buffer.contents b

let name_of es xs =
  let b = Buffer.create (es.E.events_number + 1) in
  for i = 1 to es.E.events_number do
    bprintf b (if List.mem i xs then "1" else "0")
  done;
  Buffer.contents b

let dump_dot fn es target whys =
  let target = U.map_option (List.sort compare) target in
  let nodes = Hashtbl.create 101 in
  let reg_n x = Hashtbl.replace nodes x () in
  List.iter (fun (x, y) -> reg_n x; reg_n y) whys;
  let o = open_out fn in
  fprintf o "digraph x {\n";
  let dump_node x () =
    let hp_style o x =
      let shape = if Some x = target then "oval" else "box" in
      let fillcolor = if E.self_justified es x then "green" else "white" in
      let label = sname_of x in
      let label = if Some x = target then "TARGET "^label else label in
      fprintf o "style=filled;shape=%s;fillcolor=%s;label=\"%s\""
        shape fillcolor label in
    fprintf o "  \"%s\" [%a];\n" (name_of es x) hp_style x in
  let dump_arc (x, y) =
    fprintf o "  \"%s\" -> \"%s\";\n" (name_of es x) (name_of es y) in
  fprintf o "  rankdir=LR;\n";
  Hashtbl.iter dump_node nodes;
  List.iter dump_arc whys;
  fprintf o "}\n";
  close_out o

let step es fn now =
  let x = MM.fresh_configuration es in
  let y = MM.fresh_configuration es in
  let q = Qbf.mk_and [ MM.equals_set x now; JR.step1 es x y ] in
  let q = MM.exists x (MM.exists y q) in
  List.map (MM.set_of_model y) (Qbf.models fn q)

let do_decide fn es target =
  let x = MM.fresh_configuration es in
  let y = MM.fresh_configuration es in
  let q = Qbf.mk_and
    [ MM.equals_set x []
    ; MM.equals_set y target
    ; JR.step1tc es x y ] in
  let q = MM.exists x (MM.exists y q) in
  let fn = sprintf "%s-decide" fn in
  printf "result: %b\n" (Qbf.holds fn q)

let do_enum fn es target =
  let whys = ref [] in
  let seen = Hashtbl.create 101 in
  let look x xs y = if not (Hashtbl.mem seen y) then begin
    if Some y = target then printf "TARGET ";
    printf "exec: %a\n%!" (U.hp_list_sep " " U.hp_int) y;
    Hashtbl.add seen y ();
    U.option () (fun x -> whys := (x, y) :: !whys) x;
    Que.push y xs
  end else xs in
  let rec bfs xs = if xs <> Que.empty then begin
    let x, xs = Que.pop xs in
    let fnx = sprintf "%s-%s" fn (name_of es x) in
    let ys = step es fnx x in
    bfs (List.fold_left (look (Some x)) xs ys)
  end in
  bfs (look None Que.empty []);
  dump_dot (sprintf "%s.dot" fn) es target !whys


let do_one fn =
  let es, target = U.parse fn in
  let fn = Filename.remove_extension fn in
  if !enum_mode
  then do_enum fn es target
  else (match target with
    | None -> eprintf "W: skipping %s: no target execution\n" fn
    | Some target -> do_decide fn es target)


let cmd_spec = Arg.
  [ "-e", Set enum_mode, "enumerate all executions" ]

let () =
  Arg.parse cmd_spec do_one "JrCheck <infiles>"

