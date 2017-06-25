open Printf

module E = EventStructure
module U = Util

(* OLD

module U = Util

let sname_of_wmm wmm =
  let b = Buffer.create 10 in
  let xs = List.sort compare wmm.Wmm.execution in
  let rec loop = function
    | [] -> ()
    | x :: xs -> bprintf b ",%d" x; loop xs in
  let f = function
    | [] -> ()
    | x :: xs -> bprintf b "%d" x; loop xs in
  f xs;
  Buffer.contents b

let dump_dot fn g =
  let o = open_out fn in
  fprintf o "digraph x {\n";
  let dump_arc x ys =
    let f y = fprintf o "  \"%s\" -> \"%s\";\n" x y in
    List.iter f ys in
  Hashtbl.iter dump_arc g;
  fprintf o "}\n";
  close_out o
*)

let name_of es xs =
  let b = Buffer.create (es.E.events_number + 1) in
  for i = 1 to es.E.events_number do
    bprintf b (if List.mem i xs then "1" else "0")
  done;
  Buffer.contents b

let step es fn now =
  let x = MM.fresh_configuration es in
  let y = MM.fresh_configuration es in
  let q = Qbf.mk_and [ MM.equals_set x []; JR.step1 es x y ] in
  let q = MM.exists x (MM.exists y q) in
  List.map (MM.set_of_model y) (Qbf.models fn q)

let do_one fn =
  (* XXX: reinstate dot dumping *)
  let es = U.parse fn in
  let fn = Filename.remove_extension fn in
  let seen = Hashtbl.create 101 in
  let rec bfs xs = if xs <> Que.empty then begin
    let x, xs = Que.pop xs in
    let fnx = sprintf "%s-%s" fn (name_of es x) in
    let ys = step es fnx x in
    let look xs y = if not (Hashtbl.mem seen y) then begin
      printf "exec: %a\n%!" (U.hp_list_sep " " U.hp_int) y;
      Hashtbl.add seen y ();
      Que.push y xs
    end else xs in
    bfs (List.fold_left look xs ys)
  end in
  Hashtbl.add seen [] ();
  bfs (Que.push [] Que.empty)

let () =
  Arg.parse [] do_one "WmmEnum <infiles>"

