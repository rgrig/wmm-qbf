open Printf

(* DBG *)
module U = Util

(* OLD

module U = Util

let name_of_wmm wmm =
  let b = Buffer.create (wmm.Wmm.events + 1) in
  for i = 1 to wmm.Wmm.events do
    bprintf b (if List.mem i wmm.Wmm.execution then "1" else "0")
  done;
  Buffer.contents b

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

let step prefix wmm =
  let q = query wmm in
  let qcir_name = sprintf "%s-%s.qcir" prefix (name_of_wmm wmm) in
  let sol_name = sprintf "%s-%s.out" prefix (name_of_wmm wmm) in
  let qcir = open_out qcir_name in
  fprintf qcir "%a" Qbf.pp_qcir q;
  close_out qcir;
  run_qbf_solver qcir_name sol_name;
  parse_qbf_output sol_name

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

let do_one fn =
  (* XXX: reinstate the bfs & dot dumping *)
  let es = U.parse fn in
  let x = MM.fresh_configuration es in
  let y = MM.fresh_configuration es in
  let q = Qbf.mk_and [ MM.equals_set x []; JR.step1 es x y ] in
  let q = MM.exists x (MM.exists y q) in
  let ms = Qbf.models fn q in
  let ys = List.map (MM.set_of_model y) ms in
  let hp_model f xs = fprintf f "exec %a\n" (U.hp_list_sep " " U.hp_int) xs in
  printf "%a" (U.hp_list hp_model) ys

let () =
  Arg.parse [] do_one "WmmEnum <infiles>"

