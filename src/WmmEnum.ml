open Printf

(* DBG *)
module ES = EventStructure
module P = EsParser
module U = Util

(* OLD

module U = Util

let query wmm =
  let ctx = U.mk_context 1 wmm.Wmm.events in
  let start_var = U.mk_var "START" [1,ctx.U.n] in
  let end_var = U.mk_var "END" [1,ctx.U.n] in
  let q =
    let step1 = U.step1 wmm ctx in
    let c = U.at2 ctx.U.c_spec in
    let start_var = U.at1 start_var in
    let end_var = U.at1 end_var in
    Qbf.mk_and
    [ U.equal ctx start_var (c 0)
    ; U.equal ctx end_var (c 1)
    ; step1 c 1 ] in
  let q = Qbf.mk_and
    [ U.is_set ctx start_var wmm.Wmm.execution
    ; q ] in
  let q = U.add_validity wmm ctx q in
  let q = U.add_quantifiers ctx q in
  let q = Qbf.mk_exists (U.var_allnames start_var) q in
  let q = Qbf.mk_exists (U.var_allnames end_var) q in
  q

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

(* FIXME huge hack *)
let run_qbf_solver qcir_name out_name =
  let cmd = sprintf "qfun-enum -a -e %s > %s" qcir_name out_name in
(*   printf "executing: %s\n" cmd; *)
  ignore (Sys.command cmd)

let re_model_line = Str.regexp "^v.*$"
let re_end_var = Str.regexp "+END_\\([0-9]*\\)"
let parse_qbf_output fn =
  let sol = open_in fn in
  let r = ref [] in
  let rec loop () =
    let line = input_line sol in
    if Str.string_match re_model_line line 0 then begin
      let xs = ref [] in
      let rec get i =
        ignore (Str.search_forward re_end_var line i);
        xs := int_of_string (Str.matched_group 1 line) :: !xs;
        get (Str.match_end ()) in
      try get 0 with Not_found -> ();
      r := !xs :: !r
    end;
    loop () in
  try loop () with End_of_file -> !r

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
  let es = U.parse fn in
  let x = MM.fresh_configuration es in
  let y = MM.fresh_configuration es in
  let q = JR.step1tc es x y in (* TODO: add that x is empty set *)
  let ms = Qbf.models q in
  ()

let () =
  Arg.parse [] do_one "wmmEnum <infiles>"

