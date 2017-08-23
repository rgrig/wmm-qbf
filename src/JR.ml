module E = EventStructure
module U = Util

open Printf

(* TODO: optimize validity checks; think sequence, and correctness. *)
         
(* Always Justifies *)
let always_justifies es = MM.intersect_n [ MM.subset; MM.justifies es; MM.valid_rel es ]


(* Always Justifies*

   There is a proof burden to show that applying that relation n times
   gives totality to the model.
 *)
let always_justifies_tc es = MM.at_most_n es es.E.events_number (always_justifies es)

(* Always Eventually Justifies 

   This relation contains always_justifies which is applied n times.
 *)
let always_eventually_justifies es =
  let justifies = MM.justifies es in
  let aj_tc = always_justifies_tc es in
  let sequence = MM.sequence es in
  let ae_justifies =
    (fun x y ->
      let z = MM.fresh_so_var es 1 in
      MM.forall z
        (Qbf.mk_implies
          [aj_tc x z]
          (sequence aj_tc justifies z y))) in
  (* Query: in the doc, we do not check valid_rel here. *)
  MM.intersect_n [ MM.subset; ae_justifies; MM.valid_rel es ]

(* Always Eventually Justifies Transitively Closed
   
   Similar to Always Justifies there is a proof burden to show that
   appling the relation n times is total.
 *)
let always_eventually_justifies_tc es = MM.at_most_n es es.E.events_number (always_eventually_justifies es)

(* Comment: the division between the description of the model given here and the
    built-in functions seems less than ideal right now.

     - Do we have to have the model writer ask for a fresh configuration, or could that be
        within the MM.forall function.

     - Also, there are bits buried in MM.ml that the model writer might want to have their
        hands on: we can't write the distinction between bug-fixed J+R and paper J+R at
        the moment.

    Query: Where is the goal represented?
     - In JRCheck.ml
 *)


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
  let x = MM.fresh_so_var es 1 in
  let y = MM.fresh_so_var es 1 in
  let q = Qbf.mk_and [ MM.equals_set x now; always_eventually_justifies es x y ] in
  let q = MM.exists x (MM.exists y q) in
  List.map (MM.set_of_model y) (Qbf.models q)

let do_decide es target =
  let x = MM.fresh_so_var es 1 in
  let y = MM.fresh_so_var es 1 in
  let q = Qbf.mk_and
    [ MM.equals_set x []
    ; MM.equals_set y target
    ; always_eventually_justifies_tc es x y ] in
  let q = MM.exists x (MM.exists y q) in
  printf "result: %b\n" (Qbf.holds q)
              
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
