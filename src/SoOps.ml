let rels xs =
  let f acc (n, r) =
    if SO.RelMap.mem n acc then failwith "repeated relation symbol (voxdy)";
    SO.RelMap.add n r acc in
  List.fold_left f SO.RelMap.empty xs
(*
let check_arities s f =
  let h = Hashtbl.create 1 in
  let chk n xs =
    let a = List.length xs in
    let o = try Hashtbl.find h n with Not_found -> a in
    if o <> a then failwith (Printf.sprintf "(aeprr) bad arity for %s" n);
    Hashtbl.replace h n a in
  let iter_chk n ls = List.iter (chk n) ls in
  SO.RelMap.iter iter_chk s.SO.relations;
  let rec chk_formula = function
    | FoAny (_, f)
    | FoAll (_, f)
    | SoAny (_, f)
    | SoAll (_, f)
    | Not f
      -> chk_formula f
    | And (f1, f2)
    | Or (f1, f2)
      -> chk_formula f1; chk_formula f2
    | CRel
  in
*)

let check_inv s f =
  failwith "eynkb"
  (*
  check_arities s f;
  check_elem_bounds s f
*)
let model_check s f =
  failwith "exjfn"
