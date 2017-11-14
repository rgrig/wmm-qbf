module ArityMap = Map.Make(String)

let rels xs =
  let f acc (n, r) =
    let k = fst n in
    if SO.RelMap.mem k acc then failwith "repeated relation symbol (voxdy)";
    SO.RelMap.add k r acc in
  List.fold_left f SO.RelMap.empty xs

let get_arity s r =
  let arity = List.length (List.nth r 0) in
  if not (List.for_all (fun e -> List.length e = arity) r) then
    failwith (Printf.sprintf "inconsistent arity of symbol %s" s);
  arity

let check_arities s f =
  let check_structure sym l arr_map =
    let a = get_arity sym l in
    if ArityMap.mem sym arr_map
    then failwith "relation defined multiple times in SO structure";
    ArityMap.add sym a arr_map
  in
  let rec check_formula fml arr_map =
    match fml with
    | SO.CRel (s, ts) ->
       let a = List.length ts in
       begin
       try
         let a' = ArityMap.find (fst s) arr_map in
         assert (a = a')
       with
         Not_found ->
         failwith (Printf.sprintf "symbol %s not defined in SO structure" (SO.show_rel_sym s))
       | Assert_failure _ ->
          failwith (Printf.sprintf "symbol %s applied with inconsistent arity" (SO.show_rel_sym s))
       end;
       arr_map
    | SO.QRel (s, ts) ->
       let a = List.length ts in
       begin
         try
           let a' = ArityMap.find (fst s) arr_map in
           assert (a = a');
           arr_map
         with
           Not_found ->
           ArityMap.add (fst s) a arr_map
         | Assert_failure _ ->
            failwith (Printf.sprintf "symbol %s applied with inconsistent arity" (SO.show_rel_sym s))
       end

    (* When a variable is quantified: shadow it's previous definition in the arity map *)
    | SO.FoAny ((s, a), f) | SO.FoAll ((s, a), f) | SO.SoAny ((s, a), f) | SO.SoAll ((s, a), f) ->
       check_formula f (ArityMap.add s a arr_map)

    | SO.And fs | SO.Or fs ->
       List.fold_right check_formula fs arr_map
    | SO.Not f ->
       check_formula f arr_map
  in
  ignore @@ SO.RelMap.fold check_structure s.SO.relations ArityMap.empty;
  
  (* Collect the arities of all of the constant relation symbols *)
  let collect_arities = SO.RelMap.fold (fun k v a -> ArityMap.add k (get_arity k v) a) in
  ignore @@ check_formula f (collect_arities s.SO.relations ArityMap.empty)

let check_inv s f =
  check_arities s f (*
  check_elem_bounds s f*)
  
let model_check s f =
  failwith "exjfn"

let so_to_qbf s f =
  Qbf.mk_false ()
