open Printf
module U = Util
module ArityMap = Map.Make(String)

let rels xs =
  let f acc (k, r) =
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
         let a' = ArityMap.find s arr_map in
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
           let a' = ArityMap.find s arr_map in
           assert (a = a');
           arr_map
         with
           Not_found ->
           ArityMap.add s a arr_map
         | Assert_failure _ ->
            failwith (Printf.sprintf "symbol %s applied with inconsistent arity" (SO.show_rel_sym s))
       end

    | SO.FoAny (_, f) | SO.FoAll (_, f) ->
       check_formula f arr_map

    (* When a variable is quantified: shadow it's previous definition in the arity map *)
    | SO.SoAny (s, a, f) | SO.SoAll (s, a, f) ->
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

let term_to_var s = function
  | SO.Var v -> SO.RelMap.find v s.SO.relations
  | SO.Const e -> [[e]]

let terms_to_vars s ts =
  List.map (term_to_var s) ts

let name p is = 
  let rec f xs = match xs with
    | [x] -> string_of_int x
    | x::xs -> string_of_int x ^ "_" ^ f xs
    | [] -> ""
  in
  List.map (sprintf "%s_%d" p) is

let qbf_names_for x arity n =
  let rec lists xs i = match i with
    | 0 -> []
    | n -> xs :: lists xs (i - 1)
  in
  let names = U.n_cartesian_product (lists (U.range 1 n) arity) in
  List.map (name x) names

let so_to_qbf s f =
  let module So2Qbf = Map.Make (struct
    type t = SO.so_var
    let compare = compare
  end) in
  let rec go m = function
    | SO.CRel (r,ts) ->
      begin
        try
          let r' = SO.RelMap.find r s.SO.relations in
          if List.mem r' (terms_to_vars s ts) then Qbf.mk_true ()
          else Qbf.mk_false ()
        with Not_found ->
          let msg = SO.RelMap.fold (fun k _ a -> Printf.sprintf "%s, %s" k a) s.SO.relations "" in
          failwith ("Could not find '" ^ r ^ "' in [" ^ msg ^ "]. (pdzoj)")
      end

    (* This is total bollocks *)
    | SO.QRel (sym,ts) ->
      begin
        try
          let r' = List.map (fun f -> SO.Var f) (So2Qbf.find sym m) in
          if List.mem r' [ts] then Qbf.mk_true ()
          else Qbf.mk_false ()
        with Not_found ->
          let msg = SO.RelMap.fold (fun k _ a -> Printf.sprintf "%s, %s" k a) s.SO.relations "" in
          failwith ("Could not find '" ^ sym ^ "' in [" ^ msg ^ "]. (pdzoj)")
      end
          
    | SO.FoAll (v, f) ->
      begin
        try
          let r  = SO.RelMap.find v s.SO.relations in
          let a = get_arity v r in
          Qbf.mk_and (List.map (fun ai ->
              go (So2Qbf.add v ai m) f
            ) (qbf_names_for v a s.SO.size))
        with Not_found ->
          SO.RelMap.iter (fun k _ -> Printf.printf "%s, " k) s.SO.relations;
          failwith ("Could not find '" ^ v ^ "'. (hnxjb)")
      end

    | SO.FoAny (v, f) ->
      begin
        try
          let r  = SO.RelMap.find v s.SO.relations in
          let a = get_arity v r in
          Qbf.mk_or (List.map (fun ai ->
              go (So2Qbf.add v ai m) f
            ) (qbf_names_for v a s.SO.size))
        with Not_found ->
          failwith ("Could not find '" ^ v ^ "'. (jgpcn)")
      end
            
    | SO.SoAll (v, a, f) ->
      let names = qbf_names_for v a s.SO.size in
      let m = So2Qbf.add v names m in
      Qbf.mk_forall names (go m f)
      
    | SO.SoAny (v, a, f) ->
      let names = qbf_names_for v a s.SO.size in
      let m = So2Qbf.add v names m in
      Qbf.mk_exists names (go m f)
        
    | SO.And fs ->
      Qbf.mk_and (List.map (go m) fs)
    | SO.Or fs ->
      Qbf.mk_or (List.map (go m) fs)
    | SO.Not f ->
      Qbf.mk_not (go m f)
  in
  go So2Qbf.empty f
