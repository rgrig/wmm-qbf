open Printf
module U = Util
module ArityMap = Map.Make(String)

let add_rel rs (k, r) =
  if SO.RelMap.mem k rs then failwith "repeated relation symbol (voxdy)";
  SO.RelMap.add k r rs

let rels xs =
  List.fold_left add_rel SO.RelMap.empty xs

let add_specials s =
  let eq = List.map (fun x -> [x; x]) (U.range 1 s.SO.size) in
  SO.{ s with relations = add_rel s.relations (eq_rel, eq) }

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

module ElementListMap = Map.Make (struct
    type t = SO.element list
    let compare = compare
  end)

module SoVarMap = Util.StringMap
module FoVarMap = Util.StringMap

let so_to_qbf structure formula =
  let module ByIdx = ElementListMap in
  let module FoEnv = FoVarMap in
  let module SoEnv = SoVarMap in
  let fo_subst env = SO.(function
      | Var v -> (try FoEnv.find v env with Not_found -> Var v)
      | t -> t) in
  let from_const = SO.(function
      | Const c -> c
      | _ -> failwith "INTERNAL (tlegz)") in

  let structure_lookup r =
    try
      SO.RelMap.find r structure.SO.relations
    with Not_found ->
      let keys = List.map fst (SO.RelMap.bindings structure.SO.relations) in
      let msg = String.concat "," keys in
      failwith ("Could not find '" ^ r ^ "' in [" ^ msg ^ "]. (pdzoj)") in
  let so_lookup sym env =
    try SoEnv.find sym env
    with Not_found ->
      failwith ("Could not find '" ^ sym ^ "'. Did you miss a quantifier? (pjmnt)")
  in
  let byidx_lookup cs qvars =
    try ByIdx.find cs qvars
    with Not_found -> failwith "Could not apply relation. (sggmh)"
  in
  
  let mk_fresh_qvars ?(prefix="q") a =
    let xs = Util.range 1 structure.SO.size in
    let xss = Util.repeat a xs in
    let xss = Util.n_cartesian_product xss in
    let add_one acc xs =
      ByIdx.add xs (Qbf.fresh_var ~prefix ()) acc in
    List.fold_left add_one ByIdx.empty xss in
  let qvars_list qvars =
    List.map snd (ByIdx.bindings qvars) in
  
  let rec fo_qs so_env fo_env v f =
    let add_sub c = FoEnv.add v (SO.Const c) fo_env in
    let go' fo_env' = go so_env fo_env' f in
    let xs = Util.range 1 structure.SO.size in
    let fo_envs = List.map add_sub xs in
    List.map go' fo_envs
  and go so_env fo_env  = SO.(function
      | CRel (r,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        let r' = structure_lookup r in
        if List.mem cs r' then Qbf.mk_true () else Qbf.mk_false ()

      | QRel (sym,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        let qvars = so_lookup sym so_env in
        Qbf.mk_var (byidx_lookup cs qvars)

      | FoAll (v, f) ->
        Qbf.mk_and (fo_qs so_env fo_env v f)
      | FoAny (v, f) ->
        Qbf.mk_or (fo_qs so_env fo_env v f)

      | SoAll (v, a, f) ->
        let qvars = mk_fresh_qvars ~prefix:v a in
        let so_env' = SoEnv.add v qvars so_env in
        let q = go so_env' fo_env f in
        Qbf.mk_forall (qvars_list qvars) q
      | SoAny (v, a, f) ->
        let qvars = mk_fresh_qvars ~prefix:v a in
        let so_env' = SoEnv.add v qvars so_env in
        let q = go so_env' fo_env f in
        Qbf.mk_exists (qvars_list qvars) q

      | SO.And fs ->
        Qbf.mk_and (List.map (go so_env fo_env) fs)
      | SO.Or fs ->
        Qbf.mk_or (List.map (go so_env fo_env) fs)
      | SO.Not f ->
        Qbf.mk_not (go so_env fo_env f)
    ) in
  go SoEnv.empty FoEnv.empty formula


let mk_implies prems conclusion =
  SO.Or (conclusion :: List.map (fun p -> SO.Not p) prems)

let mk_eq a b =
  SO.CRel (SO.eq_rel, [a; b])
