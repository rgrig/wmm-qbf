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

let name p is = (*
  let rec f xs = match xs with
    | [x] -> string_of_int x
    | x::xs -> string_of_int x ^ "_" ^ f xs
    | [] -> ""
  in*)
  List.map (sprintf "%s_%d" p) is

let qbf_names_for x arity n =
  let rec lists xs i = match i with
    | 0 -> []
    | n -> xs :: lists xs (i - 1)
  in
  let names = U.n_cartesian_product (lists (U.range 1 n) arity) in
  List.map (name x) names

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
  let so_lookup r env =
    try SoEnv.find r env
    with Not_found -> failwith "TODO: nice error (ikgsp)" in
  let byidx_lookup cs qvars =
    try ByIdx.find cs qvars
    with Not_found -> failwith "TODO: nice error (sggmh)" in
  let mk_fresh_qvars ~prefix a =
    let xs = Util.range 1 structure.SO.size in
    let xss = Util.repeat a xs in
    let xss = Util.n_cartesian_product xss in
    let add_one acc xs =
      ByIdx.add xs (Qbf.fresh_var ~prefix ()) acc in
    List.fold_left add_one ByIdx.empty xss in
  let qvars_list qvars =
    List.map snd (ByIdx.bindings qvars) in
  let rec go so_env fo_env  = SO.(function
    | CRel (r,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        (try
          let r' = RelMap.find r structure.relations in
          if List.mem cs r' then Qbf.mk_true () else Qbf.mk_false ()
        with Not_found ->
          let msg = RelMap.fold (fun k _ a -> Printf.sprintf "%s, %s" k a) structure.relations "" in
          failwith ("Could not find '" ^ r ^ "' in [" ^ msg ^ "]. (pdzoj)"))
    | QRel (sym,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        let qvars = so_lookup sym so_env in
        Qbf.mk_var (byidx_lookup cs qvars)
    | FoAll (v, f) ->
        let add_sub c = FoEnv.add v (Const c) fo_env in
        let go' fo_env' = go so_env fo_env' f in

        let xs = Util.range 1 structure.size in
        let fo_envs = List.map add_sub xs in
        let qs = List.map go' fo_envs in
        Qbf.mk_and qs
    | FoAny (v, f) -> (* TODO: maybe refactor *)
        let add_sub c = FoEnv.add v (Const c) fo_env in
        let go' fo_env' = go so_env fo_env' f in

        let xs = Util.range 1 structure.size in
        let fo_envs = List.map add_sub xs in
        let qs = List.map go' fo_envs in
        Qbf.mk_or qs
    | SoAll (v, a, f) ->
        let qvars = mk_fresh_qvars ~prefix:v a in
        let so_env' = SoEnv.add v qvars so_env in
        let q = go so_env' fo_env f in
        Qbf.mk_forall (qvars_list qvars) q

(*
    (* This is total bollocks *)

    | SO.SoAll (v, a, f) ->
      (*let names = qbf_names_for v a s.SO.size in
      let m = So2Qbf.add v names m in
      Qbf.mk_forall names (go m f)*)
      Qbf.mk_false ()

    | SO.SoAny (v, a, f) ->
      (*let names = qbf_names_for v a s.SO.size in
      let m = So2Qbf.add v names m in
      Qbf.mk_exists names (go m f)*)
      Qbf.mk_false ()

    | SO.And fs ->
      Qbf.mk_and (List.map (go m) fs)
    | SO.Or fs ->
      Qbf.mk_or (List.map (go m) fs)
    | SO.Not f ->
      Qbf.mk_not (go m f)
*)
  ) in
  go SoEnv.empty FoEnv.empty formula


let mk_implies prems conclusion =
  SO.Or (conclusion :: List.map (fun p -> SO.Not p) prems)

let mk_eq a b =
  SO.CRel (SO.eq_rel, [a; b])
