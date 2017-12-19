open Printf
open SO
module U = Util
module ArityMap = Map.Make(String)

let add_rel rs (k, r) =
  if RelMap.mem k rs then failwith "repeated relation symbol (voxdy)";
  RelMap.add k r rs

let rels xs =
  List.fold_left add_rel RelMap.empty xs

let add_specials s =
  let eq = List.map (fun x -> [x; x]) (U.range 1 s.size) in
  { s with relations = add_rel s.relations (eq_rel, eq) }

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
    | CRel (s, ts) ->
      let a = List.length ts in
      begin
        try
          let a' = ArityMap.find s arr_map in
          assert (a = a')
        with
          Not_found ->
          failwith (Printf.sprintf "symbol %s not defined in SO structure" (show_rel_sym s))
        | Assert_failure _ ->
          failwith (Printf.sprintf "symbol %s applied with inconsistent arity" (show_rel_sym s))
      end;
      arr_map
    | QRel (S s, ts) ->
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
          failwith (Printf.sprintf "symbol %s applied with inconsistent arity" (show_rel_sym s))
      end

    | FoAny (_, f) | FoAll (_, f) ->
      check_formula f arr_map

    (* When a variable is quantified: shadow it's previous definition in the arity map *)
    | SoAny (S s, a, f) | SoAll (S s, a, f) ->
      check_formula f (ArityMap.add s a arr_map)

    | And fs | Or fs ->
      List.fold_right check_formula fs arr_map
    | Not f ->
      check_formula f arr_map

  in
  ignore @@ RelMap.fold check_structure s.relations ArityMap.empty;

  (* Collect the arities of all of the constant relation symbols *)
  let collect_arities = RelMap.fold (fun k v a -> ArityMap.add k (get_arity k v) a) in
  ignore @@ check_formula f (collect_arities s.relations ArityMap.empty)

let check_inv s f =
  check_arities s f (*
  check_elem_bounds s f*)

module ElementListMap = Map.Make (struct
    type t = element list
    let compare = compare
  end)

module SoVarMap = Util.StringMap
module FoVarMap = Util.StringMap

let so_to_qbf structure formula =
  let module ByIdx = ElementListMap in
  let module FoEnv = FoVarMap in
  let module SoEnv = SoVarMap in
  let fo_subst env = (function
      | Var (F v) -> (try FoEnv.find v env with Not_found -> Var (F v))
      | t -> t) in
  let from_const = (function
      | Const c -> c
      | Var (F v) -> failwith (Printf.sprintf "'%s' appears to be free in the formula. (tlegz)" v)) in

  let structure_lookup r =
    try
      RelMap.find r structure.relations
    with Not_found ->
      let keys = List.map fst (RelMap.bindings structure.relations) in
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
    let xs = Util.range 1 structure.size in
    let xss = Util.repeat a xs in
    let xss = Util.n_cartesian_product xss in
    let add_one acc xs =
      ByIdx.add xs (Qbf.fresh_var ~prefix ()) acc in
    List.fold_left add_one ByIdx.empty xss in
  let qvars_list qvars =
    List.map snd (ByIdx.bindings qvars) in
  
  let rec fo_qs so_env fo_env v f =
    let add_sub c = FoEnv.add v (Const c) fo_env in
    let go' fo_env' = go so_env fo_env' f in
    let xs = Util.range 1 structure.size in
    let fo_envs = List.map add_sub xs in
    List.map go' fo_envs
  and go so_env fo_env  = function
      | CRel (r,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        let r' = structure_lookup r in
        if List.mem cs r' then Qbf.mk_true () else Qbf.mk_false ()

      | QRel (S sym,ts) ->
        let ts = List.map (fo_subst fo_env) ts in
        let cs = List.map from_const ts in
        let qvars = so_lookup sym so_env in
        Qbf.mk_var (byidx_lookup cs qvars)

      | FoAll (F v, f) ->
        Qbf.mk_and (fo_qs so_env fo_env v f)
      | FoAny (F v, f) ->
        Qbf.mk_or (fo_qs so_env fo_env v f)

      | SoAll (S v, a, f) ->
        let qvars = mk_fresh_qvars ~prefix:v a in
        let so_env' = SoEnv.add v qvars so_env in
        let q = go so_env' fo_env f in
        Qbf.mk_forall (qvars_list qvars) q
      | SoAny (S v, a, f) ->
        let qvars = mk_fresh_qvars ~prefix:v a in
        let so_env' = SoEnv.add v qvars so_env in
        let q = go so_env' fo_env f in
        Qbf.mk_exists (qvars_list qvars) q

      | And fs ->
        Qbf.mk_and (List.map (go so_env fo_env) fs)
      | Or fs ->
        Qbf.mk_or (List.map (go so_env fo_env) fs)
      | Not f ->
        Qbf.mk_not (go so_env fo_env f)
  in
  go SoEnv.empty FoEnv.empty formula

let model_check opts s f =
  let s = add_specials s in
  let dump_qbf,dump_query,debug = opts in
  if dump_query then (
      pp_formula Format.std_formatter f;
      Printf.printf "\n";
      pp_structure Format.std_formatter s;
    );
  let q = so_to_qbf s f in
  match Qbf.holds q with
    Some x -> x
  | None -> false

let mk_implies prems conclusion =
  Or (conclusion :: List.map (fun p -> Not p) prems)

let mk_eq a b =
  CRel (eq_rel, [a; b])
    
let subset a b =
  let y = mk_fresh_fv () in
  FoAll (y, mk_implies [QRel (a, [Var y])] (QRel (b, [Var y])))

(* z = a ∩ b *)
let intersect z a b =
  let v = mk_fresh_fv () in
  FoAll (
    v,
    And [
      mk_implies
        [ QRel (a, [Var v])
        ; QRel (b, [Var v])
        ]
        (QRel (z, [Var v]))
    ; mk_implies
        [ QRel (z, [Var v]) ]
        (And [
            QRel (a, [Var v])
          ; QRel (b, [Var v])
          ]
        )
    ]
  )

(* z = a ∪ b *)
let union z a b =
  let v = mk_fresh_fv () in
  FoAll (
    v,
    And [
      mk_implies
        [ Or 
            [ QRel (a, [Var v])
            ; QRel (b, [Var v])
            ]
        ]
        (QRel (z, [Var v]))
    ; mk_implies
        [ QRel (z, [Var v]) ]
        (Or [
            QRel (a, [Var v])
          ; QRel (b, [Var v])
          ]
        )
    ]
  )

  
let eq a b =
  And [subset a b; subset b a]

