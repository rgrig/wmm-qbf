open Printf
open SO
module U = Util
module ArityMap = Map.Make(String)

type rel1 = SO.term -> SO.formula
type rel2 = SO.term -> SO.term -> SO.formula

let add_rel rs (k, r) =
  if RelMap.mem k rs then failwith ("repeated relation symbol " ^ k ^ " (voxdy)");
  RelMap.add k r rs

let rels xs =
  List.fold_left add_rel RelMap.empty xs

let add_specials s =
  let eq = List.map (fun x -> [x; x]) (U.range 1 s.size) in
  { s with relations = add_rel s.relations (eq_rel, (1, eq)) }

let get_arity s r =
  let arity = List.length (List.nth r 0) in
  if not (List.for_all (fun e -> List.length e = arity) r) then
    failwith (Printf.sprintf "inconsistent arity of symbol %s" s);
  arity

let check_arities s f =
  let check_structure sym (a, l) arr_map =
    assert (a = get_arity sym l);
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
  let collect_arities = RelMap.fold (fun k (ar, _) a -> ArityMap.add k ar a) in
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
    with Not_found ->
      (* Print stack trace *)
      Printf.printf "%s\n" (Printexc.get_callstack 100 |> Printexc.raw_backtrace_to_string);
      failwith ("Could not apply relation " ^ (Util.map_join "_" string_of_int cs) ^ ". (sggmh)")
  in

  let mk_fresh_qvars ?(prefix="q") a =
    let xs = Util.range 1 structure.size in
    let xss = Util.repeat a xs in
    let xss = Util.n_cartesian_product xss in
    let add_one acc xs =
      let prefix = Printf.sprintf "%s_%s" prefix (Util.map_join "_" string_of_int xs) in
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
        let _, r' = structure_lookup r in
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

let dump s f =
  let basename = Filename.remove_extension (Config.filename ()) in
  let f_c = open_out (basename ^ ".sol") in
  let s_c = open_out (basename ^ ".str") in
  Printf.fprintf f_c "%s\n" (show_formula f);
  Printf.fprintf s_c "%s\n" (show_structure s);
  close_out f_c;
  close_out s_c

let holds s f =
  dump s f;
  let basename = Filename.remove_extension (Config.filename ()) in
  let o = RunSolver.run_so_solver [|(basename ^ ".sol"); (basename ^ ".str")|] "" in
  Results.parse_answer o


let model_check s f =
  let s = add_specials s in
  if (Config.dump_query ()) then dump s f;
  match Config.use_solver () with
    Some (Config.SolveQbf) ->
    Qbf.holds (so_to_qbf s f)
  | Some (Config.SolveSO) ->
    holds s f
  | None -> failwith "Solver disabled."

let mk_implies prems conclusion =
  Or (conclusion :: List.map (fun p -> Not p) prems)

let mk_eq a b =
  CRel (eq_rel, [a; b])

let subset a b =
  let y = mk_fresh_fv () in
  FoAll (y, mk_implies [QRel (a, [Var y])] (QRel (b, [Var y])))

 
let mk_fresh_reln ?prefix:(prefix="F") () =
  let r_id = mk_fresh_sv ~prefix:prefix () in
  let r i j = QRel (r_id, [i; j]) in
  (r_id, r)

let mk_crel1 id =
  (fun t -> SO.CRel (id, [t]))

let mk_crel2 id =
  (fun t s -> SO.CRel (id, [t; s]))

let mk_qrel1 id =
  let id = SO.S id in
  let mk t = SO.QRel (id, [t]) in
  (id, mk)

let mk_qrel2 id =
  let id = SO.S id in
  let mk t s = SO.QRel (id, [t; s]) in
  (id, mk)

(* Query: is there a better way to represent the empty relation *)
(* i.e. ∀x,y. (x,y) ∉ r *)
let empty_reln r =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (
    x,
    FoAll (
      y,
      Not (r (Var x) (Var y))
    )
  )

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

let iff ps qs =
  And [
    mk_implies ps (And qs)
  ; mk_implies qs (And ps)
  ]

let eq a b =
  And [subset a b; subset b a]

(* ∀x . (x∈a ⇒ x∈n) ∧ (x∈n ⇒ x∈a) *)
let eq_crel a n =
  let x = mk_fresh_fv ~prefix:"eq_crel" () in
  FoAll (
    x,
    And [
       mk_implies [QRel (a, [Var x])] (CRel (n, [Var x])) 
     ; mk_implies [CRel (n, [Var x])] (QRel (a, [Var x]))
     ] 
  )

(* {{{ Combinators for arity-1 relations (aka sets/predicates). *)

let and1 (ps : rel1 list) : rel1 = fun (x : term) ->
  SO.And (List.map (fun p -> p x) ps)

let or1 (ps : rel1 list) : rel1 = fun (x : term) ->
  SO.Or (List.map (fun p -> p x) ps)

let set_intersect = and1
let set_union = or1


(* }}} Combinators for arity-1 relations (aka sets/predicates). *)

let invert r a b = r b a

let sequence r1 r2 x z = 
  let y = mk_fresh_fv () in
  FoAny (y, And [
      r1 x (Var y)
    ; r2 (Var y) z
    ])

let rel_union r1 r2 x y =
  Or [r1 x y; r2 x y]

let rel_nary_of_binary f = function
  | [] -> mk_eq
  | [r] -> r
  | r :: rs -> List.fold_left f r rs

let sequence_n = rel_nary_of_binary sequence
let rel_union_n = rel_nary_of_binary rel_union

let rel_intersect r1 r2 x y =
  And [r1 x y; r2 x y]
    
let rel_subset r1 r2 =
  let x = mk_fresh_fv () in
  let y = mk_fresh_fv () in
  FoAll (
    x,
    FoAll (
      y,
      mk_implies
        [r1 (Var x) (Var y)]
        (r2 (Var x) (Var y))
    )
  )

let rel_eq a b = And [rel_subset a b; rel_subset b a]

(* Bounded reflexive transitive closure, up to n steps *)
let rec r_tc n f a b =
  let x = mk_fresh_fv ~prefix:"r_tc_x" () in
  let step = match n with
      0 -> mk_eq
    | _ -> r_tc (n-1) f
  in
  Or [
    mk_eq a b
  ; FoAny (x, And [f a (Var x); step (Var x) b])
  ]
  
(* Bounded transitive closure *)
(* f+ a b ≜ f a b ∨ (∃x. f a x ∧ f+ x b) *)
let rec tc n f a b =
  let x = mk_fresh_fv ~prefix:"tc_x" () in
  let step = match n with
      1 -> f
    | _ -> tc (n-1) f
  in
  Or [
    f a b
  ; FoAny (x, And [f a (Var x); step (Var x) b])
  ]

let transitive r =
  let a = mk_fresh_fv () in
  let b = mk_fresh_fv () in
  let c = mk_fresh_fv () in
  FoAll (
    a,
    FoAll (
      b,
      FoAll (
        c,
        mk_implies
          [ r (Var a) (Var b)
          ; r (Var b) (Var c)]
          (r (Var a) (Var c))
      )
    )
  )

let irreflexive r = 
  let x = mk_fresh_fv ~prefix:"irrefl_" () in
  FoAll (x, Not (r (Var x) (Var x)))
    
let acyclic e =
  let r_id, r = mk_fresh_reln ~prefix:"acycl_" () in
  SoAny (
    r_id, 2,
    And [
      irreflexive r
    ; rel_subset (sequence r r) r
    ; rel_subset e r
    ]
  )

let total s r =
  let x = mk_fresh_fv ~prefix:"total_" () in
  let y = mk_fresh_fv ~prefix:"total_" () in
  FoAll (x, FoAll (y,
    mk_implies
      [s (Var x); s (Var y)]
      ((rel_union_n [r; invert r; mk_eq]) (Var x) (Var y))))

let eq_crel2 a n =
  let x = mk_fresh_fv ~prefix:"eq_crel2_x" () in
  let y = mk_fresh_fv ~prefix:"eq_crel2_y" () in
  FoAll (
    x,
    FoAll (
      y,
      And [
        mk_implies [QRel (a, [Var x; Var y])] (CRel (n, [Var x; Var y]))
      ; mk_implies [CRel (n, [Var x; Var y])] (QRel (a, [Var x; Var y]))
      ]
    )
  )
    
let rel_minus a b x y =
  And [a x y; Not (b x y)]

let cross a b x y =
  And [a x; b y]
