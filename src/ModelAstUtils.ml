open ModelAst

let union_map f =
  let g acc x = Util.StringSet.union acc (f x) in
  List.fold_left g Util.StringSet.empty

(* Free variables *)
let bound_pat = function
  | Pvar x -> Util.StringSet.singleton x
  | Ptuple xs -> Util.StringSet.of_list xs

let bound_bds bds =
  let f acc (pat, _) = Util.StringSet.union acc (bound_pat pat) in
  List.fold_left f Util.StringSet.empty bds

let rec free = function
  | Konst _ | Tag _ -> Util.StringSet.empty
  | Var x -> Util.StringSet.singleton x
  | Op1 (_,e)
    -> free e
  | Op (_,es)|ExplicitSet (es) -> frees es
  | App (e1,e2) ->
      Util.StringSet.union (free e1) (free e2)
  | Bind (bds,e) ->
      let xs = bound_bds bds in
      Util.StringSet.union
        (bindings bds)
        (Util.StringSet.diff (free e) xs)
  | BindRec (bds,e) ->
      let xs = bound_bds bds in
      Util.StringSet.diff
        (Util.StringSet.union (free e) (bindings bds))
        xs
  | Fun (_,_,_,fs) -> fs
  | Match (e,cls,eo) ->
      let e = free e
      and cls = clauses cls
      and eo = match eo with
      | None -> Util.StringSet.empty
      | Some e -> free e in
      Util.StringSet.union (Util.StringSet.union e eo) cls
  | MatchSet (e1,e2,cl) ->
      let e1 = free e1
      and e2 = free e2
      and cl = free_cl cl in
      let ( + ) = Util.StringSet.union in
      e1 + e2 + cl
  | Try (e1,e2) ->
      Util.StringSet.union (free e1) (free e2)
  | If (cond,ifso,ifnot) ->
      Util.StringSet.union (free_cond cond)
        (Util.StringSet.union (free ifso) (free ifnot))

and free_cl = function
  | EltRem (x,xs,e) ->
      Util.StringSet.remove x (Util.StringSet.remove xs (free e))
  | PreEltPost (xs1,x,xs2,e) ->
      Util.StringSet.diff (free e) (Util.StringSet.of_list [xs1;x;xs2])

and free_cond c = match c with
| Eq (e1,e2) -> Util.StringSet.union (free e1) (free e2)
| Subset (e1,e2) -> Util.StringSet.union (free e1) (free e2)

and frees es = union_map free es

and bindings bds = union_map (fun (_,e) -> free e) bds

and clauses bds = union_map (fun (_,e) -> free e) bds

let free_body xs e =
  Util.StringSet.diff (free e) (Util.StringSet.of_list xs)
