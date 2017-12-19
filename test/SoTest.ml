open OUnit


let verbose = ref false



(* Check the invariants of an SO structure with a simple and well
   formed relation `foo' *)
let t1 = "check_arity_pass" >:: (fun () ->
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[2]])] } in
    let f = SO.CRel ("foo", [SO.Const 1]) in
    SoOps.check_inv s f
  )

(* Check the invarients of an SO structure which contains a poorly
   formed relation `foo' *)
let t2 = "check_arity_fail" >:: (fun () ->
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[1;2]])] } in
    let f = SO.CRel ("foo", [SO.Const 1]) in
    OUnit.assert_raises
      (Failure "inconsistent arity of symbol foo")
      (fun () -> SoOps.check_inv s f)
  )

let t3 = "check_misapplied_pass" >:: (fun () ->
    let bar = SO.mk_fresh_sv () in
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[1]])] } in
    let f =
      SO.SoAll (bar, 2, (SO.QRel (bar, [SO.Const 1; SO.Const 2])))
    in
    SoOps.check_inv s f
  )

let t4 = "check_misapplied_fail" >:: (fun () ->
    let bar = SO.mk_fresh_sv ~prefix:"bar" () in
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[1]])] } in
    let f =
      SO.SoAll (bar, 2, (SO.QRel (bar, [SO.Const 1])))
    in
    OUnit.assert_raises
      (Failure "symbol \"bar2\" applied with inconsistent arity")
      (fun () -> SoOps.check_inv s f)
  )

let check s f =
  let s = SoOps.add_specials s in
  let q = SoOps.so_to_qbf s f in
  match Qbf.holds q with
    Some x -> x
  | None -> false

let t5 = "simple so logic model" >:: (fun () ->
    let s = { SO.size = 3; SO.relations = SoOps.rels [("baz", [[1]])] } in
    let r = SO.mk_fresh_sv () in
    let x = SO.mk_fresh_fv () in
    let f = SO.SoAny (r, 1, SO.FoAny (x, SO.QRel (r, [SO.Var x]))) in
    OUnit.assert_bool "models" (check s f)
  )

(* ∀X . X ⊆ X ∧ X ⊆ X *)
let so_eq_test = "simple equality test" >:: (fun () ->
    let s = { SO.size = 10; SO.relations = SoOps.rels [] } in
    let r = SO.mk_fresh_sv () in
    let f = SO.SoAll (r, 1, SoOps.eq r r) in
    OUnit.assert_bool "models" (check s f)
  )

let id_reln_test = "identity relation test" >:: (fun () ->
    let s = { SO.size = 10; SO.relations = SoOps.rels [] } in
    let r = SO.mk_fresh_fv () in
    let f = SO.FoAll (r, (SoOps.mk_eq (SO.Var r) (SO.Var r))) in
    OUnit.assert_bool "models" (check s f)
  )

(* ∀R. ∀R'. ∀Z . Z = R ∩ R' → (Z ⊆ R ∧ Z ⊆ R') *)
let intersect_subset = "intersection produces subset" >:: (fun () ->
    let s = { SO.size = 10; SO.relations = SoOps.rels [] } in
    let r = SO.mk_fresh_sv () in
    let r' = SO.mk_fresh_sv () in
    let z = SO.mk_fresh_sv () in
    let f = SO.SoAll (
        r, 1,
        SO.SoAll (
          r', 1,
          SO.SoAll (
            z, 1,
            SoOps.mk_implies
              [SoOps.intersect z r r']
              (SO.And [
                  SoOps.subset z r
                ; SoOps.subset z r'
                ]
              )
          )
        )
      )
    in
    OUnit.assert_bool "models" (check s f)
  )

let so_structure_tests = "so_structure" >::: [t1;t2;t3;t4;t5]
let so_formula_tests = "so_formula" >::: [so_eq_test; id_reln_test; intersect_subset]

let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let () =
  let _ = run_test_tt so_structure_tests ~verbose:(!verbose) in
  let _ = run_test_tt so_formula_tests  ~verbose:(!verbose) in
  ()
