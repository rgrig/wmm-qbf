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
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[1]])] } in
    let f =
      SO.SoAll ("bar", 2, (SO.QRel ("bar", [SO.Const 1; SO.Const 2])))
    in
    SoOps.check_inv s f
  )
       
let t4 = "check_misapplied_fail" >:: (fun () ->
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [("foo", [[1];[1]])] } in
    let f =
      SO.SoAll ("bar", 2, (SO.QRel ("bar", [SO.Const 1])))
    in
    OUnit.assert_raises
      (Failure "symbol \"bar\" applied with inconsistent arity")
      (fun () -> SoOps.check_inv s f)
  )

let t5 = "show formula" >:: (fun () ->
    let s = SO.show_formula (SO.SoAll ("bar", 1,
               (SO.Or [
                   SO.QRel ("bar", [SO.Const 1])
                 ; SO.QRel ("baz", [SO.Const 2])
                 ]
               )
              )
    )
    in
    OUnit.assert_equal s "∀bar . (bar(1) ∧ baz(2))"
  )

let t6 = "simple so logic model" >:: (fun () ->
    let s = { SO.size = 3; SO.relations = SoOps.rels [("baz", [[1]])] } in
    let f = SO.SoAny ("bar", 1, SO.QRel ("bar", [SO.Const 1])) in
    Printf.printf "\nFormula : %s\n" (SO.show_formula f);
    
    let q = SoOps.so_to_qbf s f in
    Printf.printf "Qbf : %s\n" (Qbf.show q);
    
    let r = match Qbf.holds q (false, false, true) with
        Some x -> x
      | None -> false
    in
    OUnit.assert_bool "models" r
  )

let so_structure_tests = "so" >::: [t1;t2;t3;t4;t5;t6]

let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let () =
  let _ = run_test_tt so_structure_tests ~verbose:(!verbose) in
  ()
