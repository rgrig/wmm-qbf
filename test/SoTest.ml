open OUnit


let verbose = ref false

(* TODO

(* Check the invariants of an SO structure with a simple and well
formed relation `foo' *)
let t1 = "check_arity_pass" >:: (fun () ->
  let s =
    { SO.size = 3
    ; relations = SoOps.rels [("foo", [[1];[2]])] } in
  let f = SO.CRel (("foo", 1), [SO.Const 1]) in
  SoOps.check_inv s f
)

(* Check the invarients of an SO structure which contains a poorly
formed relation `foo' *)
let t2 = "check_arity_fail" >:: (fun () ->
  let s =
    { SO.size = 3
    ; relations = SoOps.rels [(("foo", 1), [[1];[1;2]])] } in
  let f = SO.CRel (("foo", 1), [SO.Const 1]) in
  OUnit.assert_raises
    (Failure "inconsistent arity of symbol foo")
    (fun () -> SoOps.check_inv s f)
  )

let t3 = "check_misapplied_pass" >:: (fun () ->
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [(("foo", 1), [[1];[1]])] } in
    let f =
      SO.SoAll (("bar", 2), (SO.QRel (("bar", 2), [SO.Const 1; SO.Const 2])))
    in
    SoOps.check_inv s f
  )
       
let t4 = "check_misapplied_fail" >:: (fun () ->
    let s =
      { SO.size = 3
      ; relations = SoOps.rels [(("foo", 1), [[1];[1]])] } in
    let f =
      SO.SoAll (("bar", 2), (SO.QRel (("bar", 2), [SO.Const 1])))
    in
    OUnit.assert_raises
      (Failure "symbol (\"bar\", 2) applied with inconsistent arity")
      (fun () -> SoOps.check_inv s f)
  )

let so_structure_tests = "so" >::: [t1;t2;t3; t4]

let options = Arg.align [("--verbose", Arg.Set verbose, "run with verbose output")];;

let _ = Arg.parse options (fun _ -> ()) ""

let () =
  ignore @@ run_test_tt so_structure_tests ~verbose:(!verbose);
  SO.pp_formula
    Format.std_formatter
    (SO.SoAll (("bar", 2),
               (SO.Or [
                    SO.QRel (("bar", 1), [SO.Const 1])
                  ; SO.QRel (("baz", 1), [SO.Const 2])
                  ]
               )
              )
    )
*)
