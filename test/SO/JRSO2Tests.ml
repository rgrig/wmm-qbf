open OUnit
open JRSO2 
open SO
open SoOps
    
let jctc1 = SO.{
    size = 9;
    relations = rels [
        ("target", [[1]; [2]; [3]; [6]; [7]]);
        ("order", [[6;7]; [1;8]; [1;6]; [1;4]; [1;2]; [8;9]; [2;3]; [4;5]]);
        ("justifies", [[7;2]; [1;4]; [9;4]; [3;6]; [5;6]; [1;8]]);
        ("empty_set", [[]]);
        ("conflict", [[6;8]; [2;4]])
      ];
  }

let jctc1_subset_of_target = "subset of target" >:: (fun () ->
    let s = {jctc1 with relations = add_rel jctc1.relations ("foo", [[1]])} in
    let x = mk_fresh_sv () in
    let y = mk_fresh_sv () in
    let f =
      SoAny
        (x, 1,
         SoAny
         (y, 1, 
          And [
            eq_crel x "target"
          ; eq_crel y "foo"
          ; subset y x
          ; Not (subset x y)
          ]
         )
        )
    in
    OUnit.assert_bool "models" (SoOps.model_check s f)
  )

let jctc1_not_subset_of_target = "not subset of target" >:: (fun () ->
    let s = {jctc1 with relations = add_rel jctc1.relations ("foo", [[4]])} in
    let x = mk_fresh_sv () in
    let y = mk_fresh_sv () in
    let f =
      SoAny
        (x, 1,
         SoAny
         (y, 1, 
          And [
            eq_crel x "target"
          ; eq_crel y "foo"
          ; Not (subset y x)
          ]
         )
        )
    in
    OUnit.assert_bool "models" (SoOps.model_check s f)
  )




let tests = "jrso2_tests" >::: [
    jctc1_subset_of_target
  ; jctc1_not_subset_of_target
  ]