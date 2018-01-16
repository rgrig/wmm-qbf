open OUnit
open JRSO
open SO
open SoOps
    
let jctc1 = SO.{
    size = 9;
    relations = rels [
        ("target", (1, [[1]; [2]; [3]; [6]; [7]]));
        ("order", (2, [[6;7]; [1;8]; [1;6]; [1;4]; [1;2]; [8;9]; [2;3]; [4;5]]));
        ("justifies", (2, [[7;2]; [1;4]; [9;4]; [3;6]; [5;6]; [1;8]]));
        ("reads", (1, [[2]; [4]; [6]; [8]]));
        ("empty_set", (1, []));
        ("conflict", (2, [[6;8]; [2;4]]))
      ];
  }

let jctc1_subset_of_target = "subset of target" >:: (fun () ->
    let s = {jctc1 with relations = add_rel jctc1.relations ("foo", (1, [[1]]))} in
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
    let s = {jctc1 with relations = add_rel jctc1.relations ("foo", (1, [[4]]))} in
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


let jctc1_wx1_not_justified = "Wx1 not justified by empty in jctc1" >:: (fun () ->
    let s = { jctc1 with relations = add_rel jctc1.relations ("interesting_read", (1, [[2]])) } in
    let x = mk_fresh_sv () in
    let y = mk_fresh_sv () in
    let f =
      SoAny (x, 1,
             SoAny (y, 1,
                    And [
                      eq_crel x "interesting_read"
                    ; eq_crel y "empty_set"
                    ; Not (justify y x)
                    ]
                   )
            )
    in
    OUnit.assert_bool "models" (SoOps.model_check s f)
  )

let tests = "jrso2_tests" >::: [
    jctc1_subset_of_target
  ; jctc1_not_subset_of_target
  ; jctc1_wx1_not_justified
  ]
