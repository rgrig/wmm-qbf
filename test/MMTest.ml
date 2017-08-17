open OUnit

open EventStructure
open MM
   
let tests = [MM.test_sizeof; MM.test_name; MM.test_var;
             MM.test_subset; MM.test_subset2; MM.test_subset_r;
             MM.test_flip; MM.test_equal; MM.test_union]
          
