open Results
    
let ans = Results.parse_answer (Std.input_all stdin);;
Printf.printf "%b\n" ans
