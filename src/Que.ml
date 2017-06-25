type 'a t = 'a list * 'a list

exception Empty

let empty = ([], [])
let push z (xs, ys) = (xs, z :: ys)
let rec pop = function
  | [], [] -> raise Empty
  | [], ys -> pop (List.rev ys, [])
  | x :: xs, ys -> (x, (xs, ys))
