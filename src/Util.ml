open Printf
module B = BatList
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

exception Parsing_failed of string
exception Runtime_error of string

let n_cartesian_product = B.n_cartesian_product

(* returns [i,...,k] *)
let range i k =
  let rec loop xs k = if k < i then xs else loop (k :: xs) (k - 1) in
  loop [] k

let rec repeat n x =
  if n == 0 then [] else x :: repeat (n-1) x

let option d f = function
  | None -> d
  | Some x -> f x

let map_option f = function
  | None -> None
  | Some x -> Some (f x)

let id x = x

let flip f x y = f y x

let rec hp_list_sep sep hp_x f = function
  | [] -> ()
  | [x] -> hp_x f x
  | x :: ((_ :: _) as xs) ->
      fprintf f (format_of_string "%a%s%a") hp_x x sep (hp_list_sep sep hp_x) xs

let hp_list hp_x = hp_list_sep "" hp_x

let hp_int f x = fprintf f "%d" x

let hp_string f x = fprintf f "%s" x

(* TODO: either use same type as Haskell, or rename; maybe_unit? maybe_do? *)
let maybe a f =
  match a with
    Some a' -> f a'
  | None -> ()

let map_join c f ts =
  String.concat c (List.map f ts)

let on_channel (filename : string) (f : in_channel -> 'a) : 'a option =
  let ch = (try Some (open_in filename) with Sys_error _ -> None) in
  let result = (match ch with Some x -> Some (f x) | None -> None) in
  (match ch with Some x -> close_in_noerr x | _ -> ());
  result

let from_some = function
  | None -> failwith "INTERNAL: expected Some"
  | Some x -> x
