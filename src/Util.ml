open Printf
module B = BatList
module StringSet = Set.Make (String)


exception Parsing_failed of string
exception Runtime_error of string

let n_cartesian_product = B.n_cartesian_product

let parse filename f parser tokeniser error_t =
  let lexbuf = Lexing.from_channel f in
  try
    let r = parser tokeniser lexbuf in
    close_in_noerr f;
    r
  with
    | error_t ->
        (match Lexing.lexeme_start_p lexbuf with
        { Lexing.pos_lnum=line; Lexing.pos_bol=c0;
          Lexing.pos_fname=_; Lexing.pos_cnum=c1} ->
            let msg = sprintf "%s:%d:%d: parse error" filename line (c1-c0+1) in
            raise (Parsing_failed msg))


let range i k =
  let rec loop xs k = if k < i then xs else loop (k :: xs) (k - 1) in
  loop [] k

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

let maybe a f =
  match a with
    Some a' -> f a'
  | None -> ()

let map_concat c f ts =
  String.concat c (List.map f ts)
