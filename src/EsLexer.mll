{
  open Scanf
  open EsParser

  let keyword x =
    let table = Hashtbl.create 53 in
    List.iter (fun (k, v) -> Hashtbl.add table k v)
      [ "conflicts", CONFLICTS
      ; "events", EVENTS
      ; "justifies", JUSTIFIES
      ; "order", ORDER
      ; "reads", READS ];
    try Hashtbl.find table x
    with Not_found -> BADKEYWORD
}

let id = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']*
let ws = [' ' '\t' '\r']+
let num = ['0'-'9']+

rule token = parse
  | ws { token lexbuf }
  | "//" [^ '\n']* { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; NL }
  | num as x { INT (sscanf x "%d" (fun x->x)) }
  | id as x { keyword x }
  | eof { EOF }
  | _ { raise Error }
