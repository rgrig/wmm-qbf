{
  open Scanf
  open WmmParser

  let keyword =
    let table = Hashtbl.create 53 in
    List.iter (fun (k, v) -> Hashtbl.add table k v)
      [ "conflicts", CONFLICTS
      ; "events", EVENTS
      ; "executions", EXECUTIONS
      ; "justifies", JUSTIFIES
      ; "order", ORDER ];
    Hashtbl.find table
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
