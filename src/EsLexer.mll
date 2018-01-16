{
  open Scanf
  open EsParser

  let keyword x =
    let table = Hashtbl.create 53 in
    List.iter (fun (k, v) -> Hashtbl.add table k v)
      [ "conflicts", CONFLICTS
      ; "events", EVENTS
      ; "canExecute", CAN
      ; "mustExecute", MUST
      ; "execution", EXECUTION
      ; "justifies", JUSTIFIES
      ; "labels", LABELS
      ; "order", ORDER
      ; "reads", READS
      ; "sc", SEQUENTIALLY_CONSISTENT
      ; "rel", RELEASE
      ; "acq", ACQUIRE
      ; "consume", CONSUME
      ; "na", NON_ATOMIC
      ; "fence", FENCE
      ; "ext", EXT
      ; "sloc", SLOC];
    try Hashtbl.find table x
    with Not_found -> raise Error
}

let id = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']*
let ws = [' ' '\t' '\r']+
let num = ['0'-'9']+
let quoted_string = '"'[^'"']*'"'

rule token = parse
  | ws { token lexbuf }
  | "//" [^ '\n']* { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; NL }
  | num as x { INT (sscanf x "%d" (fun x->x)) }
  | quoted_string { QUOTED_STRING }
  | id as x { keyword x }
  | eof { EOF }
  | _ { raise Error }
