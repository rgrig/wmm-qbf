let _ = match LISALexer.lex (Lexing.from_string "-10") with
| LISAParser.INT value -> Printf.printf "Int %d\n" value
| _ -> Printf.printf "Broken\n"
