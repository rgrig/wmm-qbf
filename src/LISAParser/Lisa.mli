type state = MiscParser.state
type program = BellBase.parsedPseudo list list
type constraints =
    (MiscParser.location * MiscParser.run_type) list *
    MiscParser.prop option * MiscParser.constr *
    (string * MiscParser.quantifier) list
type litmus =
  { init : state
  ; threads : int list
  ; program : program
  ; final : constraints }
val read_to_eof : in_channel -> string
val load_litmus : string -> litmus
val print_litmus : litmus -> unit
