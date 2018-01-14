type init = MiscParser.state
type ast = BellBase.parsedPseudo list list
type constraints =
    (MiscParser.location * MiscParser.run_type) list *
    MiscParser.prop option * MiscParser.constr *
    (string * MiscParser.quantifier) list
val read_to_eof : in_channel -> string
val load_litmus : string -> init * int list * ast * constraints
val print_litmus : init * int list * ast * constraints -> unit
