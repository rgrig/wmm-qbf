val debug : bool ref
val translate :
  MiscParser.state (* initial state *)
  -> BellBase.parsedPseudo list list (* program *)
  -> int -> int (* value range *)
  -> EventStructure.t
