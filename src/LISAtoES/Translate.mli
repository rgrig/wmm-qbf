val debug : bool ref
val translate :
  Lisa.litmus
  -> int -> int (* value range *)
  -> EventStructure.t * EventStructure.set list * (EventStructure.event * string) list
