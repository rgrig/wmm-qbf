val debug : bool ref
val translate :
  Lisa.litmus
  -> int -> int (* value range *)
  -> EventStructure.t * EventStructure.set list
