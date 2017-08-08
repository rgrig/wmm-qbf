type const

type set =
  | InputSet of string
  | QuantSet of string

type relation =
  | InputRel of string
  | QuantRel of string
       
type t =
  { data : EventStructure.t
  ; relation : set list
  ; sets : relation list
  ; constraints : const list
  }
