type event = int
type set = event list
type relation = (event * event) list

type t =
  { wmm_events : int
  ; wmm_justifies : relation
  ; wmm_conflicts : relation
  ; wmm_order : relation
  ; wmm_execution : set }
