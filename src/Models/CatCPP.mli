(* TODO(rgrig): Add comments. *)
val do_decide : Config.worker
val na_do_decide : Config.worker

val simple_do_decide : Config.worker
  (** This function implements the RC11 memory model but without RMW and without
   fences. *)
