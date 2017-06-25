type 'a t

exception Empty

val empty : 'a t
val push : 'a -> 'a t -> 'a t
val pop : 'a t -> 'a * 'a t
