(** Simple imperative union-find data structure *)

type 'a t = { mutable rank : int; mutable parent : 'a t; data : 'a; }
val make : 'a -> 'a t
val find : 'a t -> 'a t
val union : 'a t -> 'a t -> unit
val data : 'a t -> 'a
val equal : 'a -> 'a -> bool
