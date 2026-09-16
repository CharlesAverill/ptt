(** Error monad *)

type ('a, 'e) t = ('a, 'e) result

let return (x : 'a) : ('a, 'e) t = Ok x

let bind (m : ('a, 'e) t) (f : 'a -> ('b, 'e) t) : ('b, 'e) t =
  match m with Ok x -> f x | Error e -> Error e

let map (f : 'a -> 'b) (m : ('a, 'e) t) : ('b, 'e) t =
  match m with Ok x -> Ok (f x) | Error e -> Error e

let ( let* ) = bind
let ( let+ ) m f = map f m

let ( and* ) m1 m2 =
  match (m1, m2) with
  | Ok x, Ok y -> Ok (x, y)
  | Error e, _ | _, Error e -> Error e

let fail (e : 'e) : ('a, 'e) t = Error e
