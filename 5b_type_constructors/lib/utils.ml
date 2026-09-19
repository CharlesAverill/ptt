(** Utilities *)

(** Wrap [s] in parentheses if it contains a space *)
let paren (s : string) : string =
  if String.contains s ' ' then "(" ^ s ^ ")" else s
