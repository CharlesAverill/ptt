(** Parser driver *)

open Logging
open Syntax
open Lexer
open Parser
open Typechecker
open Eval
open Monads

(** Parse a [string] into a [sterm], raising a [ParseError] if malformed *)
let parse_sterm (s : string) : sterm =
  let lexbuf = Lexing.from_string s in
  try
    match menhir_parse Lexer.read lexbuf with
    | Ok t -> t
    | Error e -> raise (ParseError e)
  with
  | Error -> raise (ParseError "syntax error")
  | SyntaxError m -> raise (ParseError m)

(** Parse and typecheck a [string] into a type-erased [term]*)
let parse (s : string) : typed_term =
  match typecheck (parse_sterm s) with
  | Ok t -> t
  | Error s -> raise (TypeError s)

(** Read the next [;;]-terminated term from [lexbuf], typecheck and erase it, or
    [None] once there is nothing left to read. Raises [ParseError] if the next
    phrase is malformed, or [TypeError] if it is ill-typed *)
let parse_phrase (lexbuf : Lexing.lexbuf) : typed_term option =
  let st =
    try
      match menhir_parse_phrase Lexer.read lexbuf with
      | Ok t -> t
      | Error e -> raise (ParseError e)
    with
    | Error -> raise (ParseError "syntax error")
    | SyntaxError m -> raise (ParseError m)
  in
  match st with
  | None -> None
  | Some st' -> (
      match typecheck st' with
      | Ok st'' -> Some st''
      | Error e -> raise (TypeError e))

(** Synchronize the lexer after reading a bad term *)
let synchronize (lexbuf : Lexing.lexbuf) : unit =
  let rec loop () =
    match Lexer.read lexbuf with
    | DSEMI | EOF -> ()
    | _ -> loop ()
    | exception SyntaxError _ -> loop ()
  in
  loop ()

(** General execution loop *)
let rec loop (lexbuf : Lexing.lexbuf) (prompt : unit -> unit) : unit =
  prompt ();
  match parse_phrase lexbuf with
  | None -> ()
  | Some (term, typ) ->
      print_endline (string_of_term (eval term) ^ " : " ^ string_of_typ typ);
      loop lexbuf prompt
  | exception ParseError msg ->
      err "%s" msg;
      synchronize lexbuf;
      loop lexbuf prompt
  | exception TypeError msg ->
      err "%s" msg;
      loop lexbuf prompt

(** Start the REPL *)
let repl () =
  let lexbuf = Lexing.from_channel stdin in
  loop lexbuf (fun () -> Printf.printf ">> %!")

(** Parse and execute a file *)
let run_file (fn : string) =
  let fd = open_in fn in
  let lexbuf = Lexing.from_channel fd in
  loop lexbuf (fun () -> ());
  close_in fd
