(** Parser driver *)

open Logging
open Syntax
open Lexer
open Parser
open Eval

(** Parse a [string] into a [term], raising a [ParseError] if malformed *)
let parse (s : string) : term =
  let lexbuf = Lexing.from_string s in
  try
    match menhir_parse Lexer.read lexbuf with
    | Ok t -> t
    | Error e -> raise (ParseError e)
  with
  | Error -> raise (ParseError "syntax error")
  | SyntaxError m -> raise (ParseError m)

(** Read the next [;;]-terminated term from [lexbuf], or [None] once there is
    nothing left to read. Raises [ParseError] if the next phrase is malformed *)
let parse_phrase (lexbuf : Lexing.lexbuf) : term option =
  try
    match menhir_parse_phrase Lexer.read lexbuf with
    | Ok t -> t
    | Error e -> raise (ParseError e)
  with
  | Error -> raise (ParseError "syntax error")
  | SyntaxError m -> raise (ParseError m)

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
  | Some t ->
      print_endline (string_of_term (eval t));
      loop lexbuf prompt
  | exception ParseError msg ->
      err "%s" msg;
      synchronize lexbuf;
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
