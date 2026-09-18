(** Parser driver *)

open Logging
open Syntax
open Lexer
open Parser
open Typechecker.Defs
open Typechecker.Types
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

(** Parse and typecheck a [string] from an empty context into a type-erased
    [term] *)
let parse (s : string) : typed_term =
  reset_metavar_counter ();
  Typechecker.Kinds.reset_kmetavar_counter ();
  match typecheck empty_typctx (parse_sterm s) with
  | Ok t -> t
  | Error s -> raise (TypeError s)

(** Read the next [;;]-terminated phrase from [lexbuf] and typecheck it under
    [gamma], producing the context to use for subsequent phrases and the
    type-erased [phrase] and its [typ]. Returns [None] once there is nothing
    left to read. Raises [ParseError] if the next phrase is malformed, or
    [TypeError] if it is ill-typed *)
let parse_phrase (lexbuf : Lexing.lexbuf) (gamma : typctx) :
    (typctx * phrase option * typ) option =
  let sp =
    try
      match menhir_parse_phrase Lexer.read lexbuf with
      | Ok t -> t
      | Error e -> raise (ParseError e)
    with
    | Error -> raise (ParseError "syntax error")
    | SyntaxError m -> raise (ParseError m)
  in
  match sp with
  | None -> None
  | Some sp' -> (
      match typecheck_phrase gamma sp' with
      | Ok result -> Some result
      | Error e -> raise (TypeError e))

(** Substitute previously-[def]ined names with their evaluated values *)
let subst_defs (defs : (string * term) list) (t : term) : term =
  List.fold_left (fun acc (x, v) -> cas acc x v) t defs

(** Synchronize the lexer after reading a bad term *)
let synchronize (lexbuf : Lexing.lexbuf) : unit =
  let rec loop () =
    match Lexer.read lexbuf with
    | DSEMI | EOF -> ()
    | _ -> loop ()
    | exception SyntaxError _ -> loop ()
  in
  loop ()

(** General execution loop. [gamma] is the typing context accumulated from prior
    [def]s; [defs] pairs each prior [def]'s name with its (already substituted
    and evaluated) value, so it can be substituted into later phrases before
    they are evaluated. *)
let rec loop (lexbuf : Lexing.lexbuf) (prompt : unit -> unit) (gamma : typctx)
    (defs : (string * term) list) : typctx * (string * term) list =
  prompt ();
  match parse_phrase lexbuf gamma with
  | None -> (gamma, defs) (* Now returns the final state instead of () *)
  | Some (gamma', Some (PTerm t), ty) ->
      let v = eval (subst_defs defs t) in
      Printf.printf "%s : %s\n%!" (string_of_term v) (string_of_typ ty);
      loop lexbuf prompt gamma' defs
  | Some (gamma', Some (PDef (x, e)), ty) ->
      let v = eval (subst_defs defs e) in
      Printf.printf "%s : %s\n%!"
        (string_of_phrase (PDef (x, v)))
        (string_of_typ ty);
      loop lexbuf prompt gamma' (defs @ [ (x, v) ])
  | Some (gamma', None, ty) -> loop lexbuf prompt gamma' defs
  | exception ParseError msg ->
      err "%s" msg;
      synchronize lexbuf;
      loop lexbuf prompt gamma defs
  | exception TypeError msg ->
      err "%s" msg;
      loop lexbuf prompt gamma defs

(** Execute a list of prelude files *)
let run_prelude_files (filenames : string list) : typctx * (string * term) list
    =
  List.fold_left
    (fun (acc_gamma, acc_defs) filename ->
      if not (Sys.file_exists filename) then (
        err "Prelude file %s not found. Skipping." filename;
        (acc_gamma, acc_defs))
      else
        let fd = open_in filename in
        let len = in_channel_length fd in
        let content = really_input_string fd len in
        close_in fd;

        let lexbuf = Lexing.from_string content in
        (* Run your exact loop silently (empty prompt function) *)
        loop lexbuf (fun () -> ()) acc_gamma acc_defs)
    (empty_typctx, []) filenames

let init (prelude_paths : string list) fd =
  reset_metavar_counter ();
  Typechecker.Kinds.reset_kmetavar_counter ();
  let init_gamma, init_defs = run_prelude_files prelude_paths in
  (init_gamma, init_defs, Lexing.from_channel fd)

(** Start the REPL *)
let repl (prelude_paths : string list) =
  (* List.iter print_endline prelude_paths; *)
  let init_gamma, init_defs, lexbuf = init prelude_paths stdin in
  let _ = loop lexbuf (fun () -> Printf.printf ">> %!") init_gamma init_defs in
  ()

(** Parse and execute a file *)
let run_file (prelude_paths : string list) (fn : string) =
  let fd = open_in fn in
  let init_gamma, init_defs, lexbuf = init prelude_paths fd in
  let _ = loop lexbuf (fun () -> ()) init_gamma init_defs in
  close_in fd
