open Ptt.Driver
open Ptt.Logging
open Argparse

let stdlib_path =
  match Pttlib.Sites.stdlib with
  | [ h ] -> h
  | _ -> fatal rc_Error "Couldn't locate standard library"

let () =
  let args = parse_arguments () in
  (match args.verbosity with Some v -> _GLOBAL_LOG_LEVEL := v | None -> ());
  (* Load types.tcons *)
  let stdlib = List.map (Filename.concat stdlib_path) [ "types.tcons" ] in
  match args.filename with None -> repl stdlib | Some fn -> run_file stdlib fn
