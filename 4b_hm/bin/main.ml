open Ptt.Driver
open Ptt.Logging
open Argparse

let () =
  let args = parse_arguments () in
  (match args.verbosity with Some v -> _GLOBAL_LOG_LEVEL := v | None -> ());
  match args.filename with None -> repl () | Some fn -> run_file fn
