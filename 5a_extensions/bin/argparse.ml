type arguments = {
  filename : string option;
  verbosity : Ptt.Logging.log_type option;
}

let parse_arguments () =
  let filename = ref None in
  let verbosity = ref None in

  let speclist =
    [
      ( "-v",
        Arg.String
          (fun s ->
            match Ptt.Logging.log_of_string s with
            | v -> verbosity := Some v
            | exception Failure msg -> raise (Arg.Bad msg)),
        "Set log verbosity: debug|info|warning|error|critical|none" );
    ]
  in
  let usage_msg = "Usage: ptt [-v LEVEL] [FILENAME]" in

  Arg.parse speclist
    (fun anon ->
      match !filename with
      | None -> filename := Some anon
      | Some _ -> failwith "bruh")
    usage_msg;

  { filename = !filename; verbosity = !verbosity }
