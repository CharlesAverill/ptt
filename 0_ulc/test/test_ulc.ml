(** Tests for the untyped lambda calculus interpreter. *)

open Ptt.Syntax
open Ptt.Eval
open Ptt.Driver

let failures : string list ref = ref []

let check (name : string) (expected : 'a) (actual : 'a) : unit =
  if expected <> actual then (
    Printf.printf "FAIL: %s\n%!" name;
    failures := name :: !failures)

let parse_fails (s : string) : bool =
  match parse s with _ -> false | exception Ptt.Lexer.ParseError _ -> true

(** Strip ANSI escape sequences (["\x1b[...m"]) from a string *)
let strip_ansi (s : string) : string =
  let buf = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '\x1b' then (
      incr i;
      while !i < n && s.[!i] <> 'm' do
        incr i
      done;
      if !i < n then incr i)
    else (
      Buffer.add_char buf s.[!i];
      incr i)
  done;
  Buffer.contents buf

(* Capture [run_file] output *)
let capture_run_file (fn : string) : string list =
  flush stdout;
  flush stderr;
  let tmp = Filename.temp_file "ptt_test" ".out" in
  let out_fd = Unix.openfile tmp [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let saved_stdout = Unix.dup Unix.stdout in
  let saved_stderr = Unix.dup Unix.stderr in
  Unix.dup2 out_fd Unix.stdout;
  Unix.dup2 out_fd Unix.stderr;
  Unix.close out_fd;
  let restore () =
    flush stdout;
    flush stderr;
    Unix.dup2 saved_stdout Unix.stdout;
    Unix.dup2 saved_stderr Unix.stderr;
    Unix.close saved_stdout;
    Unix.close saved_stderr
  in
  (try run_file fn
   with e ->
     restore ();
     Sys.remove tmp;
     raise e);
  restore ();
  let ic = open_in tmp in
  let lines = ref [] in
  (try
     while true do
       lines := strip_ansi (input_line ic) :: !lines
     done
   with End_of_file -> ());
  close_in ic;
  Sys.remove tmp;
  List.rev !lines

(* free *)

let () =
  check "free: var" [ "x" ] (free (Var "x"));
  check "free: bound" [] (free (Lam ("x", Var "x")));
  check "free: mixed" [ "y" ] (free (Lam ("x", App (Var "x", Var "y"))));
  check "free: app" [ "x"; "y" ] (free (App (Var "x", Var "y")))

(* cas *)

let () =
  check "cas: hit" (Var "y") (cas (Var "x") "x" (Var "y"));
  check "cas: miss" (Var "z") (cas (Var "z") "x" (Var "y"));
  check "cas: shadow"
    (Lam ("x", Var "x"))
    (cas (Lam ("x", Var "x")) "x" (Var "y"));
  check "cas: under binder"
    (Lam ("z", Var "y"))
    (cas (Lam ("z", Var "x")) "x" (Var "y"));
  check "cas: avoids capture"
    (Lam ("y0", Var "y"))
    (cas (Lam ("y", Var "x")) "x" (Var "y"))

(* is_value *)

let () =
  check "is_value: lam" true (is_value (Lam ("x", Var "x")));
  check "is_value: var" false (is_value (Var "x"));
  check "is_value: app" false (is_value (App (Var "x", Var "y")))

(* step *)

let () =
  check "step: var stuck" true (Result.is_error (step (Var "x")));
  check "step: lam stuck" true (Result.is_error (step (Lam ("x", Var "x"))));
  check "step: nonvalue arg stuck" true
    (Result.is_error (step (App (Lam ("x", Var "x"), Var "y"))));
  check "step: beta"
    (Ok (Lam ("y", Var "y")))
    (step (App (Lam ("x", Var "x"), Lam ("y", Var "y"))))

(* eval *)

let () =
  check "eval: id"
    (Lam ("y", Var "y"))
    (eval (App (Lam ("x", Var "x"), Lam ("y", Var "y"))));
  check "eval: K"
    (Lam ("z", Var "z"))
    (eval
       (App
          ( App (Lam ("x", Lam ("y", Var "x")), Lam ("z", Var "z")),
            Lam ("w", Var "w") )));
  check "eval: value" (Lam ("x", Var "x")) (eval (Lam ("x", Var "x")));
  check "eval: arg reduced"
    (Lam ("z", Var "z"))
    (eval
       (App (Lam ("x", Var "x"), App (Lam ("y", Var "y"), Lam ("z", Var "z")))));
  check "eval: stuck arg"
    (App (Lam ("x", Var "x"), Var "z"))
    (eval (App (Lam ("x", Var "x"), Var "z")))

(* parse *)

let () =
  check "parse: var" (Var "x") (parse "x");
  check "parse: lam" (Lam ("x", Var "x")) (parse "\\x. x");
  check "parse: app" (App (Var "x", Var "y")) (parse "x y");
  check "parse: app left-assoc"
    (App (App (Var "x", Var "y"), Var "z"))
    (parse "x y z");
  check "parse: parens"
    (App (Var "x", App (Var "y", Var "z")))
    (parse "x (y z)");
  check "parse: lam body extends right"
    (Lam ("x", App (Var "x", Var "y")))
    (parse "\\x. x y");
  check "parse: unmatched paren" true (parse_fails ")");
  check "parse: empty" true (parse_fails "");
  check "parse: comment skipped"
    (App (Var "x", Var "y"))
    (parse "x (* a comment *) y");
  check "parse: nested comment skipped" (Var "x")
    (parse "(* outer (* inner *) outer *) x");
  check "parse: unterminated comment" true (parse_fails "(* oops")

(* end-to-end *)

let () =
  check "e2e: id" "\\y.(y)" (string_of_term (eval (parse "(\\x. x) (\\y. y)")));
  check "e2e: K" "\\z.(z)"
    (string_of_term (eval (parse "(\\x. \\y. x) (\\z. z) (\\w. w)")));
  check "e2e: stuck" "\\x.(x) y" (string_of_term (eval (parse "(\\x. x) y")))

(* file reading and execution *)

let () =
  check "file: multi-line terms and comments"
    [ "\\x.(x)"; "\\y.(y)"; "\\x.(\\y.(x))" ]
    (capture_run_file "sample1.ulc");
  check "file: execution continues after a bad phrase"
    [ "\\x.(x)"; "LOG:[ERROR] syntax error"; "\\y.(y)" ]
    (capture_run_file "sample2.ulc")

(* Report *)

let () =
  match !failures with
  | [] -> print_endline "All tests passed"
  | fs ->
      Printf.printf "\n%d test(s) failed:\n" (List.length fs);
      List.iter (Printf.printf "  - %s\n") (List.rev fs);
      exit 1
