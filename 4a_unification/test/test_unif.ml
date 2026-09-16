(** Tests for the simply-typed lambda calculus interpreter. *)

open Ptt.Syntax
open Ptt.Eval
open Ptt.Typechecker
open Ptt.Driver

let failures : string list ref = ref []

let check (name : string) (expected : 'a) (actual : 'a) : unit =
  if expected <> actual then (
    Printf.printf "FAIL: %s\n%!" name;
    failures := name :: !failures)

let parse_fails (s : string) : bool =
  match parse_sterm s with
  | _ -> false
  | exception Ptt.Lexer.ParseError _ -> true

let typecheck_fails (s : string) : bool =
  match parse s with _ -> false | exception TypeError _ -> true

(** Strip ANSI escape sequences from a string *)
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
  let out_fd =
    Unix.openfile tmp [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600
  in
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

(* tfree *)

let () =
  check "tfree: var" [ "a" ] (tfree (TVar "a"));
  check "tfree: primitive" [] (tfree TUnit);
  check "tfree: arrow" [ "a"; "b" ] (tfree (TArrow (TVar "a", TVar "b")));
  check "tfree: bound" [] (tfree (TForall ("a", TVar "a")));
  check "tfree: mixed under forall" [ "b" ]
    (tfree (TForall ("a", TArrow (TVar "a", TVar "b"))));
  check "tfree: shadowing forall still binds" []
    (tfree (TForall ("a", TForall ("a", TVar "a"))))

(* tcas *)

let () =
  check "tcas: hit" (TVar "b") (tcas (TVar "a") "a" (TVar "b"));
  check "tcas: miss" (TVar "c") (tcas (TVar "c") "a" (TVar "b"));
  check "tcas: arrow"
    (TArrow (TVar "b", TNat))
    (tcas (TArrow (TVar "a", TNat)) "a" (TVar "b"));
  check "tcas: shadow"
    (TForall ("a", TVar "a"))
    (tcas (TForall ("a", TVar "a")) "a" (TVar "b"));
  check "tcas: under binder"
    (TForall ("c", TVar "b"))
    (tcas (TForall ("c", TVar "a")) "a" (TVar "b"));
  check "tcas: avoids capture"
    (TForall ("b0", TVar "b"))
    (tcas (TForall ("b", TVar "a")) "a" (TVar "b"))

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

(* parse (structural, pre-typecheck) *)

let () =
  check "parse: var" (SVar "x") (parse_sterm "x");
  check "parse: lam"
    (SLam ("x", Some TUnit, SVar "x"))
    (parse_sterm "\\x:unit. x");
  check "parse: app" (SApp (SVar "x", SVar "y")) (parse_sterm "x y");
  check "parse: app left-assoc"
    (SApp (SApp (SVar "x", SVar "y"), SVar "z"))
    (parse_sterm "x y z");
  check "parse: parens"
    (SApp (SVar "x", SApp (SVar "y", SVar "z")))
    (parse_sterm "x (y z)");
  check "parse: lam body extends right"
    (SLam ("x", Some TUnit, SApp (SVar "x", SVar "y")))
    (parse_sterm "\\x:unit. x y");
  check "parse: unit" SUnit (parse_sterm "()");
  check "parse: unmatched paren" true (parse_fails ")");
  check "parse: empty" true (parse_fails "");
  check "parse: comment skipped"
    (SApp (SVar "x", SVar "y"))
    (parse_sterm "x (* a comment *) y");
  check "parse: nested comment skipped" (SVar "x")
    (parse_sterm "(* outer (* inner *) outer *) x");
  check "parse: unterminated comment" true (parse_fails "(* oops");
  check "parse: def rejected as subexpression" true
    (parse_fails "\\x:unit. def y = x");
  check "parse: def rejected in application" true (parse_fails "(def y = x) y")

(* typecheck_phrase *)

let () =
  check "typecheck_phrase: plain term leaves context unchanged" true
    (match typecheck_phrase empty_typctx (SPTerm (SAnn (SUnit, TUnit))) with
    | Ok (gamma', PTerm Unit, TUnit) -> lookup_term gamma' "x" = None
    | _ -> false);
  check "typecheck_phrase: annotated def extends context" true
    (match typecheck_phrase empty_typctx (SPDef ("x", Some TNat, SNat 5)) with
    | Ok (gamma', PDef ("x", Nat 5), TNat) -> lookup_term gamma' "x" = Some TNat
    | _ -> false);
  check "typecheck_phrase: unannotated def synthesizes and extends context" true
    (match
       typecheck_phrase empty_typctx
         (SPDef ("id", None, SLam ("y", Some TUnit, SVar "y")))
     with
    | Ok (gamma', PDef ("id", Lam ("y", Var "y")), TArrow (TUnit, TUnit)) ->
        lookup_term gamma' "id" = Some (TArrow (TUnit, TUnit))
    | _ -> false);
  check "typecheck_phrase: later def can see earlier def's binding" true
    (match typecheck_phrase empty_typctx (SPDef ("x", Some TNat, SNat 5)) with
    | Ok (gamma', _, _) -> (
        match typecheck_phrase gamma' (SPTerm (SVar "x")) with
        | Ok (_, PTerm (Var "x"), TNat) -> true
        | _ -> false)
    | _ -> false)

(* type_wf *)

let () =
  check "type_wf: closed primitive" true (type_wf empty_typctx TUnit);
  check "type_wf: free tyvar rejected" false (type_wf empty_typctx (TVar "a"));
  check "type_wf: bound tyvar accepted" true
    (type_wf empty_typctx (TForall ("a", TVar "a")));
  check "type_wf: free under forall rejected" false
    (type_wf empty_typctx (TForall ("a", TVar "b")));
  check "type_wf: arrow of bound tyvars" true
    (type_wf empty_typctx (TForall ("a", TArrow (TVar "a", TVar "a"))))

(* polymorphism *)

let () =
  check "gen: tlam over unit" true
    (match get_constraints empty_typctx (STLam ("a", SAnn (SUnit, TUnit))) with
    | Ok (TForall ("a", TUnit), _) -> true
    | _ -> false);
  check "gen: tlam over id at tyvar" true
    (match
       get_constraints empty_typctx
         (STLam ("a", SLam ("x", Some (TVar "a"), SVar "x")))
     with
    | Ok (TForall ("a", TArrow (TVar "a", TVar "a")), _) -> true
    | _ -> false);
  check "gen: polyapp instantiates binder" true
    (match
       get_constraints empty_typctx
         (SPolyApp
            (STLam ("a", SLam ("x", Some (TVar "a"), SVar "x")), Some TNat))
     with
    | Ok (TArrow (TNat, TNat), _) -> true
    | _ -> false);
  check "gen: polyapp ill-formed kappa rejected" true
    (match
       get_constraints empty_typctx
         (SPolyApp (STLam ("a", SAnn (SUnit, TUnit)), Some (TVar "b")))
     with
    | Error _ -> true
    | _ -> false);
  check "gen: polyapp non-polymorphic head rejected" true
    (match
       get_constraints empty_typctx (SPolyApp (SAnn (SUnit, TUnit), Some TNat))
     with
    | Error _ -> true
    | _ -> false)

(* end-to-end *)

let () =
  check "e2e: id" "\\y.(y)"
    (string_of_term (eval (fst (parse "(\\x:unit->unit. x) (\\y:unit. y)"))));
  check "e2e: K" "\\z.(z)"
    (string_of_term
       (eval
          (fst
             (parse
                "(\\x:unit->unit. \\y:unit->unit. x) (\\z:unit. z) (\\w:unit. \
                 w)"))));
  check "e2e: unbound variable rejected" true
    (typecheck_fails "(\\x:unit. x) y");
  check "e2e: argument type mismatch rejected" true
    (typecheck_fails "(\\x:unit. x) (\\y:unit. y)")

let () =
  check "e2e: unif id instantiated"
    (Ok (TArrow (TNat, TNat)))
    (match parse "(/\\'a. \\x:'a. x)[nat]" with
    | _, ty -> Ok ty
    | exception TypeError m -> Error m);
  check "e2e: free tyvar instantiation rejected" true
    (typecheck_fails "(/\\'a. ())['b]")

(* file reading and execution *)

let () =
  check "file: multi-line terms and comments"
    [
      "\\x.(x) : unit -> unit";
      "\\y.(y) : unit -> unit";
      "\\x.(\\y.(x)) : unit -> unit -> unit";
    ]
    (capture_run_file "sample1.unif");
  check "file: execution continues after a bad phrase"
    [
      "\\x.(x) : unit -> unit"; "[ERROR] syntax error"; "\\y.(y) : unit -> unit";
    ]
    (capture_run_file "sample2.unif");
  check "file: defs persist across phrases and are substituted at use"
    [
      "def x = 5 : nat";
      "def inc = \\y.(y == 5) : nat -> bool";
      "5 : nat";
      "true : bool";
    ]
    (capture_run_file "sample3.unif");
  check "file: System F features are supported"
    [
      "\\x.(x) : forall 'b.('b -> 'b) -> forall 'b.('b -> 'b)";
      "\\f.(f 5) : forall 'a.('a -> 'a) -> nat";
      "[ERROR] Type forall 'a.('b) is not well-formed";
      "\\x.(x) : forall 'b.('b -> 'b)";
    ]
    (capture_run_file "systemf.unif");
  check "file: Type inference"
    [
      "\\x.(x) : ?A -> ?A";
      "5 : nat";
      "\\x.(x == 5) : nat -> bool";
      "false : bool";
      "\\f.(f 5) : nat -> ?H -> ?H";
      "\\f.(\\x.(f x)) : ?J -> ?K -> ?J -> ?K";
      "true : bool";
      "\\x.(if x then 5 else 6) : bool -> nat";
      "[ERROR] Unification failure, ?Q <> ?Q -> ?R";
      "\\y.(y) : ?T -> ?T";
      "\\f.(\\x.(f f x)) : ?Y -> ?Y -> ?Y -> ?Y";
      "def id = \\x.(x) : ?Z -> ?Z";
      "5 : nat";
      "true : bool";
    ] (capture_run_file "infer.unif")

(* Report *)

let () =
  match !failures with
  | [] -> print_endline "All tests passed"
  | fs ->
      Printf.printf "\n%d test(s) failed:\n" (List.length fs);
      List.iter (Printf.printf "  - %s\n") (List.rev fs);
      exit 1
