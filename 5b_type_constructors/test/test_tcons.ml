(** Tests for the simply-typed lambda calculus interpreter. *)

open Ptt.Syntax
open Ptt.Eval
open Ptt.Typechecker.Defs
open Ptt.Typechecker.Types
open Ptt.Driver
open Ptt.Typechecker.Kinds

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
let capture_run_file ?(prelude = []) (fn : string) : string list =
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
  (try run_file prelude fn
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
  check "tfree: bound" [] (tfree (TForall ("a", Some KProper, TVar "a")));
  check "tfree: mixed under forall" [ "b" ]
    (tfree (TForall ("a", Some KProper, TArrow (TVar "a", TVar "b"))));
  check "tfree: shadowing forall still binds" []
    (tfree (TForall ("a", Some KProper, TForall ("a", Some KProper, TVar "a"))))

(* tcas *)

let () =
  check "tcas: hit" (TVar "b") (tcas (TVar "a") "a" (TVar "b"));
  check "tcas: miss" (TVar "c") (tcas (TVar "c") "a" (TVar "b"));
  check "tcas: arrow"
    (TArrow (TVar "b", TNat))
    (tcas (TArrow (TVar "a", TNat)) "a" (TVar "b"));
  check "tcas: shadow"
    (TForall ("a", Some KProper, TVar "a"))
    (tcas (TForall ("a", Some KProper, TVar "a")) "a" (TVar "b"));
  check "tcas: under binder"
    (TForall ("c", Some KProper, TVar "b"))
    (tcas (TForall ("c", Some KProper, TVar "a")) "a" (TVar "b"));
  check "tcas: avoids capture"
    (TForall ("b0", Some KProper, TVar "b"))
    (tcas (TForall ("b", Some KProper, TVar "a")) "a" (TVar "b"))

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
    | Ok (gamma', Some (PTerm Unit), TUnit) -> lookup_term gamma' "x" = None
    | _ -> false);
  check "typecheck_phrase: annotated def extends context" true
    (match typecheck_phrase empty_typctx (SPDef ("x", Some TNat, SNat 5)) with
    | Ok (gamma', Some (PDef ("x", Nat 5)), TNat) ->
        lookup_term gamma' "x" = Some TNat
    | _ -> false);
  check "typecheck_phrase: unannotated def synthesizes and extends context" true
    (match
       typecheck_phrase empty_typctx
         (SPDef ("id", None, SLam ("y", Some TUnit, SVar "y")))
     with
    | Ok (gamma', Some (PDef ("id", Lam ("y", Var "y"))), TArrow (TUnit, TUnit))
      ->
        lookup_term gamma' "id" = Some (TArrow (TUnit, TUnit))
    | _ -> false);
  check "typecheck_phrase: def with an undetermined type is rejected" true
    (Result.is_error
       (typecheck_phrase empty_typctx
          (SPDef ("id", None, SLam ("y", None, SVar "y")))));
  check "typecheck_phrase: later def can see earlier def's binding" true
    (match typecheck_phrase empty_typctx (SPDef ("x", Some TNat, SNat 5)) with
    | Ok (gamma', _, _) -> (
        match typecheck_phrase gamma' (SPTerm (SVar "x")) with
        | Ok (_, Some (PTerm (Var "x")), TNat) -> true
        | _ -> false)
    | _ -> false)

(* kind checking *)

let kind_of (g : typctx) (t : typ) : (kind, string) result =
  Result.map
    (fun (_, k, st) -> kdefault st.ksubst k)
    (check_type empty_state g t)

let () =
  check "check_type: closed primitive" (Ok KProper) (kind_of empty_typctx TUnit);
  check "check_type: free tyvar rejected" true
    (Result.is_error (kind_of empty_typctx (TVar "a")));
  check "check_type: bound tyvar accepted" (Ok KProper)
    (kind_of empty_typctx (TForall ("a", None, TVar "a")));
  check "check_type: free under forall rejected" true
    (Result.is_error (kind_of empty_typctx (TForall ("a", None, TVar "b"))));
  check "check_type: type operator kind is inferred"
    (Ok (KOperator (KOperator (KProper, KProper), KProper)))
    (kind_of empty_typctx (TLam ("f", None, TApp (TVar "f", TNat))));
  check "check_type: unconstrained binder kind defaults to *"
    (Ok (KOperator (KProper, KProper)))
    (kind_of empty_typctx (TLam ("a", None, TVar "a")));
  check "check_type: self-application is ill-kinded" true
    (Result.is_error
       (kind_of empty_typctx (TLam ("a", None, TApp (TVar "a", TVar "a")))));
  check "check_type: arrow of an operator is ill-kinded" true
    (Result.is_error
       (kind_of empty_typctx (TArrow (TLam ("a", None, TVar "a"), TNat))));
  check "check_type: bound tyvars shadow aliases" true
    (let g = update_alias empty_typctx "x" TNat KProper in
     match check_type empty_state g (TForall ("x", None, TVar "x")) with
     | Ok (TForall (x', _, TVar x''), _, _) -> x' = x'' && x' <> "x"
     | _ -> false)

(* polymorphism *)

let () =
  check "typecheck: tlam over unit" true
    (match typecheck empty_typctx (STLam ("a", SAnn (SUnit, TUnit))) with
    | Ok (_, TForall ("a", Some KProper, TUnit)) -> true
    | _ -> false);
  check "typecheck: tlam over id at tyvar" true
    (match
       typecheck empty_typctx
         (STLam ("a", SLam ("x", Some (TVar "a"), SVar "x")))
     with
    | Ok (_, TForall ("a", Some KProper, TArrow (TVar "a", TVar "a"))) -> true
    | _ -> false);
  check "typecheck: polyapp instantiates binder" true
    (match
       typecheck empty_typctx
         (SPolyApp (STLam ("a", SLam ("x", Some (TVar "a"), SVar "x")), TNat))
     with
    | Ok (_, TArrow (TNat, TNat)) -> true
    | _ -> false);
  check "typecheck: polyapp ill-formed argument rejected" true
    (Result.is_error
       (typecheck empty_typctx
          (SPolyApp (STLam ("a", SAnn (SUnit, TUnit)), TVar "b"))));
  check "typecheck: polyapp non-polymorphic head rejected" true
    (Result.is_error
       (typecheck empty_typctx (SPolyApp (SAnn (SUnit, TUnit), TNat))))

(* higher-kinded polymorphism (System F omega) *)

let () =
  check "typecheck: higher-kinded tlam infers operator kind from usage" true
    (match
       typecheck empty_typctx
         (STLam ("f", SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")))
     with
    | Ok
        ( _,
          TForall
            ( "f",
              Some (KOperator (KProper, KProper)),
              TArrow (TApp (TVar "f", TNat), TApp (TVar "f", TNat)) ) ) ->
        true
    | _ -> false);
  check "typecheck: instantiating a higher-kinded tlam with a type operator"
    true
    (match
       typecheck empty_typctx
         (SPolyApp
            ( STLam ("f", SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")),
              TLam ("g", None, TVar "g") ))
     with
    | Ok (_, TArrow (TNat, TNat)) -> true
    | _ -> false);
  check
    "typecheck: instantiating a higher-kinded tlam with a mismatched kind is \
     rejected"
    true
    (Result.is_error
       (typecheck empty_typctx
          (SPolyApp
             ( STLam ("f", SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")),
               TNat ))));
  check "typecheck: annotating a term with a type operator is rejected" true
    (Result.is_error
       (typecheck empty_typctx (SAnn (SUnit, TLam ("f", None, TVar "f")))))

(* [unify], type aliases *)

let () =
  check "unify: solves a metavariable, then compares up to beta" true
    (let id_op = TLam ("g", Some KProper, TVar "g") in
     let x, st = fresh_metavar empty_state in
     Result.is_ok
       (Result.bind (unify st empty_typctx x TNat) (fun st ->
            unify st empty_typctx (TApp (id_op, x)) TNat)));
  check "unify: alpha-equivalent foralls" true
    (Result.is_ok
       (unify empty_state empty_typctx
          (TForall ("a", Some KProper, TArrow (TVar "a", TVar "a")))
          (TForall ("b", Some KProper, TArrow (TVar "b", TVar "b")))));
  check "unify: foralls over different kinds differ" true
    (Result.is_error
       (unify empty_state empty_typctx
          (TForall ("a", Some KProper, TNat))
          (TForall ("b", Some (KOperator (KProper, KProper)), TNat))));
  check "typecheck_phrase: self-referential type alias is rejected" true
    (Result.is_error
       (typecheck_phrase empty_typctx (SPTypedef ("loop", TVar "loop"))));
  check "typecheck_phrase: typedef stores the inferred kind" true
    (match
       typecheck_phrase empty_typctx
         (SPTypedef ("idop", TLam ("g", None, TApp (TVar "g", TUnit))))
     with
    | Ok (gamma', None, _) -> (
        match lookup_alias gamma' "idop" with
        | Some
            ( TLam (_, Some (KOperator (KProper, KProper)), _),
              KOperator (KOperator (KProper, KProper), KProper) ) ->
            true
        | _ -> false)
    | _ -> false)

(* end-to-end *)

let () =
  check "e2e: id" "\\y. y"
    (string_of_term (eval (fst (parse "(\\x:unit->unit. x) (\\y:unit. y)"))));
  check "e2e: K" "\\z. z"
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
  check "e2e: tcons id instantiated"
    (Ok (TArrow (TNat, TNat)))
    (match parse "(/\\'a. \\x:'a. x)[nat]" with
    | _, ty -> Ok ty
    | exception TypeError m -> Error m);
  check "e2e: free tyvar instantiation rejected" true
    (typecheck_fails "(/\\'a. ())['b]");
  check "e2e: higher-kinded instantiation infers and checks operator kind"
    (Ok (TArrow (TNat, TNat)))
    (match parse "(/\\'f. \\x:'f nat. x) [\\'g. 'g]" with
    | _, ty -> Ok (beta_reduce_typ_display ty)
    | exception TypeError m -> Error m);
  check "e2e: instantiating with a mismatched kind is rejected" true
    (typecheck_fails "(/\\'f. \\x:'f nat. x) [nat]")

(* file reading and execution *)

let () =
  check "file: multi-line terms and comments"
    [
      "\\x. x : unit -> unit";
      "\\y. y : unit -> unit";
      "\\x. \\y. x : unit -> unit -> unit";
      "\\x. x : unit -> unit";
      "[ERROR] syntax error";
      "\\y. y : unit -> unit";
      "def x = 5 : nat";
      "def inc = \\y. y == 5 : nat -> bool";
      "5 : nat";
      "true : bool";
    ]
    (capture_run_file "sample.tcons");
  check "file: System F features are supported"
    [
      "\\x. x : (forall 'b:*. 'b -> 'b) -> forall 'b:*. 'b -> 'b";
      "\\f. f 5 : (forall 'a:*. 'a -> 'a) -> nat";
      "[ERROR] Unbound type variable 'b";
      "\\x. x : forall 'b:*. 'b -> 'b";
    ]
    (capture_run_file "systemf.tcons");
  check "file: System F omega features are supported"
    [
      "\\x. x : nat -> nat";
      "\\h. h 5 : (forall 'f:* => *. ('f nat) -> 'f nat) -> nat";
      "[ERROR] Type unification failure, forall 'a:* => *. 'a nat <> unit";
      "\\x. x : forall 'g:* => *. ('g nat) -> 'g nat";
      "\\x. x : forall 'f:(* => *) => *. ('f (\\'a:*. 'a)) -> 'f (\\'a:*. 'a)";
      "\\x. x : forall 'f:* => *. ('f ('f nat)) -> 'f ('f nat)";
      "\\x. x : forall 'b:*. nat -> nat";
      "[ERROR] Infinite kind: ?k0 occurs in ?k0 => ?k1";
      "[ERROR] \\'a. 'a has kind ?k0 => ?k0, but only types of kind * can \
       classify terms";
    ]
    (capture_run_file "fomega.tcons");
  check "file: Type inference"
    [
      "\\x. x : ?a -> ?a";
      "5 : nat";
      "\\x. x == 5 : nat -> bool";
      "false : bool";
      "\\f. f 5 : (nat -> ?b) -> ?b";
      "\\f. \\x. f x : (?b -> ?c) -> ?b -> ?c";
      "true : bool";
      "\\x. if x then 5 else 6 : bool -> nat";
      "[ERROR] Type unification failure, ?a <> ?a -> ?b";
      "\\y. y : ?b -> ?b";
      "\\f. \\x. f (f x) : (?d -> ?d) -> ?d -> ?d";
      "[ERROR] The type of id: (?a -> ?a) is not fully determined. Try \
       annotating it";
      "[ERROR] Couldn't determine type of id";
      "[ERROR] Couldn't determine type of id";
    ]
    (capture_run_file "infer.tcons");
  check "file: type variables cannot escape their scope"
    [
      "[ERROR] Type variable 'a would escape its scope through the type of y: \
       'a";
      "[ERROR] Type variable 'a would escape its scope through the type of y: \
       'a";
      "[ERROR] Type variable 'b#3 would escape its scope through the type of \
       y: 'b#3";
      "[ERROR] Type variable 'a0 would escape its scope through the type of f: \
       forall 'a:*. 'a0 -> 'a0";
      "\\x. x : forall 'b:*. 'b -> 'b";
      "5 : nat";
      "\\y. \\z. y : forall 'a:*. 'a -> forall 'a0:*. 'a0 -> 'a";
      "5 : nat";
      "[ERROR] Type unification failure, 'a0 <> 'a";
      "true : bool";
      "true : bool";
    ]
    (capture_run_file "scope.tcons");
  (* Only compare the output of the file itself, not of the stdlib prelude *)
  let last n l = List.filteri (fun i _ -> i >= List.length l - n) l in
  let expected =
    [
      "\\f. \\g. g 5 : 'option nat";
      "true : bool";
      "true : bool";
      "def toggle = \\k. k (\\f. (f false) (\\f. (f (\\b. if b then false else \
       true)) (\\b. b))) : 'exists 'toggleSig";
      "true : bool";
      "[ERROR] Type unification failure, bool <> 'S";
    ]
  in
  check "file: stdlib encodings are usable" expected
    (last (List.length expected)
       (capture_run_file ~prelude:[ "../stdlib/types.tcons" ] "stdlib.tcons"))

(* Report *)

let () =
  match !failures with
  | [] -> print_endline "All tests passed"
  | fs ->
      Printf.printf "\n%d test(s) failed:\n" (List.length fs);
      List.iter (Printf.printf "  - %s\n") (List.rev fs);
      exit 1
