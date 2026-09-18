(** Tests for the simply-typed lambda calculus interpreter. *)

open Ptt.Syntax
open Ptt.Eval
open Ptt.Typechecker.Defs
open Ptt.Typechecker.Types
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
  (try run_file [] fn
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
  check "tfree: bound" [] (tfree (TForall ("a", KProper, TVar "a")));
  check "tfree: mixed under forall" [ "b" ]
    (tfree (TForall ("a", KProper, TArrow (TVar "a", TVar "b"))));
  check "tfree: shadowing forall still binds" []
    (tfree (TForall ("a", KProper, TForall ("a", KProper, TVar "a"))))

(* tcas *)

let () =
  check "tcas: hit" (TVar "b") (tcas (TVar "a") "a" (TVar "b"));
  check "tcas: miss" (TVar "c") (tcas (TVar "c") "a" (TVar "b"));
  check "tcas: arrow"
    (TArrow (TVar "b", TNat))
    (tcas (TArrow (TVar "a", TNat)) "a" (TVar "b"));
  check "tcas: shadow"
    (TForall ("a", KProper, TVar "a"))
    (tcas (TForall ("a", KProper, TVar "a")) "a" (TVar "b"));
  check "tcas: under binder"
    (TForall ("c", KProper, TVar "b"))
    (tcas (TForall ("c", KProper, TVar "a")) "a" (TVar "b"));
  check "tcas: avoids capture"
    (TForall ("b0", KProper, TVar "b"))
    (tcas (TForall ("b", KProper, TVar "a")) "a" (TVar "b"))

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
  check "typecheck_phrase: later def can see earlier def's binding" true
    (match typecheck_phrase empty_typctx (SPDef ("x", Some TNat, SNat 5)) with
    | Ok (gamma', _, _) -> (
        match typecheck_phrase gamma' (SPTerm (SVar "x")) with
        | Ok (_, Some (PTerm (Var "x")), TNat) -> true
        | _ -> false)
    | _ -> false)

(* type_wf / kind checking *)

let () =
  check "type_wf: closed primitive" true
    (Result.is_ok (type_wf empty_typctx TUnit));
  check "type_wf: free tyvar rejected" true
    (Result.is_error (type_wf empty_typctx (TVar "a")));
  check "type_wf: bound tyvar accepted" true
    (Result.is_ok (type_wf empty_typctx (TForall ("a", KProper, TVar "a"))));
  check "type_wf: free under forall rejected" true
    (Result.is_error (type_wf empty_typctx (TForall ("a", KProper, TVar "b"))));
  check "type_wf: arrow of bound tyvars" true
    (Result.is_ok
       (type_wf empty_typctx
          (TForall ("a", KProper, TArrow (TVar "a", TVar "a")))));
  (* [type_wf] only gathers kind constraints; a genuine kind mismatch (as
     opposed to an unbound variable) only surfaces once those constraints
     are actually solved *)
  check "type_wf: bare type operator rejected, must have kind *" true
    (match type_wf empty_typctx (TLam ("f", KProper, TVar "f")) with
    | Ok kc -> Result.is_error (Ptt.Typechecker.Kinds.unify kc)
    | Error _ -> true);
  check "type_wf: forall over a type operator is itself kind *" true
    (match
       type_wf empty_typctx
         (TForall
            ( "f",
              KOperator (KProper, KProper),
              TArrow (TApp (TVar "f", TUnit), TApp (TVar "f", TUnit)) ))
     with
    | Ok kc -> Result.is_ok (Ptt.Typechecker.Kinds.unify kc)
    | Error _ -> false)

(* polymorphism *)

let () =
  check "gen: tlam over unit" true
    (match
       get_constraints empty_typctx (STLam ("a", None, SAnn (SUnit, TUnit)))
     with
    | Ok (TForall ("a", _, TUnit), _, _) -> true
    | _ -> false);
  check "gen: tlam over id at tyvar" true
    (match
       get_constraints empty_typctx
         (STLam ("a", None, SLam ("x", Some (TVar "a"), SVar "x")))
     with
    | Ok (TForall ("a", _, TArrow (TVar "a", TVar "a")), _, _) -> true
    | _ -> false);
  check "gen: polyapp instantiates binder" true
    (match
       get_constraints empty_typctx
         (SPolyApp
            (STLam ("a", None, SLam ("x", Some (TVar "a"), SVar "x")), TNat))
     with
    | Ok (TArrow (TNat, TNat), _, _) -> true
    | _ -> false);
  check "gen: polyapp ill-formed kappa rejected" true
    (match
       get_constraints empty_typctx
         (SPolyApp (STLam ("a", None, SAnn (SUnit, TUnit)), TVar "b"))
     with
    | Error _ -> true
    | _ -> false);
  check "gen: polyapp non-polymorphic head rejected" true
    (match
       get_constraints empty_typctx (SPolyApp (SAnn (SUnit, TUnit), TNat))
     with
    | Error _ -> true
    | _ -> false)

(* higher-kinded polymorphism (System F omega) *)

let () =
  check "typecheck: higher-kinded tlam infers operator kind from usage" true
    (match
       typecheck empty_typctx
         (STLam ("f", None, SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")))
     with
    | Ok
        ( _,
          TForall
            ( "f",
              KOperator (KProper, KProper),
              TArrow (TApp (TVar "f", TNat), TApp (TVar "f", TNat)) ) ) ->
        true
    | _ -> false);
  check "typecheck: instantiating a higher-kinded tlam with a type operator"
    true
    (match
       typecheck empty_typctx
         (SPolyApp
            ( STLam
                ("f", None, SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")),
              TLam ("g", KProper, TVar "g") ))
     with
    | Ok (_, TArrow (TNat, TNat)) -> true
    | _ -> false);
  check
    "typecheck: instantiating a higher-kinded tlam with a mismatched kind is \
     rejected"
    true
    (match
       typecheck empty_typctx
         (SPolyApp
            ( STLam
                ("f", None, SLam ("x", Some (TApp (TVar "f", TNat)), SVar "x")),
              TNat ))
     with
    | Error _ -> true
    | _ -> false);
  check "typecheck: annotating a term with a type operator is rejected" true
    (match
       typecheck empty_typctx (SAnn (SUnit, TLam ("f", KProper, TVar "f")))
     with
    | Error _ -> true
    | _ -> false)

(* [unify] re-reduction, type aliases *)

let () =
  check "unify: re-reduces a redex introduced by a metavariable substitution"
    true
    (reset_metavar_counter ();
     let x = fresh_metavar () in
     let id_op = TLam ("g", KProper, TVar "g") in
     match unify empty_typctx [ (x, id_op); (TApp (x, TNat), TNat) ] with
     | Ok _ -> true
     | Error _ -> false);
  check "typecheck_phrase: self-referential type alias is rejected" true
    (match typecheck_phrase empty_typctx (SPTypedef ("loop", TVar "loop")) with
    | Error _ -> true
    | _ -> false);
  check "typecheck_phrase: typedef stores the kind-substituted alias body" true
    (let kmv = Ptt.Typechecker.Kinds.fresh_kmetavar () in
     match
       typecheck_phrase empty_typctx
         (SPTypedef ("idop", TLam ("g", kmv, TApp (TVar "g", TUnit))))
     with
     | Ok (gamma', None, _) -> (
         match lookup_alias gamma' "idop" with
         | Some (TLam (_, KOperator (KProper, _), _)) -> true
         | _ -> false)
     | _ -> false)

(* products *)

(* let () =
  check "type_wf: product of primitives" true
    (type_wf empty_typctx (TProd (TUnit, TBool)));
  check "gen: pair" true
    (match
       get_constraints empty_typctx
         (SPair (SAnn (SNat 5, TNat), SAnn (STrue, TBool)))
     with
    | Ok (TProd (TNat, TBool), _) -> true
    | _ -> false);
  check "typecheck: fst resolves via unification" true
    (match
       typecheck empty_typctx
         (SFst (SPair (SAnn (SNat 5, TNat), SAnn (STrue, TBool))))
     with
    | Ok (_, TNat) -> true
    | _ -> false);
  check "typecheck: snd resolves via unification" true
    (match
       typecheck empty_typctx
         (SSnd (SPair (SAnn (SNat 5, TNat), SAnn (STrue, TBool))))
     with
    | Ok (_, TBool) -> true
    | _ -> false);
  check "typecheck: fst on non-product rejected" true
    (match typecheck empty_typctx (SFst (SAnn (SNat 5, TNat))) with
    | Error _ -> true
    | _ -> false);
  check "typecheck: snd on non-product rejected" true
    (match typecheck empty_typctx (SSnd (SAnn (SNat 5, TNat))) with
    | Error _ -> true
    | _ -> false)

(* sums *)

let () =
  check "type_wf: sum of primitives" true
    (type_wf empty_typctx (TSum (TUnit, TBool)));
  check "gen: inl leaves right branch open" true
    (match get_constraints empty_typctx (SInl (SAnn (SNat 5, TNat))) with
    | Ok (TSum (TNat, TMetaVar _), _) -> true
    | _ -> false);
  check "gen: inr leaves left branch open" true
    (match get_constraints empty_typctx (SInr (SAnn (STrue, TBool))) with
    | Ok (TSum (TMetaVar _, TBool), _) -> true
    | _ -> false);
  check "typecheck: match merges branch types" true
    (match
       typecheck empty_typctx
         (SMatch
            ( SInl (SAnn (SNat 5, TNat)),
              "y",
              SIseq (SVar "y", SNat 5),
              "z",
              SVar "z" ))
     with
    | Ok (_, TBool) -> true
    | _ -> false);
  check "typecheck: match rejects mismatched branch types" true
    (match
       typecheck empty_typctx
         (SMatch (SInl (SAnn (SNat 5, TNat)), "y", SNat 5, "z", STrue))
     with
    | Error _ -> true
    | _ -> false)

(* lists *)

let () =
  check "type_wf: list of a primitive" true (type_wf empty_typctx (TList TNat));
  check "gen: nil is polymorphic" true
    (match get_constraints empty_typctx SNil with
    | Ok (TList (TMetaVar _), _) -> true
    | _ -> false);
  check "typecheck: cons resolves element type" true
    (match typecheck empty_typctx (SCons (SAnn (SNat 5, TNat), SNil)) with
    | Ok (_, TList TNat) -> true
    | _ -> false);
  check "typecheck: cons rejects mismatched element and tail" true
    (match
       typecheck empty_typctx
         (SCons (SAnn (STrue, TBool), SCons (SAnn (SNat 5, TNat), SNil)))
     with
    | Error _ -> true
    | _ -> false);
  check "typecheck: list match merges nil/cons branch types" true
    (match
       typecheck empty_typctx
         (SListMatch
            ( SCons (SAnn (SNat 5, TNat), SNil),
              STrue,
              "h",
              "t",
              SIseq (SVar "h", SNat 5) ))
     with
    | Ok (_, TBool) -> true
    | _ -> false);
  check "typecheck: self-referential list is rejected (occurs check)" true
    (match
       typecheck empty_typctx (SLam ("x", None, SCons (SVar "x", SVar "x")))
     with
    | Error _ -> true
    | _ -> false) *)

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
  check "e2e: tcons id instantiated"
    (Ok (TArrow (TNat, TNat)))
    (match parse "(/\\'a. \\x:'a. x)[nat]" with
    | _, ty -> Ok ty
    | exception TypeError m -> Error m);
  check "e2e: free tyvar instantiation rejected" true
    (typecheck_fails "(/\\'a. ())['b]");
  check "e2e: higher-kinded instantiation infers and checks operator kind"
    (Ok (TArrow (TNat, TNat)))
    (match parse "(/\\'f. \\x:'f nat. x) [\\'g:*. 'g]" with
    | _, ty -> Ok (beta_reduce_typ_display ty)
    | exception TypeError m -> Error m);
  check "e2e: instantiating with a mismatched kind is rejected" true
    (typecheck_fails "(/\\'f. \\x:'f nat. x) [nat]")

(* products, sums, lists: end-to-end *)

(* let () =
  check "e2e: fst reduces to the left component" "5"
    (string_of_term (eval (fst (parse "fst (5, true)"))));
  check "e2e: snd reduces to the right component" "true"
    (string_of_term (eval (fst (parse "snd (5, true)"))));
  check "e2e: sum match selects the inl branch" "true"
    (string_of_term
       (eval (fst (parse "match inl 5 with inl y => y == 5 | inr z => z end"))));
  check "e2e: sum match selects the inr branch" "true"
    (string_of_term
       (eval
          (fst (parse "match inr true with inl y => y == 5 | inr z => z end"))));
  check "e2e: list match selects the cons branch" "true"
    (string_of_term
       (eval
          (fst
             (parse "match (1 :: []) with [] => false | h :: t => h == 1 end"))));
  check "e2e: list match selects the nil branch" "true"
    (string_of_term
       (eval (fst (parse "match [] with [] => true | h :: t => false end"))));
  check "e2e: fst on a non-product is rejected" true (typecheck_fails "fst 5");
  check "e2e: mismatched cons element/tail rejected" true
    (typecheck_fails "true :: (1 :: [])") *)

(* file reading and execution *)

let () =
  check "file: multi-line terms and comments"
    [
      "\\x.(x) : (unit) -> (unit)";
      "\\y.(y) : (unit) -> (unit)";
      "\\x.(\\y.(x)) : (unit) -> ((unit) -> (unit))";
      "\\x.(x) : (unit) -> (unit)";
      "[ERROR] syntax error";
      "\\y.(y) : (unit) -> (unit)";
      "def x = 5 : nat";
      "def inc = \\y.(y == 5) : (nat) -> (bool)";
      "5 : nat";
      "true : bool";
    ]
    (capture_run_file "sample.tcons");
  check "file: System F features are supported"
    [
      "\\x.(x) : (forall 'b:*.(('b) -> ('b))) -> (forall 'b:*.(('b) -> ('b)))";
      "\\f.(f 5) : (forall 'a:*.(('a) -> ('a))) -> (nat)";
      "[ERROR] Couldn't determine kind of 'b";
      "\\x.(x) : forall 'b:*.(('b) -> ('b))";
    ]
    (capture_run_file "systemf.tcons");
  check "file: System F omega features are supported"
    [
      "\\x.(x) : (nat) -> (nat)";
      "\\h.(h 5) : (forall 'f:* => *.(('f nat) -> ('f nat))) -> (nat)";
      "[ERROR] Kind unification failure, * <> * => *e";
      "\\x.(x) : forall 'g:* => *.(('g nat) -> ('g nat))";
    ]
    (capture_run_file "fomega.tcons");
  check "file: Type inference"
    [
      "\\x.(x) : (?a) -> (?a)";
      "5 : nat";
      "\\x.(x == 5) : (nat) -> (bool)";
      "false : bool";
      "\\f.(f 5) : ((nat) -> (?h)) -> (?h)";
      "\\f.(\\x.(f x)) : ((?j) -> (?k)) -> ((?j) -> (?k))";
      "true : bool";
      "\\x.(if x then 5 else 6) : (bool) -> (nat)";
      "[ERROR] Type unification failure, ?q <> (?q) -> (?r)";
      "\\y.(y) : (?t) -> (?t)";
      "\\f.(\\x.(f f x)) : ((?y) -> (?y)) -> ((?y) -> (?y))";
      "def id = \\x.(x) : (?z) -> (?z)";
      "5 : nat";
      "true : bool";
    ]
    (capture_run_file "infer.tcons")

(* Report *)

let () =
  match !failures with
  | [] -> print_endline "All tests passed"
  | fs ->
      Printf.printf "\n%d test(s) failed:\n" (List.length fs);
      List.iter (Printf.printf "  - %s\n") (List.rev fs);
      exit 1
