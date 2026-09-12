%{
open Syntax
open Monads
%}

%token LAMBDA
%token <string> IDENT
%token <int> INT
%token DOT
%token LPAREN
%token RPAREN
%token UNIT
%token TUNIT
%token TRUE
%token FALSE
%token BOOL
%token NAT
%token DSEMI
%token COLON
%token ARROW
%token IF
%token THEN
%token ELSE
%token ISEQ
%token EOF

%right ARROW

%start <(Syntax.sterm, string) result> menhir_parse
%start <(Syntax.sterm option, string) result> menhir_parse_phrase
%%

menhir_parse:
  | t = term; EOF   { t }

menhir_parse_phrase:
  | EOF               { return None }
  | t = term; DSEMI   { let* t' = t in return (Some t') }

term:
  | LAMBDA; id = IDENT; COLON; ty = typ; DOT; t = term
      { let* t' = t in return (SLam (id, Some ty, t')) }
  | IF; b = term; THEN; c1 = term; ELSE; c2 = term
      { let* b' = b in
        let* c1' = c1 in
        let* c2' = c2 in
        return (SIfthenelse (b', c1', c2')) }
  | e = eq
      { e }

eq:
  | a = app; ISEQ; b = app
      { let* a' = a in
        let* b' = b in
        return (SIseq (a', b')) }
  | a = app
      { a }

app:
  | a = app; at = atom
      { let* a'  = a  in
        let* at' = at in
        return (SApp (a', at')) }
  | at = atom
      { at }

atom:
  | id = IDENT               { return (SVar id) }
  | UNIT                     { return SUnit }
  | TRUE                     { return STrue }
  | FALSE                    { return SFalse }
  | n = INT                  { return (SNat n) }
  | LPAREN; t = term; RPAREN { t }

typ:
  | t = typAtom             { t }
  | t1 = typ; ARROW; t2 = typ
                             { TArrow (t1, t2) }

typAtom:
  | TUNIT                    { TUnit }
  | BOOL                     { TBool }
  | NAT                      { TNat }
  | LPAREN; t = typ; RPAREN  { t }
