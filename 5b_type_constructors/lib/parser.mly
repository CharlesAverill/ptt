%{
open Syntax
open Monads
%}

// binders
%token LAMBDA, BIGLAM, FORALL
%token <string> IDENT
%token <string> TYPE_IDENT
%token DOT
// brackets
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
// primitives
%token UNIT, TRUE, FALSE
%token <int> INT
// types
%token TUNIT
%token BOOL
%token NAT
%token COLON
%token ARROW
// operators
%token IF
%token THEN
%token ELSE
%token ISEQ
%token LET
%token IN
%token BINDER
// top-level definitions
%token EQ
%token DEF
%token TYPE
// control tokens
%token DSEMI
%token EOF

// precedences
%nonassoc BINDER
%nonassoc ISEQ

%start <(Syntax.sterm, string) result> menhir_parse
%start <(Syntax.sphrase option, string) result> menhir_parse_phrase
%%

menhir_parse:
  | t = term; EOF   { t }

menhir_parse_phrase:
  | EOF               { return None }
  | DEF; id = IDENT; EQ; t = term; DSEMI
      { let* t' = t in
        return (Some (SPDef (id, None, t'))) }
  | DEF; id = IDENT; COLON; ty = typ; EQ; t = term; DSEMI
      { let* t' = t in
        return (Some (SPDef (id, Some ty, t'))) }
  | TYPE; id = TYPE_IDENT; EQ; t = typ; DSEMI
      { return (Some (SPTypedef (id, t))) }
  | t = term; DSEMI   { let* t' = t in return (Some (SPTerm t')) }

term:
  | LAMBDA; id = IDENT; COLON; ty = typ; DOT; t = term
      { let* t' = t in return (SLam (id, Some ty, t')) } %prec BINDER
  | LAMBDA; id = IDENT; DOT; t = term
      { let* t' = t in return (SLam (id, None, t')) } %prec BINDER
  | BIGLAM; id = TYPE_IDENT; DOT; t = term
      { let* t' = t in return (STLam (id, t')) } %prec BINDER
  | IF; b = term; THEN; c1 = term; ELSE; c2 = term
      { let* b' = b in
        let* c1' = c1 in
        let* c2' = c2 in
        return (SIfthenelse (b', c1', c2')) } %prec BINDER
  | LET; id = IDENT; EQ; t1 = term; IN; t2 = term
      { let* t1' = t1 in
        let* t2' = t2 in
        return (SLet (id, None, t1', t2')) } %prec BINDER
  | LET; id = IDENT; COLON; ty = typ; EQ; t1 = term; IN; t2 = term
      { let* t1' = t1 in
        let* t2' = t2 in
        return (SLet (id, Some ty, t1', t2')) } %prec BINDER
  | a = term; ISEQ; b = term
      { let* a' = a in
        let* b' = b in
        return (SIseq (a', b')) } %prec ISEQ
  | a = app
      { a }

app:
  | a = app; LBRACE; ty = typ; RBRACE
      { let* a' = a in return (SPolyApp (a', ty)) }
  | a = app; at = atom
      { let* a' = a in let* at' = at in return (SApp (a', at')) }
  | at = atom
      { at }

atom:
  | id = IDENT               { return (SVar id) }
  | UNIT                     { return SUnit }
  | TRUE                     { return STrue }
  | FALSE                    { return SFalse }
  | n = INT                  { return (SNat n) }
  | LPAREN; t = term; COLON; ty = typ; RPAREN
                             { let* t' = t in return (SAnn (t', ty)) }
  | LPAREN; t = term; RPAREN { t }

typ:
  | t = typArrow             { t }

typArrow:
  | t1 = typApp; ARROW; t2 = typArrow
                            { TArrow (t1, t2) }
  | FORALL; id = TYPE_IDENT; DOT; t = typArrow
                            { TForall (id, None, t) }
  | LAMBDA; id = TYPE_IDENT; DOT; t = typArrow
                            { TLam (id, None, t) }
  | t = typApp               { t }

typApp:
  | t = typAtom              { t }
  | t1 = typApp; t2 = typAtom
                            { TApp (t1, t2) }

typAtom:
  | TUNIT                    { TUnit }
  | BOOL                     { TBool }
  | NAT                      { TNat }
  | id = TYPE_IDENT          { TVar id }
  | LPAREN; t = typ; RPAREN  { t }
