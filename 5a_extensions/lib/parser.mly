%{
open Syntax
open Monads
%}

// binders
%token LAMBDA, BIGLAM, FORALL
%token <string> IDENT
%token <string> TYPE_IDENT
%token DOT
%token COMMA
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
%token FST
%token SND
%token INL
%token INR
%token NIL
%token CONS
%token MATCH
%token WITH
%token VERT
%token BIGARROW
%token END
// top-level definitions
%token EQ
%token DEF
// control tokens
%token DSEMI
%token EOF

// precedences
%nonassoc FORALL
%right ARROW

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
  | t = term; DSEMI   { let* t' = t in return (Some (SPTerm t')) }

term:
  | LAMBDA; id = IDENT; COLON; ty = typ; DOT; t = term
      { let* t' = t in return (SLam (id, Some ty, t')) }
  | LAMBDA; id = IDENT; DOT; t = term
      { let* t' = t in return (SLam (id, None, t')) }
  | BIGLAM; id = TYPE_IDENT; DOT; t = term
      { let* t' = t in return (STLam (id, t')) }
  | IF; b = term; THEN; c1 = term; ELSE; c2 = term
      { let* b' = b in
        let* c1' = c1 in
        let* c2' = c2 in
        return (SIfthenelse (b', c1', c2')) }
  | LET; id = IDENT; EQ; t1 = term; IN; t2 = term
      { let* t1' = t1 in
        let* t2' = t2 in
        return (SLet (id, None, t1', t2')) }
  | LET; id = IDENT; COLON; ty = typ; EQ; t1 = term; IN; t2 = term
      { let* t1' = t1 in
        let* t2' = t2 in
        return (SLet (id, Some ty, t1', t2')) }
  | MATCH; x = app; WITH;
      INL; y = IDENT; BIGARROW; e1 = term; VERT;
      INR; z = IDENT; BIGARROW; e2 = term; END
      { let* x' = x in let* e1' = e1 in let* e2' = e2 in
        return (SMatch (x', y, e1', z, e2')) }
  | MATCH; x = app; WITH;
      NIL; BIGARROW; e1 = term; VERT;
      h = IDENT; CONS; t = IDENT; BIGARROW; e2 = term; END
      { let* x' = x in let* e1' = e1 in let* e2' = e2 in
        return (SListMatch (x', e1', h, t, e2')) }
  | e = eq
      { e }

eq:
  | a = cons_expr; ISEQ; b = cons_expr
      { let* a' = a in
        let* b' = b in
        return (SIseq (a', b')) }
  | a = cons_expr
      { a }

cons_expr:
  | a = app; CONS; b = cons_expr
      { let* a' = a in let* b' = b in return (SCons (a', b')) }
  | a = app
      { a }

app:
  | FST; a = atom   { let* a' = a in return (SFst a') }
  | SND; a = atom   { let* a' = a in return (SSnd a') }
  | INL; a = atom   { let* a' = a in return (SInl a') }
  | INR; a = atom   { let* a' = a in return (SInr a') }
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
  | NIL                      { return SNil }
  | LPAREN; t = term; COLON; ty = typ; RPAREN
                             { let* t' = t in return (SAnn (t', ty)) }
  | LPAREN; t1 = term; COMMA; t2 = term; RPAREN
      { let* t1' = t1 in let* t2' = t2 in return (SPair (t1', t2')) }
  | LPAREN; t = term; RPAREN { t }

typ:
  | t = typAtom             { t }
  | t1 = typ; ARROW; t2 = typ
                            { TArrow (t1, t2) }
  | FORALL; id = TYPE_IDENT; DOT; t = typ
                            { TForall (id, t) } %prec FORALL

typAtom:
  | TUNIT                    { TUnit }
  | BOOL                     { TBool }
  | NAT                      { TNat }
  | id = TYPE_IDENT          { TVar id }
  | LPAREN; t = typ; RPAREN  { t }
