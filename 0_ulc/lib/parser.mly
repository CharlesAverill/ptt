%{
open Syntax
open Monads
%}

%token LAMBDA
%token <string> IDENT
%token DOT
%token LPAREN
%token RPAREN
%token DSEMI
%token EOF

%start <(Syntax.term, string) result> menhir_parse
%start <(Syntax.term option, string) result> menhir_parse_phrase
%%

menhir_parse:
  | t = term; EOF   { t }

menhir_parse_phrase:
  | EOF               { return None }
  | t = term; DSEMI   { let* t' = t in return (Some t') }

term:
  | LAMBDA; id = IDENT; DOT; t = term
      { let* t' = t in return (Lam (id, t')) }
  | a = app
      { a }

app:
  | a = app; at = atom
      { let* a'  = a  in
        let* at' = at in
        return (App (a', at')) }
  | at = atom
      { at }

atom:
  | id = IDENT               { return (Var id) }
  | LPAREN; t = term; RPAREN { t }
