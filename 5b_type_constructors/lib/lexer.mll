{
open Lexing
open Parser

exception SyntaxError of string
exception ParseError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let type_id = '\'' id+
let digit = ['0'-'9']
let num = '0' | ['1'-'9'] digit*

rule read =
  parse
  | whitespace      { read lexbuf }
  | newline         { next_line lexbuf; read lexbuf }
  | "(*"            { comment 1 lexbuf }
  | "unit"          { TUNIT }
  | "bool"          { BOOL }
  | "nat"           { NAT }
  | "()"            { UNIT }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "def"           { DEF }
  | "type"          { TYPE }
  | "let"           { LET }
  | "in"            { IN }
  | "forall"        { FORALL }
  | "/\\"           { BIGLAM }
  | "=="            { ISEQ }
  | "="             { EQ }
  | id              { IDENT (Lexing.lexeme lexbuf) }
  | type_id         { TYPE_IDENT (Lexing.lexeme lexbuf) }
  | "\\"            { LAMBDA }
  | num             { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | ";;"            { DSEMI }
  | "."             { DOT }
  | ":"             { COLON }
  | "->"            { ARROW }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "["             { LBRACE }
  | "]"             { RBRACE }
  | eof             { EOF }
  | _ as c          { raise (SyntaxError (Printf.sprintf "unexpected character: %c" c)) }

and comment depth =
  parse
  | "(*"     { comment (depth + 1) lexbuf }
  | "*)"     { if depth = 1 then read lexbuf else comment (depth - 1) lexbuf }
  | newline  { next_line lexbuf; comment depth lexbuf }
  | eof      { raise (SyntaxError "unterminated comment") }
  | _        { comment depth lexbuf }
