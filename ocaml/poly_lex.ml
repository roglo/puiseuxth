(* $Id: poly_lex.ml,v 1.1 2013-03-28 13:24:20 deraugla Exp $ *)

#load "pa_lexer.cmo";

exception Lexer_error of string;

value rec digits =
  lexer [ [ '0'-'9' ] digits! | ]
;

value number =
  lexer
  [ digits '.' digits → ("FLOAT", $buf)
  | digits → ("INT", $buf) ]
;

value rec next_token =
  lexer
  [ [ 'a'-'z' | 'A'-'Z' ] → ("IDENT", $buf)
  | [ '(' | ')' | '+' | '-' | '/' ] -> ("", $buf)
  | [ '*' | '^' ] → ("", $buf)
  | '0'-'9' number!
  | "¹" → ("SUP", "1")
  | "²" → ("SUP", "2")
  | "³" → ("SUP", "3")
  | "⁴" → ("SUP", "4")
  | "⁵" → ("SUP", "5")
  | "⁶" → ("SUP", "6")
  | "⁷" → ("SUP", "7")
  | "⁸" → ("SUP", "8")
  | "⁹" → ("SUP", "9")
  | "⁰" → ("SUP", "0")
  | "⁻" → ("", $buf)
  | "√" → ("", $buf)
  | "∛" → ("", $buf)
  | "ᐟ" → ("", $buf)
  | ' '/ next_token!
  | '\n'/ next_token!
  | _ -> raise (Lexer_error "bad char")
  | -> ("EOI", "") ]
;
value next_token_func (cs, r1, r2) =
  let bp = Stream.count cs in
  let tok =
    try next_token Plexing.Lexbuf.empty cs with
    [ Stream.Error s → raise (Lexer_error s) ]
  in
  let loc = Ploc.make_unlined (bp, bp + 1) in
  (tok, loc)
;
value lexer_func = Plexing.lexer_func_of_parser next_token_func;

value t =
  { Plexing.tok_func = lexer_func;
    Plexing.tok_using = (fun _ -> ());
    Plexing.tok_removing = (fun _ -> ());
    Plexing.tok_match = Plexing.default_match;
    Plexing.tok_text = Plexing.lexer_text;
    Plexing.tok_comm = None };
