(* $Id: poly_parse.ml,v 1.1 2013-03-28 13:24:20 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "./q_def_expr.cmo";

open Pnums;

value gram = Grammar.gcreate Poly_lex.t;
value polynom_eoi = Grammar.Entry.create gram "polynom";

EXTEND
  GLOBAL: polynom_eoi;
  polynom_eoi:
    [ [ p = polynom; EOI → p ] ]
  ;
  polynom:
    [ [ e₁ = SELF; "+"; e₂ = SELF → << $e₁$ + $e₂$ >>
      | e₁ = SELF; "-"; e₂ = SELF → << $e₁$ - $e₂$ >> ]
    | [ "-"; e = SELF → << - $e$ >> ]
    | "*"
      [ e₁ = SELF; e₂ = SELF → << $e₁$ * $e₂$ >>
      | e₁ = SELF; "/"; e₂ = SELF → << $e₁$ / $e₂$ >> ]
    | "simple"
      [ v = IDENT → << $lid:v$ >>
      | v = IDENT; n = rat_rsup → << $lid:v$ ** $n$ >>
      | "√"; v = IDENT → << $lid:v$ ** (1/2) >>
      | "√"; v = INT → << $int:v$ ** (1/2) >>
      | "√"; n = INT; "/"; d = INT → << $int:n$ ** (1/2) / $int:d$ >>
      | "∛"; v = IDENT → << $lid:v$ ** (1/3) >>
      | "∛"; v = IDENT; n = nsup → << $lid:v$ ** ($int:n$/3) >>
      | e = rat → e
      | "("; e = SELF; ")" → e
      | "("; e = SELF; ")"; n = nsup → << $e$ ** $int:n$ >> ] ]
  ;
  polynom: LEVEL "*"
    [ [ e₁ = SELF; "*"; e₂ = SELF → << $e₁$ * $e₂$ >> ] ]
  ;
  polynom: LEVEL "simple"
    [ [ v = IDENT; "^"; e = rat₀ → << $lid:v$ ** $e$ >>
      | "("; e₁ = SELF; ")"; "^"; e₂ = rat₀ → << $e₁$ ** $e₂$ >> ] ]
  ;
  rat₀:
    [ [ q = rat → q
      | "("; q = rat; ")" → q
      | "("; "-"; q = rat; ")" → << - $q$ >> ] ]
  ;

  rat_rsup:
    [ [ q = rat → q
      | q = rsup → q
      | "⁻"; q = rsup → << - $q$ >> ] ]
  ;
  rat:
    [ [ n = INT; "/"; d = INT → << $int:n$ / $int:d$ >>
      | n = INT → << $int:n$ >>
      | n = FLOAT → << $flo:n$ >> ] ]
  ;
  rsup:
    [ [ n = nsup; "ᐟ"; d = nsup → << $int:n$ / $int:d$ >>
      | n = nsup → << $int:n$ >> ] ]
  ;
  nsup:
    [ [ i = nsup; n = SUP → i ^ n
      | n = SUP → n ] ]
  ;
END;

value parse_poly s =
  Grammar.Entry.parse polynom_eoi (Stream.of_string s)
;

value parse_poly_in_file vy fname =
  let ic = open_in fname in
  try
    loop 0 1 [] where rec loop bol_pos line rev_pl =
      match try Some (input_line ic) with [ End_of_file → None ] with
      [ Some s →
          let p =
            try parse_poly s with
            [ Ploc.Exc loc e →
                let loc =
                  Ploc.make_loc fname line bol_pos
                    (Ploc.first_pos loc, Ploc.last_pos loc) ""
                in
                Ploc.raise loc e ]
          in
          loop (pos_in ic) (line + 1) [p :: rev_pl]
      | None →
          let (_, p) =
            let loc = Ploc.dummy in
            List.fold_right
              (fun p₁ (ypow, p) →
                 let p =
                   if ypow = 0 then p₁
                   else << $p$ + $p₁$ * $lid:vy$ ** $int:soi ypow$ >>
                 in
                 (ypow + 1, p))
              rev_pl (0, << phony >>)
          in
          p ]
  with e → do { close_in ic; raise e }
;

value op = ["+"; "-"; "*"; "/"; "**"];

value find_vars =
  loop [] where rec loop vl =
    fun
    [ << $a$ $b$ >> → loop (loop vl a) b
    | << $int:_$ >> | << $flo:_$ >> → vl
    | << $lid:v$ >> → if List.mem v vl || List.mem v op then vl else [v :: vl]
    | x → not_impl "poly.find_vars" x ]
;
