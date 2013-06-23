(* $Id: coq.ml,v 1.1 2013-06-23 17:03:51 deraugla Exp $ *)

open Pnums;

type comparison = [ Eq | Lt | Gt ];

value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value zcompare x₁ x₂ =
  let c = I.compare x₁ x₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;
