(* $Id: coq.ml,v 1.2 2013-06-23 19:27:22 deraugla Exp $ *)

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

value nat_compare i₁ i₂ =
  let c = compare i₁ i₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;
