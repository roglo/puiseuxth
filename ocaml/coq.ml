(* $Id: coq.ml,v 1.4 2013-07-02 02:30:12 deraugla Exp $ *)

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

type z = [ Z0 | Zpos of I.t | Zneg of I.t ];

value zcoq z =
  if I.lt z I.zero then Zneg (I.neg z)
  else if I.gt z I.zero then Zpos z
  else Z0
;

value arg_test = ref False;
