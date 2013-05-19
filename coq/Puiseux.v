(* $Id: Puiseux.v,v 1.484 2013-05-19 15:44:35 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Puiseux_base.
Require Import Misc.

Record algebraically_closed_field α :=
  { ac_field : field α;
    ac_roots : polynomial α → list (α * nat) }.
Arguments ac_field : default implicits.
Arguments ac_roots : default implicits.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (fld : field α) k n dcl :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol α fld k n₁ []]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec (deg + n) k then
            [coeff … make_char_pol α fld k n₁ dcl₁]
          else
            [zero fld … make_char_pol α fld k n₁ dcl]
      end
    end.

Definition deg_coeff_of_point α pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := List.nth h (al pol) (an pol) in
  let c := valuation_coeff α ps in
  (h, c).

Definition roots_of_characteristic_polynomial α acf pol ns :=
  let dcl := List.map (deg_coeff_of_point α pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol α (ac_field acf) k (k - j) dcl in
  let kps := List.nth k (al pol) (an pol) in
  let cpol := {| al := cl; an := valuation_coeff α kps |} in
  ac_roots acf cpol.
