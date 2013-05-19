(* $Id: Puiseux.v,v 1.482 2013-05-19 13:46:54 deraugla Exp $ *)

Require Import QArith.
Require Import Puiseux_base.
Require Import Misc.

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

Definition characteristic_polynomial α fld pol ns :=
  let dcl := List.map (deg_coeff_of_point α pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol α fld k (k - j) dcl in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff α kps |}.

