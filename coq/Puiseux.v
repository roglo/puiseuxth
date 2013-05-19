(* $Id: Puiseux.v,v 1.479 2013-05-19 09:18:47 deraugla Exp $ *)

Require Import QArith.
Require Import Puiseux_base.
Require Import Misc.

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

Section puiseux.

Variable α : Type.
Variable fld : field (puiseux_series α).

End puiseux.

