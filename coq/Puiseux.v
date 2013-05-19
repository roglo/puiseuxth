(* $Id: Puiseux.v,v 1.489 2013-05-19 18:44:02 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Puiseux_base.
Require Import Misc.

Definition degree α (pol : polynomial α) := List.length (al pol).
Arguments degree : default implicits.

Definition apply_polynomial {α} fld pol (x : α) :=
  List.fold_right (λ accu coeff, add fld (mul fld accu x) coeff) (an pol)
    (al pol).
Arguments apply_polynomial : default implicits. 

Record algebraically_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol, degree pol ≥ 1
      → ∃ r, apply_polynomial ac_field pol r = zero ac_field }.
Arguments ac_field : default implicits.
Arguments ac_prop : default implicits.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (fld : field α) k dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol α fld k [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec (deg + n) k then
            [coeff … make_char_pol α fld k dcl₁ n₁]
          else
            [zero fld … make_char_pol α fld k dcl n₁]
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
  let cl := make_char_pol α fld (k - j) dcl k in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff α kps |}.

Lemma cpol_degree : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → degree cpol ≥ 1.
Proof.
intros α fld acf pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (fin_pt ns))) as n.
destruct n; simpl.
 Focus 2.
 destruct (eq_nat_dec (nofq (fst (ini_pt ns)) + S n)); apply le_n_S, le_0_n.

 unfold nofq in Heqn.
 unfold newton_segments in Hns.
bbb.

Lemma exists_root : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros α fld acf pol cpol ns Hns Hpol.
eapply cpol_degree in Hns; [ idtac | eassumption ].
apply (ac_prop acf cpol Hns).
Qed.
