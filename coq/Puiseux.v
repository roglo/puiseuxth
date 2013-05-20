(* $Id: Puiseux.v,v 1.495 2013-05-20 01:01:00 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Puiseux_base.
Require Import Misc.

Definition degree α (pol : polynomial α) := List.length (al pol).
Arguments degree : default implicits.

(* Horner's algorithm *)
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

Fixpoint make_char_pol α (fld : field α) cdeg dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol α fld (S cdeg) [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec deg cdeg then
            [coeff … make_char_pol α fld (S cdeg) dcl₁ n₁]
          else
            [zero fld … make_char_pol α fld (S cdeg) dcl n₁]
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
  let cl := make_char_pol α fld j dcl (k - j) in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff α kps |}.

(* *)

Lemma j_lt_k : ∀ α (fld : field (puiseux_series α)) pol j k ns,
  ns ∈ newton_segments fld pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros α fld pol j k ns Hns Hj Hk.
bbb.
 unfold newton_segments in Hns.
 remember (points_of_ps_polynom α fld pol) as pts.
 remember (lower_convex_hull_points pts) as hsl.
 remember Heqpts as Hsort; clear HeqHsort.
 apply points_of_polyn_sorted in Hsort.
 symmetry in Heqhsl.
 eapply lower_convex_hull_points_sorted in Hsort; [ idtac | eassumption ].
bbb.
*)

Lemma cpol_degree : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → degree cpol ≥ 1.
Proof.
intros α fld acf pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (ini_pt ns))) as j.
remember (nofq (fst (fin_pt ns))) as k.
remember (k - j)%nat as kj.
destruct kj; simpl.
 eapply j_lt_k with (j := j) in Hns; try eassumption.
 apply NPeano.Nat.sub_gt in Hns.
 symmetry in Heqkj; contradiction.

 rewrite <- Heqj.
 destruct (eq_nat_dec j j) as [| H]; [ apply le_n_S, le_0_n | idtac ].
 exfalso; apply H; reflexivity.
Qed.

Lemma exists_root : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros α fld acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
apply (ac_prop acf cpol Hdeg).
Qed.
