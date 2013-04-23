(* $Id: Misc.v,v 1.2 2013-04-23 21:09:02 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Lemma Qmutual_shift_div : ∀ a b c d,
  0 < b
  → 0 < d
    → a / b < c / d
      → a * d < c * b.
Proof.
intros a b c d Hb Hd H.
apply Qmult_lt_compat_r with (z := b) in H; [ idtac | assumption ].
rewrite Qmult_comm in H.
rewrite Qmult_div_r in H.
 apply Qmult_lt_compat_r with (z := d) in H; [ idtac | assumption ].
 rewrite <- Qmult_assoc in H.
 remember (a * d) as t.
 rewrite Qmult_comm in H.
 rewrite <- Qmult_assoc in H.
 rewrite Qmult_div_r in H.
  rewrite Qmult_comm; assumption.

  intros HH; rewrite HH in Hd; apply Qlt_irrefl in Hd; contradiction.

 intros HH; rewrite HH in Hb; apply Qlt_irrefl in Hb; contradiction.
Qed.

Lemma Qdiv_lt_compat_r : ∀ a b c, 0 < c → a < b → a / c < b / c.
Proof.
intros a b c Hc H.
apply Qmult_lt_compat_r; [ idtac | assumption ].
apply Qinv_lt_0_compat; assumption.
Qed.

Lemma Qdiv_lt_reg_r : ∀ a b c, 0 < c → a / c < b / c → a < b.
Proof.
intros a b c Hc H.
apply Qmutual_shift_div in H; [ idtac | assumption | assumption ].
apply Qmult_lt_r in H; assumption.
Qed.

Lemma Qdiv_minus_distr_r : ∀ x y z, (x - y) / z == x / z - y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qdiv_plus_distr_r : ∀ x y z, (x + y) / z == x / z + y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qeq_opp_l : ∀ x y, - x == - y → x == y.
Proof.
intros x y H.
rewrite <- Qopp_opp, H.
apply Qopp_opp.
Qed.

Lemma Qeq_opp_r : ∀ x y, x == y → - x == - y.
Proof.
intros x y H; rewrite H; reflexivity.
Qed.

Lemma Qgt_0_not_0 : ∀ a, 0 < a → ¬a == 0.
Proof.
intros a Ha.
intros H.
rewrite H in Ha.
apply Qlt_irrefl in Ha; assumption.
Qed.

Lemma Qlt_minus : ∀ x y, x < y → 0 < y - x.
Proof.
intros x y H.
unfold Qlt in H |-*; simpl.
rewrite Z.mul_1_r, <- Zopp_mult_distr_l.
apply Zlt_left_lt.
assumption.
Qed.

Lemma Qlt_shift_mult_r : ∀ a b c, 0 < c → a < b / c → a * c < b.
Proof.
intros a b c Hc H.
apply Qmult_lt_compat_r with (z := c) in H; [ idtac | assumption ].
unfold Qdiv in H.
rewrite <- Qmult_assoc in H.
setoid_replace (/ c * c) with (c * / c) in H by apply Qmult_comm.
rewrite Qmult_inv_r in H; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Qmult_1_r in H; assumption.
Qed.

Lemma Qminus_eq : ∀ a b, a - b == 0 → a == b.
Proof.
intros a b H.
apply Qplus_inj_r with (z := - b).
rewrite Qplus_opp_r.
assumption.
Qed.

Lemma Qmult_div_assoc : ∀ a b c, a * (b / c) == (a * b) / c.
Proof. intros a b c; unfold Qdiv; apply Qmult_assoc. Qed.

Lemma Qmult_opp_r : ∀ x y, x * - y == - (x * y).
Proof.
intros x y.
unfold Qeq, Qmult, Qopp; simpl.
rewrite Z.mul_opp_r.
reflexivity.
Qed.

Lemma Qmult_minus_distr_r : ∀ x y z, x * (y - z) == x * y - x * z.
Proof.
intros x y z.
unfold Qminus.
rewrite Qmult_plus_distr_r.
rewrite Qmult_opp_r; reflexivity.
Qed.

(* to put in alphabetic order *)

Lemma QZ_plus : ∀ a b, a + b # 1 == (a # 1) + (b # 1).
Proof.
intros.
unfold Qplus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma QZ_minus : ∀ a b, a - b # 1 == (a # 1) - (b # 1).
Proof.
intros.
unfold Qminus, Qplus, Zminus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma Qopp_minus : ∀ x y, - (x - y) == y - x.
Proof. intros; field. Qed.

Lemma Qopp_lt_compat: ∀ p q : Q, p < q → - q < - p.
Proof.
intros (a₁, a₂) (b₁, b₂); unfold Qlt; simpl; intros H.
apply Z.opp_lt_mono.
do 2 rewrite Z.mul_opp_l.
do 2 rewrite Z.opp_involutive.
assumption.
Qed.

Lemma Qplus_div : ∀ a b c, ¬(c == 0) → a + b / c == (a * c + b) / c.
Proof.
intros a b c Hc.
rewrite Qdiv_plus_distr_r.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Lemma Qnat_lt_not_0 : ∀ i j, (i < j)%nat → ¬Z.of_nat (j - i) # 1 == 0.
Proof.
intros i j H.
rewrite Nat2Z.inj_sub; [ idtac | apply lt_le_weak; assumption ].
rewrite QZ_minus.
intros HH.
apply Qminus_eq in HH.
unfold Qeq in HH.
simpl in HH.
do 2 rewrite Zmult_1_r in HH.
apply Nat2Z.inj in HH.
subst j; apply lt_irrefl in H; assumption.
Qed.

Lemma Qnat_lt_0_lt : ∀ i j, (i < j)%nat → 0 < Z.of_nat (j - i) # 1.
Proof.
intros i j H.
rewrite Nat2Z.inj_sub; [ idtac | apply lt_le_weak; assumption ].
rewrite QZ_minus.
apply Qlt_minus.
unfold Qlt; simpl.
do 2 rewrite Zmult_1_r.
apply inj_lt; assumption.
Qed.

Lemma Qplus_minus_assoc : ∀ x y z, x + (y - z) == (x + y) - z.
Proof. intros x y z; ring. Qed.
