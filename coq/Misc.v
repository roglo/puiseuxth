(* Misc.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorted.
From Stdlib Require Import Psatz.

Require Import RingLike.Misc.
Require Import RingLike.Core.
Require Import A_ZArith A_QArith.
Open Scope Q_scope.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).
Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).
(*
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
*)
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Ltac negation H := exfalso; apply H; reflexivity.
Tactic Notation "fast_omega" hyp_list(Hs) := revert Hs; clear; intros; lia.

Set Implicit Arguments.

(* Some theorems working with syntactic equality
   and not only with equivalence relation in Q *)

Theorem Q_opp_sub_distr : ∀ x y, - (x - y) = y - x.
Proof.
intros.
progress unfold Q.sub.
progress unfold Q.add.
progress unfold Q.opp.
progress unfold pos_mul; cbn.
rewrite (Nat.mul_comm (q_den y + 1)).
progress f_equal.
do 2 rewrite Z.mul_opp_l.
rewrite Z.add_comm.
rewrite Z.opp_add_distr.
now rewrite Z.opp_involutive.
Qed.

Theorem Q_sub_sub_distr : ∀ x y z, x - (y - z) = (x - y) + z.
Proof.
intros.
progress unfold Q.sub at 1.
rewrite Q_opp_sub_distr.
progress unfold Q.sub.
rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem Q_add_add_swap : ∀ x y z, x + y + z = x + z + y.
Proof.
intros.
do 2 rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem Q_mul_div_assoc : ∀ x y z, x * (y / z) = (x * y) / z.
Proof. intros; apply Q.mul_assoc. Qed.

Theorem Q_mul_div_swap : ∀ x y z, x / y * z = x * z / y.
Proof.
intros.
progress unfold Q.div.
do 2 rewrite <- Q.mul_assoc.
progress f_equal.
apply Q.mul_comm.
Qed.

Theorem Q_opp_0 : - 0 = 0.
Proof. easy. Qed.

Theorem Q_sub_0_r : ∀ n, n - 0 = n.
Proof.
intros.
progress unfold Q.sub.
rewrite Q_opp_0.
apply Q.add_0_r.
Qed.

(* doesn't work, works with this small modification *)

Definition Q1 x := q_Den x # q_den x.

Theorem Q_mul_add_distr_l' : ∀ x y z, x * (y + z) * Q1 x = x * y + x * z.
Proof.
intros.
progress unfold Q.add.
progress unfold Q.mul.
progress unfold pos_mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
progress f_equal. {
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_add_distr_r.
  progress unfold q_Den; cbn.
  rewrite Nat.sub_add; [ | flia ].
  rewrite Nat.sub_add; [ | flia ].
  do 2 rewrite Nat2Z.inj_mul.
  do 4 rewrite Z.mul_assoc.
  do 2 rewrite (Z.mul_mul_swap _ (Z.of_nat (q_den x + 1))).
  easy.
} {
  do 3 rewrite <- Nat.mul_assoc.
  progress f_equal.
  progress f_equal.
  progress f_equal.
  apply Nat.mul_comm.
}
Qed.

Theorem Q_mul_add_distr_r' : ∀ x y z, (x + y) * z * Q1 z = x * z + y * z.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q_mul_add_distr_l'.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem Q_mul_Q1_r : ∀ x y, x * Q1 y == x.
Proof.
intros.
progress unfold Q.eq.
cbn.
rewrite <- Z.mul_assoc.
progress f_equal.
rewrite Z.mul_comm.
symmetry.
progress unfold q_Den; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | flia ].
apply Nat2Z.inj_mul.
Qed.

(* *)

Theorem Q_mul_add_distr_l : ∀ x y z, x * (y + z) == x * y + x * z.
Proof.
intros.
rewrite <- Q_mul_add_distr_l'.
symmetry.
apply Q_mul_Q1_r.
Qed.

Theorem Q_mul_add_distr_r : ∀ x y z, (x + y) * z == x * z + y * z.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q_mul_add_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem Q_mul_sub_distr_l : ∀ x y z, x * (y - z) == x * y - x * z.
Proof.
intros.
progress unfold Q.sub.
rewrite Q_mul_add_distr_l.
apply Q.add_compat_l.
now rewrite Q.mul_opp_r.
Qed.

Theorem Q_mul_sub_distr_r : ∀ x y z, (x - y) * z == x * z - y * z.
Proof.
intros.
rewrite (Q.mul_comm (_ - _)).
rewrite Q_mul_sub_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Definition Qnat i := Z.of_nat i # 1.

Theorem Nat_sub_succ_diag : ∀ n, (S n - n = 1)%nat.
Proof.
intros.
rewrite Nat.sub_succ_l; [ | easy ].
now rewrite Nat.sub_diag.
Qed.

Theorem Nat_le_neq_lt : ∀ x y : nat, (x <= y)%nat → x ≠ y → (x < y)%nat.
Proof.
intros * Hxy Hnxy.
now destruct (le_lt_eq_dec x y Hxy).
Qed.

Theorem Qle_neq_lt : ∀ x y : Q, x ≤ y → ¬ x == y → x < y.
Proof.
intros * Hxy Hnxy.
apply Q.nle_gt.
intros H.
apply Q.le_antisymm in Hxy; [ | easy ].
now apply Hnxy.
Qed.

Theorem Z_mul_pos_pos : ∀ a b, (0 < a → 0 < b → 0 < a * b)%Z.
Proof.
intros * Hz1 Hz2.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ | easy ].
destruct sb; [ | easy ].
easy.
Qed.

Theorem Q_mul_pos_pos : ∀ a b, (0 < a → 0 < b → 0 < a * b)%Q.
Proof.
intros * Hz1 Hz2.
progress unfold Q.lt in Hz1, Hz2 |-*.
cbn in Hz1, Hz2 |-*.
rewrite Z.mul_1_r in Hz1, Hz2 |-*.
now apply Z_mul_pos_pos.
Qed.

Theorem Z_lt_eq_cases : ∀ a b, (a ≤ b ↔ a < b ∨ a = b)%Z.
Proof.
intros.
split; intros H. {
  destruct a as [| sa va]. {
    destruct b as [| sb vb]; [ now right | left ].
    now destruct sb.
  }
  destruct b as [| sb vb]. {
    destruct sa; [ easy | now left ].
  }
  destruct sa. {
    destruct sb; [ | easy ].
    progress unfold Z.le in H; cbn in H.
    progress unfold Z.lt; cbn.
    apply Nat.compare_le_iff in H.
    apply Nat.lt_eq_cases in H.
    destruct H; [ now left; apply Nat.compare_lt_iff | ].
    now right; subst.
  } {
    destruct sb; [ now left | ].
    progress unfold Z.le in H; cbn in H.
    progress unfold Z.lt; cbn.
    apply Nat.compare_le_iff in H.
    apply Nat.lt_eq_cases in H.
    destruct H; [ now left; apply Nat.compare_lt_iff | ].
    now right; subst.
  }
}
destruct H as [H| H]; [ | subst; apply Z.le_refl ].
now apply Z.lt_le_incl.
Qed.

Theorem Q_lt_eq_cases : ∀ a b, (a ≤ b ↔ a < b ∨ a == b)%Q.
Proof.
intros.
split; intros H. {
  progress unfold Q.le in H.
  apply Z_lt_eq_cases in H.
  now destruct H; [ left | right ].
}
destruct H as [H| H]; [ | rewrite H; apply Q.le_refl ].
now apply Q.lt_le_incl.
Qed.

Theorem Qdiv_lt_compat_r : ∀ x y z, 0 < z → x < y → x / z < y / z.
Proof.
intros * Hz Hxy.
Theorem Q_mul_lt_mono_pos_l :
  ∀ a b c, (0 < a)%Q → (b < c)%Q ↔ (a * b < a * c)%Q.
Proof.
intros * Hza.
split; intros Hbc. {
  apply Q.lt_0_sub.
  rewrite <- Q_mul_sub_distr_l.
  apply Q_mul_pos_pos; [ easy | ].
  now apply Q.lt_0_sub.
} {
  apply Q.lt_0_sub in Hbc.
  rewrite <- Q_mul_sub_distr_l in Hbc.
Theorem Q_mul_pos_cancel_l : ∀ a b, (0 < a → 0 < a * b ↔ 0 < b)%Q.
Proof.
intros * Hz.
split; intros Hz2. {
  apply Q.lt_iff in Hz.
  apply Q.lt_iff in Hz2.
  apply Q.lt_iff.
  destruct Hz as (Hle, Hz).
  destruct Hz2 as (Hlem, Hzm).
  split. {
    apply Q_lt_eq_cases in Hle.
    destruct Hle as [Hlt| H]; [ | easy ].
...
    apply rngl_nle_gt in Habz.
      apply (rngl_nlt_ge_iff Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hos Hor).
}

... ...
  apply Q_mul_pos_cancel_l in Hz2; [ | easy ].
...
  apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
...
intros * Hza.
split; intros Hbc. {
  progress unfold Q.lt in Hza, Hbc |-*.
  cbn in Hza.
  rewrite Z.mul_1_r in Hza.
  progress unfold q_Den in Hbc |-*; cbn.
  progress unfold pos_mul.
  rewrite Nat.sub_add; [ | flia ].
  rewrite Nat.sub_add; [ | flia ].
  do 2 rewrite Nat2Z.inj_mul.
  do 2 rewrite <- Z.mul_assoc.
  apply Z.mul_lt_mono_pos_l; [ easy | ].
  do 2 rewrite (Z.mul_comm (q_num _)).
  do 2 rewrite <- Z.mul_assoc.
  apply Z.mul_lt_mono_pos_l; [ now rewrite Nat.add_comm | ].
  now do 2 rewrite (Z.mul_comm _ (q_num _)).
}
Require Import RingLike.Core.
About rngl_mul_lt_mono_pos_l.

... ...
apply Z_mul_lt_mono_pos_l; [ easy | ].
Search (_ * _ < _ * _)%Z.
...
Theorem Q_mul_lt_mono_pos_r : ∀ a b c, (0 < a)%Q → (b < c)%Q ↔ (b * a < c * a)%Q.
Proof.
intros * Hza.
do 2 rewrite (Q.mul_comm _ a).
now apply Q_mul_lt_mono_pos_l.
Qed.
...
apply Q_mul_lt_mono_pos_r; [ | easy ].
...
Require Import RingLike.Core.
Search (_ < _ → _ * _ < _ * _)%nat.
Search (_ < _ ↔ _ / _ < _ / _)%nat.
Search (_ < _ → _ / _ < _ / _)%nat.
...
Theorem Q_mul_lt_compat_r :
     : ∀ x y z : Q, 0 < z → x < y → x * z < y * z

Nat.mul_lt_mono_nonneg:
  ∀ n m p q : nat, (0 <= n)%nat → (n < m)%nat → (0 <= p)%nat → (p < q)%nat → (n * p < m * q)%nat

Nat.mul_lt_mono_neg_r: ∀ p n m : nat, (p < 0)%nat → (n < m)%nat ↔ (m * p < n * p)%nat
Nat.mul_lt_mono_neg_l: ∀ p n m : nat, (p < 0)%nat → (n < m)%nat ↔ (p * m < p * n)%nat
Nat.mul_lt_mono_pos_r: ∀ p n m : nat, (0 < p)%nat → (n < m)%nat ↔ (n * p < m * p)%nat
Nat.mul_lt_mono_pos_l: ∀ p n m : nat, (0 < p)%nat → (n < m)%nat ↔ (p * n < p * m)%nat

rngl_div_lt_mono_pos_r:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_1 T = true
      → rngl_has_opp T = true
        → rngl_has_inv T = true
          → rngl_is_ordered T = true
            → (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true
              → ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b / a < c / a)%L

rngl_mul_lt_mono_pos_l:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_opp T = true
      → rngl_is_ordered T = true
        → (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true
          → ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L
rngl_mul_lt_mono_pos_r:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_opp T = true
      → rngl_is_ordered T = true
        → (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true
          → ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L

Zmult_lt_compat_l: ∀ n m p : Z, (0 < p)%Z → (n < m)%Z → (p * n < p * m)%Z
Zmult_lt_compat_r: ∀ n m p : Z, (0 < p)%Z → (n < m)%Z → (n * p < m * p)%Z
Z.square_lt_mono_nonpos: ∀ n m : Z, (n <= 0)%Z → (m < n)%Z → (n * n < m * m)%Z
Z.square_lt_mono_nonneg: ∀ n m : Z, (0 <= n)%Z → (n < m)%Z → (n * n < m * m)%Z
Zmult_gt_0_lt_compat_l: ∀ n m p : Z, (p > 0)%Z → (n < m)%Z → (p * n < p * m)%Z
Zmult_gt_0_lt_compat_r: ∀ n m p : Z, (p > 0)%Z → (n < m)%Z → (n * p < m * p)%Z
Z.mul_lt_mono_nonneg:
  ∀ n m p q : Z, (0 <= n)%Z → (n < m)%Z → (0 <= p)%Z → (p < q)%Z → (n * p < m * q)%Z
Z.mul_lt_mono_nonpos:
  ∀ n m p q : Z, (m <= 0)%Z → (n < m)%Z → (q <= 0)%Z → (p < q)%Z → (m * q < n * p)%Z

Search (_ * _ < _ * _)%Q.
...
apply Qmult_lt_compat_r; [ | easy ].
now apply Qinv_lt_0_compat.
Qed.

Theorem Qdiv_minus_distr_r : ∀ x y z, (x - y) / z == x / z - y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Theorem Qdiv_plus_distr_r : ∀ x y z, (x + y) / z == x / z + y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Definition Qeq_opp_r : ∀ x y, x == y → - x == - y :=
  λ x y Hxy,
  let H₁ := eq_sym (f_equal Z.opp Hxy) in
  let H₂ := eq_trans (Z.mul_opp_l (Qnum y) (Zpos (Qden x))) H₁ in
  let H₃ := Z.mul_opp_l (Qnum x) (Zpos (Qden y)) in
  eq_trans H₃ (eq_sym H₂).

Theorem Qgt_0_not_0 : ∀ x, 0 < x → ¬x == 0.
Proof.
intros x Ha.
intros H.
rewrite H in Ha.
apply Qlt_irrefl in Ha; assumption.
Qed.

Theorem Qlt_minus : ∀ x y, x < y → 0 < y - x.
Proof.
intros x y H.
unfold Qlt in H |-*; simpl.
rewrite Z.mul_1_r, <- Zopp_mult_distr_l.
apply Zlt_left_lt.
assumption.
Qed.

Theorem Qminus_eq : ∀ x y, x - y == 0 → x == y.
Proof.
intros x y H.
apply Qplus_inj_r with (z := - y).
rewrite Qplus_opp_r.
assumption.
Qed.

Theorem Qmult_minus_distr_l : ∀ x y z, (x - y) * z == x * z - y * z.
Proof.
intros x y z.
unfold Qminus.
rewrite <- Q_mul_opp_l.
rewrite <- Q_mul_add_distr_r.
symmetry.
apply Q_mul_Q1_r.
Qed.

Theorem Qmult_minus_distr_r : ∀ x y z, x * (y - z) == x * y - x * z.
Proof.
intros x y z.
unfold Qminus.
rewrite <- Q_mul_opp_r.
rewrite <- Q_mul_add_distr_l.
symmetry.
apply Q_mul_Q1_r.
Qed.

Theorem QZ_plus : ∀ x y z, x + y # z == (x # z) + (y # z).
Proof.
intros x y z.
unfold Qplus; simpl.
unfold Qeq; simpl.
rewrite Pos2Z.inj_mul; ring.
Qed.

Theorem Qnat_lt : ∀ i j, (i < j)%nat ↔ Qnat i < Qnat j.
Proof.
intros i j; split; intros H.
 unfold Qnat, Qlt; simpl.
 do 2 rewrite Zmult_1_r.
 apply inj_lt; assumption.

 unfold Qlt in H; simpl in H.
 do 2 rewrite Z.mul_1_r in H.
 apply Nat2Z.inj_lt in H; assumption.
Qed.

Theorem Qnat_succ : ∀ n x, x * Qnat (S n) == x * Qnat n + x.
Proof.
intros n x.
unfold Qnat.
setoid_replace x with (x * 1) at 3 by now rewrite Q_mul_1_r.
rewrite <- Q_mul_add_distr_l.
rewrite Q_mul_Q1_r.
rewrite Nat2Z.inj_succ.
rewrite <- Z.add_1_r.
now rewrite QZ_plus.
Qed.

Theorem Qlt_not_0 : ∀ x y, x < y → ¬ y - x == 0.
Proof.
intros i j H HH.
apply Qminus_eq in HH.
rewrite HH in H; apply Qlt_irrefl in H; contradiction.
Qed.

Theorem Qplus_div : ∀ x y z, ¬(z == 0) → x + y / z == (x * z + y) / z.
Proof.
intros x y z Hc.
rewrite Qdiv_plus_distr_r.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Theorem Zposnat2Znat : ∀ i, (0 < i)%nat → Zpos (Pos.of_nat i) = Z.of_nat i.
Proof.
intros i Hi.
destruct i; [ apply Nat.lt_irrefl in Hi; contradiction | clear Hi ].
simpl; f_equal.
induction i; [ reflexivity | simpl ].
rewrite IHi; reflexivity.
Qed.

(* *)

Theorem Qplus_lt_compat_r : ∀ x y z, x < y → x + z < y + z.
Proof.
intros (x₁, x₂) (y₁, y₂) (z₁, z₂) H.
unfold Qlt in H; simpl in H.
unfold Qlt, Qplus; simpl.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
do 4 rewrite Z.mul_assoc.
remember (z₁ * Zpos y₂ * Zpos x₂ * Zpos z₂)%Z as t.
remember (z₁ * Zpos y₂ * Zpos x₂)%Z as u.
rewrite Z.mul_shuffle0 in Hequ.
subst u.
rewrite <- Heqt.
apply Zplus_lt_compat_r.
clear t Heqt.
rewrite <- Zmult_assoc.
rewrite Z.mul_shuffle1.
remember (y₁ * Zpos z₂ * Zpos x₂ * Zpos z₂)%Z as t.
rewrite <- Zmult_assoc in Heqt.
rewrite Z.mul_shuffle1 in Heqt; subst t.
apply Zmult_lt_compat_r; [ idtac | assumption ].
rewrite <- Pos2Z.inj_mul.
apply Pos2Z.is_pos.
Qed.

Theorem Qminus_lt_lt_plus_r : ∀ x y z, x - y < z → x < z + y.
Proof.
intros x y z H.
apply Qplus_lt_compat_r with (z := y) in H.
rewrite <- Q_add_sub_swap, <- Q_add_sub_assoc in H.
unfold Qminus in H.
rewrite Qplus_opp_r, Q_add_0_r in H.
assumption.
Qed.

Theorem Qlt_minus_plus_lt_r : ∀ x y z, x < y - z → x + z < y.
Proof.
intros x y z H.
apply Qplus_lt_compat_r with (z := z) in H.
rewrite <- Q_add_sub_swap in H.
rewrite <- Q_add_sub_assoc in H.
unfold Qminus in H.
rewrite Qplus_opp_r, Q_add_0_r in H.
assumption.
Qed.

Theorem Qeq_shift_mult_l : ∀ x y z, ¬z == 0 → x / z == y → x == y * z.
Proof.
intros x y z Hc H.
rewrite <- H.
rewrite Q_mul_div_swap.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Theorem Qeq_shift_div_l : ∀ x y z, ¬z == 0 → x == y * z → x / z == y.
Proof.
intros x y z Hz H.
rewrite H.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Theorem Qminus_diag : ∀ x, x - x == 0.
Proof. intros; apply Qplus_opp_r. Qed.

Theorem Qminus_eq_eq_plus_r : ∀ x y z, x - y == z → x == z + y.
Proof.
intros.
rewrite <- H.
rewrite <- Q_add_sub_swap, <- Q_add_sub_assoc.
rewrite Qminus_diag, Q_add_0_r.
reflexivity.
Qed.

(* TODO: transform the above with ?= like below. *)

Theorem Zplus_cmp_compat_r : ∀ n m p,
  (n ?= m)%Z = (n + p ?= m + p)%Z.
Proof.
intros.
rewrite Zplus_comm.
replace (m + p)%Z with (p + m)%Z by apply Zplus_comm.
symmetry; apply Zcompare_plus_compat.
Qed.

Theorem Zmult_cmp_compat_r : ∀ n m p,
  (0 < p)%Z
  → (n ?= m)%Z = (n * p ?= m * p)%Z.
Proof.
intros.
apply Zmult_compare_compat_r.
apply Z.lt_gt; assumption.
Qed.

Theorem Qplus_cmp_compat_r : ∀ x y z,
  (x ?= y) = (x + z ?= y + z).
Proof.
intros (x₁, x₂) (y₁, y₂) (z₁, z₂).
unfold Qcompare; simpl.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
do 4 rewrite Z.mul_assoc.
remember (z₁ * Zpos y₂ * Zpos x₂ * Zpos z₂)%Z as t.
remember (z₁ * Zpos y₂ * Zpos x₂)%Z as u.
rewrite Z.mul_shuffle0 in Hequ.
subst u.
rewrite <- Heqt.
rewrite <- Zplus_cmp_compat_r.
clear t Heqt.
rewrite <- Zmult_assoc.
rewrite Z.mul_shuffle1.
remember (y₁ * Zpos z₂ * Zpos x₂ * Zpos z₂)%Z as t.
rewrite <- Zmult_assoc in Heqt.
rewrite Z.mul_shuffle1 in Heqt; subst t.
apply Zmult_cmp_compat_r.
rewrite <- Pos2Z.inj_mul.
apply Pos2Z.is_pos.
Qed.

Theorem Qcmp_plus_minus_cmp_r : ∀ x y z,
  (x ?= y + z) = (x - z ?= y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - z).
rewrite <- Q_add_assoc.
rewrite Qplus_opp_r, Q_add_0_r.
reflexivity.
Qed.

Theorem Qeq_plus_minus_eq_r : ∀ x y z, x == y + z → x - z == y.
Proof.
intros.
apply Qeq_alt in H; apply Qeq_alt.
rewrite <- H; symmetry; apply Qcmp_plus_minus_cmp_r.
Qed.

Theorem Qlt_plus_minus_lt_r : ∀ x y z, x < y + z → x - z < y.
Proof.
intros.
apply Qlt_alt in H; apply Qlt_alt.
rewrite <- H; symmetry; apply Qcmp_plus_minus_cmp_r.
Qed.

Theorem Qmult_cmp_compat_r : ∀ x y z,
  0 < z
  → (x ?= y) = (x * z ?= y * z).
Proof.
intros (a₁, a₂) (b₁, b₂) (c₁, c₂) H.
unfold Qcompare; simpl.
do 2 rewrite Pos2Z.inj_mul.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b₁).
rewrite <- Zmult_cmp_compat_r; [ reflexivity | idtac ].
apply Z.mul_pos_pos; [ idtac | reflexivity ].
unfold Qlt in H; simpl in H.
rewrite Zmult_1_r in H; assumption.
Qed.

Theorem Qcmp_shift_mult_l : ∀ x y z,
  0 < z
  → (x / z ?= y) = (x ?= y * z).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Q_mul_div_swap.
unfold Qdiv.
rewrite <- Q_mul_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Q_mul_1_r; reflexivity.
Qed.

Theorem Qlt_shift_mult_l : ∀ x y z, 0 < z → x / z < y → x < y * z.
Proof.
intros x y z Hc H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qcmp_shift_mult_l; assumption.
Qed.

Theorem Qcmp_shift_mult_r : ∀ x y z,
  0 < z
  → (x ?= y / z) = (x * z ?= y).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Q_mul_div_swap.
unfold Qdiv.
rewrite <- Q_mul_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Q_mul_1_r; reflexivity.
Qed.

Theorem Qlt_shift_mult_r : ∀ x y z, 0 < z → x < y / z → x * z < y.
Proof.
intros x y z Hc H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qcmp_shift_mult_r; assumption.
Qed.

Theorem Qplus_cmp_cmp_minus_r : ∀ x y z,
  (x + y ?= z) = (x ?= z - y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - y).
rewrite <- Q_add_assoc.
rewrite Qplus_opp_r, Q_add_0_r.
reflexivity.
Qed.

Theorem Qplus_lt_lt_minus_r : ∀ x y z, x + y < z → x < z - y.
Proof.
intros x y z H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qplus_cmp_cmp_minus_r.
Qed.

Theorem Qplus_cmp_compat_l : ∀ x y z,
  (x ?= y) = (z + x ?= z + y).
Proof.
intros x y z.
do 2 rewrite (Q_add_comm z).
apply Qplus_cmp_compat_r.
Qed.

Theorem list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P [a … l] → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.

Theorem Pos2Z_ne_0 : ∀ p, (Zpos p ≠ 0)%Z.
Proof.
intros p H.
pose proof (Zgt_pos_0 p) as HH.
rewrite H in HH.
apply Zgt_irrefl in HH; assumption.
Qed.

Theorem Qnum_inv : ∀ a, (0 < Qnum a)%Z → Qnum (/ a) = Zpos (Qden a).
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Z.lt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Z.lt_le_incl, Zlt_neg_0.
Qed.

Theorem Qden_inv : ∀ a, (0 < Qnum a)%Z → Zpos (Qden (/ a)) = Qnum a.
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Z.lt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Z.lt_le_incl, Zlt_neg_0.
Qed.

Theorem Qnum_minus_distr_r : ∀ a b c, a - b # c == ((a # c) - (b # c)).
Proof.
intros a b c.
unfold Qeq; simpl.
rewrite Zmult_minus_distr_r.
rewrite Zmult_plus_distr_l.
rewrite Pos2Z.inj_mul.
do 2 rewrite Zmult_assoc.
do 2 rewrite Z.mul_opp_l.
reflexivity.
Qed.

Definition pair_rec A B C (f : A → B → C) := λ xy, f (fst xy) (snd xy).

Theorem divmod_div : ∀ a b, fst (Nat.divmod a b 0 b) = (a / S b)%nat.
Proof. intros a b; reflexivity. Qed.

Theorem Pos2Nat_ne_0 : ∀ a, (Pos.to_nat a ≠ 0)%nat.
Proof.
intros a H.
pose proof Pos2Nat.is_pos a as HH.
rewrite H in HH.
revert HH; apply Nat.lt_irrefl.
Qed.
Global Hint Resolve Pos2Nat_ne_0 : Arith.

Open Scope positive_scope.

Theorem Pos_mul_mul_swap : ∀ n m p, n * m * p = n * p * m.
Proof.
intros n m p.
rewrite <- Pos.mul_assoc.
remember (m * p) as mp.
rewrite Pos.mul_comm in Heqmp; subst mp.
apply Pos.mul_assoc.
Qed.

Close Scope positive_scope.

Theorem Z2Nat_sub_min :  ∀ x y, Z.to_nat (x - Z.min x y) = Z.to_nat (x - y).
Proof.
intros x y.
destruct (Z.min_dec x y) as [H₁| H₁].
 rewrite H₁.
 rewrite Z.sub_diag.
 apply Z.min_l_iff in H₁.
 apply Z.le_sub_0 in H₁.
 destruct (x - y)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
 apply Z.nlt_ge in H₁.
 exfalso; apply H₁, Pos2Z.is_pos.

 rewrite H₁; reflexivity.
Qed.

Theorem Z2Nat_sub_min1 : ∀ x y z,
  (Z.to_nat (Z.min x y - z) + Z.to_nat (y - x))%nat =
  Z.to_nat (y - Z.min z x).
Proof.
intros x y z.
rewrite <- Z.sub_min_distr_r.
rewrite <- Z.sub_max_distr_l.
destruct (Z_le_dec (x - z) (y - z)) as [Hle₁| Hgt₁].
 rewrite Z.min_l; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hle₁.
 destruct (Z_le_dec (y - z) (y - x)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  destruct (x - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₂.
  exfalso; apply Hle₂, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := x) in Hle₁.
  rewrite Z.sub_diag in Hle₁.
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  rewrite <- Z2Nat.inj_add; [ idtac | assumption | assumption ].
  rewrite Z.add_comm, Z.add_sub_assoc, Z.sub_add.
  reflexivity.

 apply Z.nle_gt, Z.lt_le_incl in Hgt₁.
 rewrite Z.min_r; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hgt₁.
 destruct (Z_le_dec (y - z) (y - x)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  eapply Z.le_trans in Hle₂; [ idtac | eassumption ].
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  destruct (y - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₂.
  exfalso; apply Hle₂, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := x) in Hgt₁.
  rewrite Z.sub_diag in Hgt₁.
  rewrite Nat.add_comm.
  destruct (y - x)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₁.
  exfalso; apply Hgt₁, Pos2Z.is_pos.
Qed.

Theorem Z2Nat_sub_min2 : ∀ x y z,
  (Z.to_nat (Z.min x y - z) + Z.to_nat (x - y))%nat =
  Z.to_nat (x - Z.min y z).
Proof.
intros x y z.
rewrite <- Z.sub_min_distr_r.
rewrite <- Z.sub_max_distr_l.
destruct (Z_le_dec (x - z) (y - z)) as [Hle₁| Hgt₁].
 rewrite Z.min_l; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hle₁.
 destruct (Z_le_dec (x - y) (x - z)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  rewrite Z.sub_le_mono_r with (p := y) in Hle₁.
  rewrite Z.sub_diag in Hle₁.
  rewrite Nat.add_comm.
  destruct (x - y)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₁.
  exfalso; apply Hle₁, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  eapply Z.le_trans in Hgt₂; [ idtac | eassumption ].
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  destruct (x - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₂.
  exfalso; apply Hgt₂, Pos2Z.is_pos.

 apply Z.nle_gt, Z.lt_le_incl in Hgt₁.
 rewrite Z.min_r; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hgt₁.
 destruct (Z_le_dec (x - y) (x - z)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  rewrite Z.sub_le_mono_r with (p := y) in Hgt₁.
  rewrite Z.sub_diag in Hgt₁.
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  rewrite <- Z2Nat.inj_add; [ idtac | assumption | assumption ].
  rewrite Z.add_comm, Z.add_sub_assoc, Z.sub_add.
  reflexivity.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  destruct (y - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₂.
  exfalso; apply Hgt₂, Pos2Z.is_pos.
Qed.

Theorem Z2Nat_inj_mul_pos_r : ∀ n m,
  Z.to_nat (n * Zpos m) = (Z.to_nat n * Pos.to_nat m)%nat.
Proof.
intros n m.
destruct n as [| n| ]; [ reflexivity | simpl | reflexivity ].
rewrite Pos2Nat.inj_mul; reflexivity.
Qed.

Theorem Nat_sub_sub_distr : ∀ n m p, (p ≤ m → n - (m - p) = n + p - m)%nat.
Proof.
intros n m p Hpm.
rewrite Nat.add_comm.
revert n m Hpm.
induction p; intros.
 rewrite Nat.sub_0_r, Nat.add_0_l; reflexivity.

 destruct m as [| m].
  exfalso; revert Hpm; apply Nat.nle_succ_0.

  rewrite Nat.sub_succ; simpl.
  apply Nat.succ_le_mono in Hpm.
  apply IHp; assumption.
Qed.

Theorem Nat_sub_sub_comm : ∀ m n p, (m - n - p)%nat = (m - p - n)%nat.
Proof.
intros.
do 2 rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
apply eq_refl.
Qed.

Theorem Z2Nat_id_max : ∀ x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
intros x.
destruct x as [| x| x]; [ reflexivity | idtac | reflexivity ].
rewrite Z2Nat.id; [ reflexivity | apply Pos2Z.is_nonneg ].
Qed.

Theorem Nat_sub_succ_1 : ∀ n, (S n - 1 = n)%nat.
Proof. intros n; simpl; rewrite Nat.sub_0_r; reflexivity. Qed.

Theorem Z_div_pos_is_nonneg : ∀ x y, (0 <= Zpos x / Zpos y)%Z.
Proof.
intros x y.
apply Z.div_pos.
 apply Pos2Z.is_nonneg.

 apply Pos2Z.is_pos.
Qed.

Theorem Pos2Nat_to_pos : ∀ x,
  (0 < x)%Z
  → Pos.to_nat (Z.to_pos x) = Z.to_nat x.
Proof.
intros x Hx.
destruct x as [| x| x].
 exfalso; revert Hx; apply Z.lt_irrefl.

 reflexivity.

 exfalso; apply Z.nle_gt in Hx.
 apply Hx, Pos2Z.neg_is_nonpos.
Qed.

Theorem Nat_divides_l : ∀ a b, (∃ c, a = (b * c)%nat) ↔ Nat.divide b a.
Proof.
intros a b.
split; intros H.
 destruct H as (c, Hc); subst a.
 exists c; apply Nat.mul_comm.

 destruct H as (c, Hc); subst a.
 exists c; apply Nat.mul_comm.
Qed.

Theorem Nat_lcm_divides : ∀ a b c,
  (a ≠ 0
   → b ≠ 0
     → Nat.divide a c
       → Nat.divide b c
         → Nat.divide (Nat.lcm a b) c)%nat.
Proof.
intros k l c Hkp Hlp Hkm Hlm.
apply Nat_divides_l in Hkm.
apply Nat_divides_l in Hlm.
apply Nat_divides_l.
destruct Hkm as (k₁, Hk₁).
destruct Hlm as (l₁, Hl₁).
pose proof (Nat.gcd_divide_l k l) as Hk'.
pose proof (Nat.gcd_divide_r k l) as Hl'.
destruct Hk' as (k', Hk').
destruct Hl' as (l', Hl').
remember (Nat.gcd k l) as g eqn:Hg .
subst k l.
apply Nat.gcd_div_gcd in Hg.
 rewrite Nat.div_mul in Hg.
  rewrite Nat.div_mul in Hg.
   unfold Nat.lcm.
   rewrite Nat.gcd_mul_mono_r.
   rewrite Hg, Nat.mul_1_l.
   rewrite Nat.div_mul.
    rewrite Hk₁ in Hl₁.
    rewrite Nat.mul_shuffle0 in Hl₁; symmetry in Hl₁.
    rewrite Nat.mul_shuffle0 in Hl₁; symmetry in Hl₁.
    apply Nat.mul_cancel_r in Hl₁.
     exists (k₁ / l')%nat.
     rewrite <- Nat.mul_assoc.
     rewrite <- Nat.Lcm0.divide_div_mul_exact.
      replace (l' * k₁)%nat with (k₁ * l')%nat by apply Nat.mul_comm.
      rewrite Nat.div_mul.
       assumption.

       intros H; apply Hlp; subst l'; reflexivity.

      apply Nat.gauss with (m := k').
       rewrite Hl₁; exists l₁; apply Nat.mul_comm.

       rewrite Nat.gcd_comm; assumption.

     intros H1; apply Hlp; subst g; auto.

    intros H; apply Hlp; subst g; auto.

   intros H; apply Hlp; subst g; auto.

  intros H; apply Hlp; subst g; auto.

 intros H; apply Hlp; subst g; auto.
Qed.

Theorem Nat_gcd_le_l : ∀ a b, (a ≠ 0 → Nat.gcd a b ≤ a)%nat.
Proof.
intros * Haz.
specialize (Nat.gcd_divide_l a b) as Hg.
destruct Hg as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | cbn ].
apply Nat.le_add_r.
Qed.

Theorem Nat_gcd_le_r : ∀ a b, (b ≠ 0 → Nat.gcd a b ≤ b)%nat.
Proof.
intros a b Hb.
rewrite Nat.gcd_comm.
apply Nat_gcd_le_l; assumption.
Qed.

Theorem Nat_le_lcm_l : ∀ a b, (b ≠ 0 → a ≤ Nat.lcm a b)%nat.
Proof.
intros a b Hb.
remember Hb as Hab; clear HeqHab.
apply Nat_gcd_le_l with (b := a) in Hab.
rewrite Nat.gcd_comm in Hab.
unfold Nat.lcm.
eapply Nat.Div0.div_le_mono in Hab.
rewrite Nat.div_same in Hab.
 apply Nat.mul_le_mono_l with (p := a) in Hab.
 rewrite Nat.mul_1_r in Hab; assumption.

 destruct a; [ assumption | idtac ].
 intros H; apply Nat.gcd_eq_0_r in H; contradiction.
Qed.

Theorem Nat_divides_lcm_l : ∀ a b, Nat.divide a (Nat.lcm a b).
Proof.
intros a b.
unfold Nat.lcm.
exists (b / Nat.gcd a b)%nat.
apply Nat.mul_comm.
Qed.

Theorem Nat_compare_add : ∀ a b c,
  Nat.compare a b = Nat.compare (a + c) (b + c).
Proof.
intros a b c.
remember (Nat.compare a b) as c₁ eqn:Hc₁ .
remember (Nat.compare (a + c) (b + c)) as c₂ eqn:Hc₂ .
symmetry in Hc₁, Hc₂.
destruct c₁.
 apply nat_compare_eq in Hc₁; subst a.
 destruct c₂; auto.
  apply nat_compare_lt in Hc₂.
  exfalso; revert Hc₂; apply Nat.lt_irrefl.

  apply nat_compare_gt in Hc₂.
  exfalso; revert Hc₂; apply Nat.lt_irrefl.

 apply nat_compare_lt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  apply Nat.add_cancel_r in Hc₂; subst a.
  exfalso; revert Hc₁; apply Nat.lt_irrefl.

  apply nat_compare_gt in Hc₂.
  apply Nat.add_lt_mono_r in Hc₂.
  eapply Nat.lt_trans in Hc₁; eauto .
  exfalso; revert Hc₁; apply Nat.lt_irrefl.

 apply nat_compare_gt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  apply Nat.add_cancel_r in Hc₂; subst a.
  exfalso; revert Hc₁; apply Nat.lt_irrefl.

  apply nat_compare_lt in Hc₂.
  apply Nat.add_lt_mono_r in Hc₂.
  eapply Nat.lt_trans in Hc₁; eauto .
  exfalso; revert Hc₁; apply Nat.lt_irrefl.
Qed.

Theorem list_in_cons_app : ∀ A (a : A) x y l,
  List.In a [x … l ++ [y]] → List.In a [x; y … l].
Proof.
intros A a x y l H.
simpl in H; simpl.
destruct H as [| H]; [ left; assumption | right ].
revert H; clear; intros.
induction l as [| x]; intros; [ assumption | simpl ].
simpl in H.
destruct H as [H| H].
 right; left; assumption.

 apply IHl in H.
 destruct H as [H| H]; [ left | right; right ]; assumption.
Qed.

Theorem list_map_app_at : ∀ A B (g : A → B) l x,
  List.map g l ++ [g x] = List.map g (l ++ [x]).
Proof.
intros.
induction l as [| b]; [ reflexivity | simpl ].
rewrite IHl; reflexivity.
Qed.

Theorem imp_or_tauto : ∀ A B : Prop, (A → B) → A → A ∧ B.
Proof. tauto. Qed.

Theorem list_last_cons_app : ∀ A x y (l : list A) d,
  List.last [x … l ++ [y]] d = y.
Proof.
intros A x y l d.
revert x.
induction l as [| z]; [ reflexivity | intros ].
simpl in IHl; simpl.
apply IHl.
Qed.

Theorem list_nth_nil : ∀ A n (d : A), List.nth n [] d = d.
Proof. intros A n d; destruct n; reflexivity. Qed.

Theorem list_skipn_nil : ∀ A n, List.skipn n [] = ([] : list A).
Proof. intros A n; destruct n; reflexivity. Qed.

Theorem list_skipn_overflow : ∀ A n (cl : list A),
  length cl ≤ n → List.skipn n cl = [].
Proof.
intros A n cl H.
revert n H.
induction cl as [| c]; intros.
 rewrite list_skipn_nil; reflexivity.

 destruct n; [ exfalso; simpl in H; fast_omega H | simpl ].
 apply IHcl, le_S_n; assumption.
Qed.

Theorem match_id : ∀ α a (b : α), match a with O => b | S _ => b end = b.
Proof. intros α a b; destruct a; reflexivity. Qed.

Theorem fold_sub_succ_l : ∀ a b,
  (match a with 0 => S b | S c => b - c end = S b - a)%nat.
Proof. reflexivity. Qed.

Theorem Sorted_inv_1 {A} : ∀ (f : A → A → Prop) x l,
  Sorted f [x … l]
  → Sorted f l.
Proof.
intros f x l H.
apply Sorted_LocallySorted_iff in H.
apply Sorted_LocallySorted_iff.
inversion H; [ constructor | assumption ].
Qed.

Theorem Sorted_inv_2 {A} : ∀ (f : A → A → Prop) x y l,
  Sorted f [x; y … l]
  → f x y ∧ Sorted f [y … l].
Proof.
intros f x y l H.
apply Sorted_LocallySorted_iff in H.
rewrite Sorted_LocallySorted_iff.
inversion H; subst a b l0.
split; assumption.
Qed.

Theorem Sorted_minus_2nd {A} : ∀ (f : A → A → Prop) x₁ x₂ xl,
  (∀ x y z, f x y → f y z → f x z)
  → Sorted f [x₁; x₂ … xl]
    → Sorted f [x₁ … xl].
Proof.
intros f x₁ x₂ l Ht H.
apply Sorted_LocallySorted_iff.
destruct l as [| x₃]; [ constructor | intros ].
constructor.
 apply Sorted_LocallySorted_iff.
 do 2 apply Sorted_inv_1 in H.
 assumption.

 apply Sorted_inv_2 in H; destruct H as (Hlt₁, H).
 apply Sorted_inv_2 in H; destruct H as (Hlt₂, H).
 eapply Ht; eassumption.
Qed.

Theorem Sorted_minus_3rd {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ xl,
  (∀ x y z, f x y → f y z → f x z)
  → Sorted f [x₁; x₂; x₃ … xl]
    → Sorted f [x₁; x₂ … xl].
Proof.
intros f x₁ x₂ x₃ l Ht H.
apply Sorted_LocallySorted_iff.
constructor.
 apply Sorted_inv_1 in H.
 apply Sorted_LocallySorted_iff.
 eapply Sorted_minus_2nd; eassumption.

 apply Sorted_inv_2 in H; destruct H; assumption.
Qed.

Theorem Z_div_mul_swap : ∀ a b c, (b | a)%Z → (a / b * c = a * c / b)%Z.
Proof.
intros a b c H.
destruct H as (d, H).
subst a.
destruct (Z_zerop b) as [Hb| Hb].
 subst b; rewrite Z.mul_0_r.
 reflexivity.

 rewrite Z.div_mul; [ idtac | assumption ].
 rewrite Z.mul_shuffle0.
 rewrite Z.div_mul; [ idtac | assumption ].
 reflexivity.
Qed.

Theorem Z_div_reg_r : ∀ a b c,
  (c | a)%Z → (c | b)%Z → (a / c = b / c)%Z → a = b.
Proof.
intros a b c Ha Hb Hab.
destruct Ha as (d, Ha).
destruct Hb as (e, Hb).
subst a b.
destruct (Z_zerop c) as [Hc| Hc].
 subst c.
 do 2 rewrite Z.mul_0_r; reflexivity.

 rewrite Z.div_mul in Hab; [ idtac | assumption ].
 rewrite Z.div_mul in Hab; [ idtac | assumption ].
 subst d; reflexivity.
Qed.

Theorem Z_gcd_pos_r_le : ∀ a b, (Z.gcd a (Zpos b) <= Zpos b)%Z.
Proof.
intros a b.
pose proof (Z.gcd_divide_r a (Zpos b)) as Hd.
destruct Hd as (c, Hc).
rewrite Hc in |- * at 2.
rewrite Z.mul_comm.
apply Z.le_mul_diag_r.
 pose proof (Z.gcd_nonneg a (Zpos b))%Z as H.
 assert (Z.gcd a (Zpos b) ≠ 0)%Z as HH.
  intros HH; apply Z.gcd_eq_0_r in HH.
  revert HH; apply Pos2Z_ne_0.

  lia.

 rename Hc into Hd.
 destruct (Z_zerop c) as [Hc| Hc].
  subst c; simpl in Hd.
  exfalso; revert Hd; apply Pos2Z_ne_0.

  destruct c as [| c| c].
   exfalso; apply Hc; reflexivity.

   pose proof (Pos2Z.is_pos c) as Hp.
   fast_omega Hp.

   exfalso; clear Hc.
   assert (Zpos b <= 0)%Z as HH.
    rewrite Hd.
    apply Z.mul_nonpos_nonneg.
     apply Pos2Z.neg_is_nonpos.

     apply Z.gcd_nonneg.

    apply Z.nlt_ge in HH.
    apply HH, Pos2Z.is_pos.
Qed.

Theorem Qlt_sub_lt_add_l : ∀ n m p, (n - m < p)%Q ↔ (n < m + p)%Q.
Proof.
intros n m p.
destruct p as (pn, pd).
destruct m as (mn, md).
destruct n as (nn, nd).
unfold Qlt; simpl.
split; intros H.
 rewrite Z.mul_add_distr_r.
 apply Z.lt_sub_lt_add_l.
 rewrite Z.mul_shuffle0, Pos2Z.inj_mul, Z.mul_assoc.
 rewrite <- Z.mul_sub_distr_r, Z.mul_shuffle0.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite <- Z.add_opp_r.
 rewrite <- Z.mul_opp_l; assumption.

 rewrite Z.mul_add_distr_r.
 do 2 rewrite Z.mul_opp_l.
 rewrite Z.add_opp_r.
 apply Z.lt_sub_lt_add_l.
 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 rewrite Pos2Z.inj_mul, Z.mul_assoc in H.
 rewrite Z.mul_add_distr_r in H.
 remember (nn * Zpos md * Zpos pd)%Z as x.
 rewrite Z.mul_shuffle0.
 remember (mn * Zpos pd * Zpos nd)%Z as y.
 rewrite Z.mul_shuffle0; assumption.
Qed.

Theorem Qle_sub_le_add_l : ∀ n m p, (n - m <= p)%Q ↔ (n <= m + p)%Q.
Proof.
intros n m p.
destruct p as (pn, pd).
destruct m as (mn, md).
destruct n as (nn, nd).
unfold Qle; simpl.
split; intros H.
 rewrite Z.mul_add_distr_r.
 apply Z.le_sub_le_add_l.
 rewrite Z.mul_shuffle0, Pos2Z.inj_mul, Z.mul_assoc.
 rewrite <- Z.mul_sub_distr_r, Z.mul_shuffle0.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite <- Z.add_opp_r.
 rewrite <- Z.mul_opp_l; assumption.

 rewrite Z.mul_add_distr_r.
 do 2 rewrite Z.mul_opp_l.
 rewrite Z.add_opp_r.
 apply Z.le_sub_le_add_l.
 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 rewrite Pos2Z.inj_mul, Z.mul_assoc in H.
 rewrite Z.mul_add_distr_r in H.
 remember (nn * Zpos md * Zpos pd)%Z as x.
 rewrite Z.mul_shuffle0.
 remember (mn * Zpos pd * Zpos nd)%Z as y.
 rewrite Z.mul_shuffle0; assumption.
Qed.

Theorem list_nth_in : ∀ A l n (d : A),
  (n < length l)%nat
  → List.nth n l d ∈ l.
Proof.
intros A l n d Hnl.
revert n Hnl.
induction l as [| x]; intros.
 exfalso; revert Hnl; apply Nat.nlt_0_r.

 simpl in Hnl.
 destruct n; [ left; reflexivity | simpl ].
 apply Nat.succ_lt_mono in Hnl.
 right; apply IHl; assumption.
Qed.

Theorem list_fold_right_map : ∀ A B C (f : B → A → A) (g : C → B) l a,
  List.fold_right f a (List.map g l) =
  List.fold_right (λ b acc, f (g b) acc) a l.
Proof.
intros A B C f g l a.
induction l as [| x]; [ reflexivity | simpl; f_equal; assumption ].
Qed.

Theorem Z_div_gcd_r_pos : ∀ a b, (0 < b)%Z → (0 < b / Z.gcd a b)%Z.
Proof.
intros a b Hb.
pose proof (Z.gcd_divide_r a b) as H.
destruct H as (c, Hc).
rewrite Hc in |- * at 1.
rewrite Z.divide_div_mul_exact.
 rewrite Z.div_same.
  rewrite Z.mul_1_r.
  destruct c as [| c| c].
   simpl in Hc; subst b; assumption.

   apply Pos2Z.is_pos.

   remember Hb as H; clear HeqH.
   rewrite Hc in H.
   apply Z.lt_0_mul in H.
   destruct H as [H| H].
    destruct H; assumption.

    destruct H as (H, _).
    apply Z.nle_gt in H.
    exfalso; apply H, Z.gcd_nonneg.

  intros H.
  rewrite H in Hc; simpl in Hc.
  rewrite Z.mul_0_r in Hc; subst b.
  revert Hb; apply Z.lt_irrefl.

 intros H.
 rewrite H in Hc; simpl in Hc.
 rewrite Z.mul_0_r in Hc; subst b.
 revert Hb; apply Z.lt_irrefl.

 exists 1%Z.
 rewrite Z.mul_1_l; reflexivity.
Qed.

Definition Qmin x y := if Qlt_le_dec x y then x else y.

Theorem Qmin_dec : ∀ n m, {Qmin n m = n} + {Qmin n m = m}.
Proof.
intros n m.
unfold Qmin.
destruct (Qlt_le_dec n m); [ left | right ]; reflexivity.
Qed.

Theorem Qmin_comm : ∀ n m, Qmin n m == Qmin m n.
Proof.
intros n m.
unfold Qmin.
destruct (Qlt_le_dec n m) as [H₁| H₁].
 destruct (Qlt_le_dec m n) as [H₂| H₂]; [ idtac | reflexivity ].
 apply Qlt_le_weak, Qle_not_lt in H₂.
 contradiction.

 destruct (Qlt_le_dec m n) as [H₂| H₂]; [ reflexivity | idtac ].
 apply Qle_antisym; assumption.
Qed.

Theorem Qmin_l : ∀ n m, (n <= m)%Q → Qmin n m == n.
Proof.
intros n m H.
unfold Qmin.
destruct (Qlt_le_dec n m) as [| Hge]; [ reflexivity | idtac ].
apply Qle_antisym; assumption.
Qed.

Theorem List_In_nth : ∀ α a la (d : α),
  a ∈ la
  → ∃ n, a = List.nth n la d.
Proof.
intros u a la d Ha.
revert a Ha.
induction la as [| b]; intros; [ contradiction | idtac ].
simpl in Ha.
destruct Ha as [Ha| Ha].
 subst b.
 exists O; reflexivity.

 apply IHla in Ha.
 destruct Ha as (n, Ha).
 exists (S n); simpl.
 assumption.
Qed.

Global Hint Resolve Pos2Z.is_nonneg : Arith.
Global Hint Resolve Pos2Nat.is_pos : Arith.
Global Hint Resolve Pos2Z_ne_0 : Arith.

(* compatibility with old version of Coq *)

Definition omodulo x y := if Nat.eq_dec y 0%nat then 0%nat else x mod y.
Notation "x 'omod' y" := (omodulo x y) (at level 40) : nat_scope.

Theorem omod_0_l : ∀ a, 0 omod a = 0%nat.
Proof.
intros.
destruct a; [ easy | apply Nat.sub_diag ].
Qed.

Theorem omod_divide :
  ∀ a b : nat, b ≠ 0%nat → a omod b = 0%nat ↔ Nat.divide b a.
Proof.
intros * Hbz.
unfold omodulo.
destruct (Nat.eq_dec b 0) as [H| H]; [ easy | ].
apply Nat.Lcm0.mod_divide.
Qed.
