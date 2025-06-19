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

(* doesn't work, works with this small modification *)

(* *)

Definition Qnat i := Z.of_nat i # 0.

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

Theorem Q_mul_pos_pos : ∀ a b, (0 < a → 0 < b → 0 < a * b)%Q.
Proof.
intros * Hz1 Hz2.
progress unfold Q.lt in Hz1, Hz2 |-*.
cbn in Hz1, Hz2 |-*.
rewrite Z.mul_1_r in Hz1, Hz2 |-*.
now apply Z.mul_pos_pos.
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

Theorem Q_mul_le_mono_nonneg_l : ∀ a b c, (0 ≤ a → b ≤ c → a * b ≤ a * c)%Q.
Proof.
intros * Hz Hle.
progress unfold Q.le in Hz, Hle |-*.
do 2 rewrite Q.q_Den_mul.
cbn in Hz |-*.
rewrite Z.mul_1_r in Hz.
do 2 rewrite <- Z.mul_assoc.
apply Z.mul_le_mono_nonneg_l; [ easy | ].
rewrite (Z.mul_comm (q_num b)).
rewrite (Z.mul_comm (q_num c)).
do 2 rewrite <- Z.mul_assoc.
apply Z.mul_le_mono_nonneg_l; [ apply q_Den_nonneg | ].
do 2 rewrite (Z.mul_comm (q_Den _)).
easy.
Qed.

Theorem Q_mul_le_mono_nonneg_r : ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%Q.
Proof.
intros * Hz Hle.
do 2 rewrite (Q.mul_comm _ c).
now apply Q_mul_le_mono_nonneg_l.
Qed.

Theorem Q_mul_le_compat_nonneg :
  ∀ a b c d, (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%Q.
Proof.
intros * (Hz1, Hle1) (Hz2, Hle2).
apply (Q.le_trans _ (a * d)). {
  now apply Q_mul_le_mono_nonneg_l.
}
apply Q_mul_le_mono_nonneg_r; [ | easy ].
now apply (Q.le_trans _ b).
Qed.

Theorem Q_q_Den_opp : ∀ a, q_Den (- a) = q_Den a.
Proof. easy. Qed.

Theorem Q_opp_le_compat : ∀ a b, (a ≤ b ↔ - b ≤ - a)%Q.
Proof.
intros.
progress unfold Q.le; cbn.
do 2 rewrite Q_q_Den_opp.
do 2 rewrite Z.mul_opp_l.
apply Z.opp_le_compat.
Qed.

Theorem Q_mul_0_l : ∀ a, (0 * a == 0)%Q.
Proof. easy. Qed.

Theorem Q_mul_0_r : ∀ a, (a * 0 == 0)%Q.
Proof. now intros; rewrite Q.mul_comm. Qed.

Theorem Q_mul_nonneg_nonpos : ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%Q.
Proof.
intros * Ha Hb.
specialize Q_mul_le_compat_nonneg as H1.
specialize (H1 0 0 a (- b))%Q.
assert (H : (0 ≤ 0 ≤ a)%Q) by now split; [ apply Q.le_refl | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%Q). {
  split; [ apply Q.le_refl | ].
  apply Q_opp_le_compat in Hb.
  now rewrite Q.opp_0 in Hb.
}
specialize (H1 H); clear H.
rewrite Q_mul_0_l in H1.
rewrite Q.mul_opp_r in H1.
apply Q_opp_le_compat in H1.
rewrite Q.opp_involutive in H1.
now rewrite Q.opp_0 in H1.
Qed.

Theorem Q_nlt_ge_iff : ∀ a b, (¬ (a < b) ↔ b ≤ a)%Q.
Proof. intros; apply Z.nlt_ge. Qed.

Theorem Q_mul_pos_cancel_l : ∀ a b, (0 < a → 0 < a * b ↔ 0 < b)%Q.
Proof.
intros * Hz.
split; intros Hz2; [ | now apply Q_mul_pos_pos ].
apply Q.lt_iff in Hz.
apply Q.lt_iff in Hz2.
apply Q.lt_iff.
destruct Hz as (Hle, Hz).
destruct Hz2 as (Hlem, Hzm).
split. {
  apply Q_lt_eq_cases in Hlem.
  destruct Hlem as [Hlem| H]; [ | easy ].
  apply Q.nle_gt in Hlem.
  apply Q_nlt_ge_iff.
  intros H; apply Hlem;  clear Hlem.
  apply Q_mul_nonneg_nonpos; [ easy | ].
  now apply Q.lt_le_incl.
}
intros H.
rewrite <- H in Hzm.
rewrite Q_mul_0_r in Hzm.
now apply Hzm.
Qed.

Theorem Q_mul_lt_mono_pos_l :
  ∀ a b c, (0 < a)%Q → (b < c)%Q ↔ (a * b < a * c)%Q.
Proof.
intros * Hza.
split; intros Hbc. {
  apply Q.lt_0_sub.
  rewrite <- Q.mul_sub_distr_l.
  apply Q_mul_pos_pos; [ easy | ].
  now apply Q.lt_0_sub.
} {
  apply Q.lt_0_sub in Hbc.
  rewrite <- Q.mul_sub_distr_l in Hbc.
  apply Q_mul_pos_cancel_l in Hbc; [ | easy ].
  now apply Q.lt_0_sub.
}
Qed.

Theorem Q_mul_lt_mono_pos_r :
  ∀ a b c, (0 < a)%Q → (b < c)%Q ↔ (b * a < c * a)%Q.
Proof.
intros * Hza.
do 2 rewrite (Q.mul_comm _ a).
now apply Q_mul_lt_mono_pos_l.
Qed.

Theorem Q_inv_pos : ∀ a : Q, 0 < a → 0 < Q.inv a.
Proof.
intros * Hlt.
progress unfold Q.lt, Q.inv in Hlt |-*; cbn in Hlt |-*.
rewrite Z.mul_1_r in Hlt |-*.
progress unfold Z.sign.
destruct (q_num a) as [| sa va]; [ easy | cbn ].
destruct sa; [ cbn | easy ].
remember (q_Den a) as da eqn:Hda.
symmetry in Hda.
destruct da; [ now apply q_Den_neq_0 in Hda | ].
destruct b; [ easy | ].
specialize (q_Den_pos a) as H.
now rewrite Hda in H.
Qed.

Theorem Qdiv_lt_compat_r : ∀ x y z, 0 < z → x < y → x / z < y / z.
Proof.
intros * Hz Hxy.
progress unfold Q.div.
apply Q_mul_lt_mono_pos_r; [ | easy ].
now apply Q_inv_pos.
Qed.

Theorem Qdiv_minus_distr_r : ∀ x y z, (x - y) / z == x / z - y / z.
Proof.
intros x y z.
progress unfold Q.sub.
progress unfold Q.div.
rewrite Q.mul_add_distr_r.
now rewrite Q.mul_opp_l.
Qed.

Theorem Qdiv_plus_distr_r : ∀ x y z, (x + y) / z == x / z + y / z.
Proof.
intros x y z.
progress unfold Q.div.
apply Q.mul_add_distr_r.
Qed.

Theorem Qeq_opp_r : ∀ x y, x == y → - x == - y.
Proof.
intros * Heq.
now rewrite Heq.
Qed.

Theorem Qgt_0_not_0 : ∀ x, 0 < x → ¬x == 0.
Proof.
intros x Ha.
intros H.
rewrite H in Ha.
now apply Q.lt_irrefl in Ha.
Qed.

Theorem Qnat_lt : ∀ i j, (i < j)%nat ↔ Qnat i < Qnat j.
Proof.
intros i j; split; intros H. {
  unfold Qnat, Q.lt; simpl.
  do 2 rewrite q_Den_num_den.
  apply Z.mul_lt_mono_pos_r; [ easy | ].
  now apply Nat2Z.inj_lt.
} {
  unfold Q.lt in H; cbn in H.
  apply Z.mul_lt_mono_pos_r in H; [ | easy ].
  now apply Nat2Z.inj_lt in H.
}
Qed.

Theorem Qnat_succ : ∀ n a, a * Qnat (S n) == a * Qnat n + a.
Proof.
intros.
unfold Qnat.
replace a with (a * 1) at 3 by now rewrite Q.mul_1_r.
rewrite <- Q.mul_add_distr_l.
rewrite Nat2Z.inj_succ.
now rewrite Q.inv_add_distr.
Qed.

Theorem Qlt_not_0 : ∀ x y, x < y → ¬ y - x == 0.
Proof.
intros i j H HH.
apply -> Q.sub_move_0_r in HH.
now rewrite HH in H; apply Q.lt_irrefl in H.
Qed.

Theorem Qplus_div : ∀ x y z, ¬ (z == 0) → x + y / z == (x * z + y) / z.
Proof.
intros x y z Hc.
rewrite Qdiv_plus_distr_r.
now rewrite Q.mul_div.
Qed.

Theorem Zposnat2Znat : ∀ i, (0 < i)%nat → z_pos (i - 1) = Z.of_nat i.
Proof.
intros * Hi.
progress unfold z_pos.
progress unfold Z.of_nat.
destruct i; [ easy | clear Hi ].
progress f_equal.
apply Nat_sub_succ_1.
Qed.

(* *)

(* Qplus_lt_compat_r → Q.add_lt_mono_r *)
(* Qminus_lt_lt_plus_r → Q.lt_sub_lt_add_l *)
(* Qlt_minus_plus_lt_r → Q.lt_add_lt_sub_r *)
(* Qeq_shift_mult_l → Q.mul_move_l *)
(* Qminus_diag → Q.sub_diag *)
(* Qeq_shift_div_l → Q.mul_move_r *)
(* Qminus_eq_eq_plus_r → Q.add_move_r *)
(* Zplus_cmp_compat_r → Z.compare_add_cancel_r *)
(* Qlt_plus_minus_lt_r → Q.lt_sub_lt_add_r *)
(* Qplus_lt_lt_minus_r → Q.lt_add_lt_sub_r *)

Theorem Zmult_cmp_compat_r : ∀ n m p,
  (0 < p)%Z
  → (n ?= m)%Z = (n * p ?= m * p)%Z.
Proof.
intros a b c Hz.
remember (a ?= b)%Z as e eqn:He.
symmetry in He |-*.
destruct e. {
  apply Z.compare_eq_iff in He.
  apply Z.compare_eq_iff.
  now subst a.
} {
  apply -> Z.compare_lt_iff in He.
  apply Z.compare_lt_iff.
  now apply Z.mul_lt_mono_pos_r.
} {
  apply Z.compare_gt_iff in He.
  apply Z.compare_gt_iff.
  now apply Z.mul_lt_mono_pos_r.
}
Qed.

Theorem Qplus_cmp_compat_r : ∀ x y z,
  (x ?= y) = (x + z ?= y + z).
Proof.
intros a b c.
remember (a ?= b)%Q as e eqn:He.
symmetry in He |-*.
destruct e. {
  apply Q.compare_eq_iff in He.
  apply Q.compare_eq_iff.
  now rewrite He.
} {
  apply -> Q.compare_lt_iff in He.
  apply Q.compare_lt_iff.
  now apply Q.add_lt_mono_r.
} {
  apply Q.compare_gt_iff in He.
  apply Q.compare_gt_iff.
  now apply Q.add_lt_mono_r.
}
Qed.

Theorem Qcmp_plus_minus_cmp_r : ∀ x y z,
  (x ?= y + z) = (x - z ?= y).
Proof.
intros a b c.
rewrite (Qplus_cmp_compat_r _ _ (-c)).
do 2 rewrite Q.fold_sub.
now rewrite Q.add_sub.
Qed.

Theorem Qeq_plus_minus_eq_r : ∀ x y z, x == y + z → x - z == y.
Proof.
intros.
rewrite H.
apply Q.add_sub.
Qed.

Theorem Qmult_cmp_compat_r : ∀ x y z,
  0 < z
  → (x ?= y) = (x * z ?= y * z).
Proof.
intros a b c Hz.
remember (a ?= b)%Q as e eqn:He.
symmetry in He |-*.
destruct e. {
  apply Q.compare_eq_iff in He.
  apply Q.compare_eq_iff.
  now rewrite He.
} {
  apply -> Q.compare_lt_iff in He.
  apply Q.compare_lt_iff.
  now apply Q_mul_lt_mono_pos_r.
} {
  apply Q.compare_gt_iff in He.
  apply Q.compare_gt_iff.
  now apply Q_mul_lt_mono_pos_r.
}
Qed.

Theorem Qcmp_shift_mult_l : ∀ x y z,
  0 < z
  → (x / z ?= y) = (x ?= y * z).
Proof.
intros x y z Hz.
rewrite (Qmult_cmp_compat_r _ _ Hz).
rewrite Q.mul_div_swap.
rewrite Q.mul_div; [ easy | ].
intros H; rewrite H in Hz.
now apply Q.lt_irrefl in Hz.
Qed.

Theorem Qlt_shift_mult_l : ∀ x y z, 0 < z → x / z < y → x < y * z.
Proof.
intros x y z Hc H.
apply Q.compare_lt_iff in H.
apply -> Q.compare_lt_iff.
now rewrite Qcmp_shift_mult_l in H.
Qed.

Theorem Qcmp_shift_mult_r : ∀ x y z,
  0 < z
  → (x ?= y / z) = (x * z ?= y).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Q.mul_div_swap.
unfold Q.div.
rewrite <- Q.mul_assoc.
rewrite Q.mul_inv_diag_r; [ now rewrite Q.mul_1_r | ].
intros H; rewrite H in Hz.
now apply Q.lt_irrefl in Hz.
Qed.

Theorem Qlt_shift_mult_r : ∀ x y z, 0 < z → x < y / z → x * z < y.
Proof.
intros x y z Hc H.
apply Q.compare_lt_iff in H.
apply -> Q.compare_lt_iff.
rewrite <- H; symmetry; apply Qcmp_shift_mult_r; assumption.
Qed.

Theorem Q_add_opp_diag_r : ∀ a, (a + - a == 0)%Q.
Proof.
intros.
progress unfold Q.add, Q.opp, Q.eq; cbn.
rewrite q_Den_num_den.
rewrite Z.mul_1_r.
rewrite Z.mul_opp_l.
apply Z.add_opp_diag_r.
Qed.

Theorem Qplus_cmp_cmp_minus_r : ∀ x y z,
  (x + y ?= z) = (x ?= z - y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - y).
rewrite <- Q.add_assoc.
rewrite Q_add_opp_diag_r.
now rewrite Q.add_0_r.
Qed.

Theorem Qplus_cmp_compat_l : ∀ x y z,
  (x ?= y) = (z + x ?= z + y).
Proof.
intros x y z.
do 2 rewrite (Q.add_comm z).
apply Qplus_cmp_compat_r.
Qed.

Theorem list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P [a … l] → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.

Theorem Pos2Z_ne_0 : ∀ p, (z_pos p ≠ 0)%Z.
Proof. easy. Qed.

Theorem Qnum_inv : ∀ a, (0 < q_num a)%Z → q_num (a⁻¹) = z_pos (q_den a).
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Q.inv; simpl.
rewrite q_Den_num_den.
destruct a as [| sa va]; [ now apply Z.lt_irrefl in Ha | ].
destruct sa; [ | easy ].
rewrite Nat.add_1_r; cbn.
now rewrite Nat.add_0_r, Nat.add_sub.
Qed.

Theorem Qden_inv : ∀ a, (0 < q_num a)%Z → z_pos (q_den a⁻¹) = q_num a.
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Q.inv; simpl.
destruct a as [| sa va]; [ now apply Z.lt_irrefl in Ha | ].
destruct sa; [ cbn | easy ].
now rewrite Nat.add_sub.
Qed.

Definition pair_rec A B C (f : A → B → C) := λ xy, f (fst xy) (snd xy).

Theorem divmod_div : ∀ a b, fst (Nat.divmod a b 0 b) = (a / S b)%nat.
Proof. intros a b; reflexivity. Qed.

(*
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
*)

Theorem Z2Nat_sub_min :  ∀ x y, Z.to_nat (x - Z.min x y) = Z.to_nat (x - y).
Proof.
intros x y.
progress unfold Z.min.
destruct (Z.le_dec x y) as [H₁| H₁]; [ | easy ].
rewrite Z.sub_diag; cbn; symmetry.
progress unfold Z.to_nat.
remember (x - y)%Z as c eqn:Hc.
symmetry in Hc.
destruct c as [| s v]; [ easy | ].
destruct s; [ exfalso | easy ].
assert (H : (0 < z_val true v)%Z) by easy.
rewrite <- Hc in H.
apply -> Z.lt_0_sub in H.
now apply Z.nle_gt in H.
Qed.

Theorem Z2Nat_sub_min1 : ∀ x y z,
  (Z.to_nat (Z.min x y - z) + Z.to_nat (y - x))%nat =
  Z.to_nat (y - Z.min z x).
Proof.
intros x y z.
progress unfold Z.min.
destruct (Z.le_dec x y) as [Hxy| Hxy]. {
  destruct (Z.le_dec z x) as [Hzx| Hzx]. {
    progress unfold Z.to_nat.
    remember (x - z)%Z as xz eqn:Hxz.
    symmetry in Hxz.
    destruct xz as [| s v]. {
      apply -> Z.sub_move_0_r in Hxz; subst z.
      remember (y - x)%Z as yx eqn:Hyx.
      symmetry in Hyx.
      now destruct yx.
    }
Theorem Z_sub_min_distr_l :
  ∀ a b c, Z.min (a - b) (a - c) = (a - Z.max b c)%Z.
Proof.
intros.
progress unfold Z.min, Z.max.
destruct (Z.le_dec (a - b) (a - c)) as [Ha| Ha]. {
  destruct (Z.le_dec b c) as [Hbc| Hbc]; [ | easy ].
  progress f_equal.
  apply Z.sub_le_mono_l in Ha.
  now apply Z.le_antisymm.
} {
  destruct (Z.le_dec b c) as [Hbc| Hbc]; [ easy | ].
  progress f_equal.
  apply Z.nle_gt in Ha, Hbc.
  apply Z.sub_lt_mono_l in Ha.
Check Nat.lt_asymm.
Check @rngl_lt_asymm.
Theorem Z_lt_asymm : ∀ a b, (a < b)%Z → ¬ (b < a)%Z.
Proof.
intros * Hab.
... ...
  now apply Z_lt_asymm in Ha.
...
  progress f_equal.
  apply Z.sub_le_mono_l in Ha.
  now apply Z.le_antisymm.

...
Z.add_le_mono_r: ∀ a b c : Z, (a ≤ b)%Z ↔ (a + c ≤ b + c)%Z
Z.add_le_compat: ∀ a b c d : Z, (a ≤ b)%Z → (c ≤ d)%Z → (a + c ≤ b + d)%Z
Search (_ - _ ≤ _ - _)%Z.
...
Theorem Z_sub_min_distr_r :
  ∀ n m p, Z.min (n - p) (m - p) = (Z.min n m - p)%Z.
...
Theorem Z_sub_min_distr_r :
  ∀ n m p, Z.min (n - p) (m - p) = (Z.min n m - p)%Z.
...
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
