(* SlopeMisc.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Setoid Ring.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Slope_base.
Require Import Misc.

(* Qcmp_eq → Q.compare_eq_iff *)
(* Qeq_alt → Q.compare_eq_iff *)

Theorem Qcmp_lt_gt : ∀ a b, (a ?= b) = Lt → (b ?= a) = Gt.
Proof.
intros a b H; apply -> Q.compare_lt_iff in H; apply Q.compare_gt_iff.
assumption.
Qed.

Theorem Qcmp_gt_lt : ∀ a b, (a ?= b) = Gt → (b ?= a) = Lt.
Proof.
intros a b H; apply Q.compare_gt_iff in H; apply Q.compare_lt_iff.
assumption.
Qed.

Theorem Qcmp_sym : ∀ a b c d,
  (a ?= b) = (c ?= d)
  → (b ?= a) = (d ?= c).
Proof.
intros a b c d H.
remember (a ?= b) as cmp.
symmetry in Heqcmp, H.
destruct cmp. {
  apply -> Q.compare_eq_iff in Heqcmp.
  apply -> Q.compare_eq_iff in H.
  rewrite Heqcmp, H.
  now do 2 rewrite Q.eq_refl.
}
apply Qcmp_lt_gt in Heqcmp.
apply Qcmp_lt_gt in H.
rewrite <- H in Heqcmp; assumption.
apply Qcmp_gt_lt in Heqcmp.
apply Qcmp_gt_lt in H.
rewrite <- H in Heqcmp; assumption.
Qed.

Theorem slope_cmp_flatten : ∀ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄,
  (x₁ < x₂)%nat
  → (x₃ < x₄)%nat
    → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₃, y₃) (x₄, y₄)) =
      (y₂ * Qnat x₄ + y₁ * Qnat x₃ + y₃ * Qnat x₂ + y₄ * Qnat x₁ ?=
       y₄ * Qnat x₂ + y₃ * Qnat x₁ + y₁ * Qnat x₄ + y₂ * Qnat x₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ Hlt₁₂ Hlt₃₄.
unfold slope_expr; simpl.
rewrite Qcmp_shift_mult_r; [ idtac | apply Q.lt_0_sub, Qnat_lt; assumption ].
rewrite Q.mul_div_swap.
rewrite Qcmp_shift_mult_l; [ idtac | apply Q.lt_0_sub, Qnat_lt; assumption ].
progress unfold Qnat.
progress repeat rewrite Q.mul_sub_distr_r.
progress repeat rewrite Q.mul_sub_distr_l.
progress repeat rewrite Q.sub_sub_distr.
progress repeat rewrite <- Q.add_sub_swap.
progress repeat rewrite <- Qcmp_plus_minus_cmp_r.
progress repeat rewrite <- Q.add_sub_swap.
progress repeat rewrite <- Qplus_cmp_cmp_minus_r.
reflexivity.
Qed.

(* should use 'slope_cmp_flatten' like the other theorems, but pb with
   conditions... *)
Theorem slope_eq : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ ≠ x₂
  → x₂ ≠ x₃
    → x₃ ≠ x₁
      → slope_expr (x₁, y₁) (x₂, y₂) == slope_expr (x₁, y₁) (x₃, y₃)
        → slope_expr (x₁, y₁) (x₂, y₂) == slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ H₁₂ H₂₃ H₃₁ H.
unfold slope_expr in H |-*.
cbn in H |-*.
symmetry in H.
apply Q.mul_move_r in H. {
  rewrite Q.mul_div_swap in H.
  symmetry in H.
  apply Q.mul_move_r in H. {
    symmetry.
    apply -> Q.mul_move_r. 2: {
      intros HH; apply H₁₂.
      apply -> Q.sub_move_0_r in HH.
      apply Q.den_cancel in HH.
      now apply Nat2Z.inj in HH.
    }
    rewrite Q.mul_div_swap.
    symmetry.
    apply Q.mul_move_r. {
      intros HH; apply H₁₂.
      apply -> Q.sub_move_0_r in HH.
      apply Q.den_cancel in HH.
      now apply Nat2Z.inj in HH; symmetry in HH.
    }
    symmetry.
    progress setoid_replace ((y₃ - y₁) * (Qnat x₂ - Qnat x₁)) with
     (Qnat x₂ * y₃ - Qnat x₂ * y₁ - Qnat x₁ * y₃ + Qnat x₁ * y₁) in H by ring.
    progress setoid_replace ((y₂ - y₁) * (Qnat x₃ - Qnat x₁)) with
     (Qnat x₃ * y₂ - Qnat x₃ * y₁ - Qnat x₁ * y₂ + Qnat x₁ * y₁) in H by ring.
    apply Q.add_compat_r in H.
    progress setoid_replace ((y₃ - y₂) * (Qnat x₂ - Qnat x₁)) with
     (Qnat x₁ * y₂ + Qnat x₂ * y₃ - Qnat x₁ * y₃ - Qnat x₂ * y₂) by ring.
    progress setoid_replace ((y₂ - y₁) * (Qnat x₃ - Qnat x₂)) with
     (Qnat x₂ * y₁ + Qnat x₃ * y₂ - Qnat x₃ * y₁ - Qnat x₂ * y₂) by ring.
    apply Q.sub_compat_r.
    do 2 apply Q.add_move_r in H.
    do 4 rewrite <- Q.add_sub_swap in H.
    symmetry in H.
    do 2 apply Q.add_move_r in H.
    apply -> Q.add_move_r.
    rewrite <- Q.add_sub_swap.
    symmetry.
    apply -> Q.add_move_r.
    rewrite (Q.add_comm (Qnat x₂ * y₁)).
    rewrite Q.add_add_swap.
    rewrite <- H.
    now rewrite (Q.add_comm (Qnat x₂ * _)).
  }
  intros HH; apply H₃₁.
  apply -> Q.sub_move_0_r in HH.
  apply Q.den_cancel in HH.
  now apply Nat2Z.inj in HH.
}
intros HH; apply H₁₂.
symmetry.
apply -> Q.sub_move_0_r in HH.
apply Q.den_cancel in HH.
now apply Nat2Z.inj in HH.
Qed.

Theorem slope_cmp_norm₁₂₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  (x₁ < x₂ < x₃)%nat
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂ ?=
     Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃)%nat as Hlt₃ by (eapply Nat.lt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
rewrite <- Q.add_assoc, Q.add_comm, Q.add_assoc.
remember (y₁ * Qnat x₂ + y₃ * Qnat x₁ + y₂ * Qnat x₃ + y₁ * Qnat x₁) as t.
rewrite <- Q.add_assoc, Q.add_comm, Q.add_assoc; subst t.
...
rewrite <- Qplus_cmp_compat_r.
setoid_replace (y₁ * Qnat x₂ + y₃ * Qnat x₁ + y₂ * Qnat x₃) with
 (Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂) by ring.
setoid_replace (y₁ * Qnat x₃ + y₂ * Qnat x₁ + y₃ * Qnat x₂) with
 (Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁) by ring.
reflexivity.
Qed.

Theorem slope_cmp_norm₁₃₁₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  (x₁ < x₂ < x₃)%nat
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₂, y₂)) =
    (Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁ ?= Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₂₁₃; assumption.
Qed.

Theorem slope_cmp_norm₁₃₂₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  (x₁ < x₂ < x₃)%nat
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₂, y₂) (x₃, y₃)) =
    (Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂ ?= Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃)%nat as Hlt₃ by (eapply Nat.lt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
repeat rewrite <- Q.add_assoc.
rewrite <- Qplus_cmp_compat_l.
repeat rewrite Q.add_assoc.
setoid_replace (y₁ * Qnat x₂ + y₂ * Qnat x₃ + y₃ * Qnat x₁) with
 (Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂) by ring.
setoid_replace (y₂ * Qnat x₁ + y₁ * Qnat x₃ + y₃ * Qnat x₂) with
 (Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁) by ring.
reflexivity.
Qed.

Theorem slope_cmp_norm₂₃₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  (x₁ < x₂ < x₃)%nat
  → (slope_expr (x₂, y₂) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁ ?= Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₃₂₃; assumption.
Qed.

Theorem slope_cmp₂ : ∀ pt₁ pt₂ pt₃,
  (fst pt₁ < fst pt₂ < fst pt₃)%nat
  → (slope_expr pt₁ pt₃ ?= slope_expr pt₁ pt₂) =
    (slope_expr pt₂ pt₃ ?= slope_expr pt₁ pt₃).
Proof.
intros (x₁, y₁) (x₂, y₂) (x₃, y₃) (Hlt₁, Hlt₂).
assert (x₁ < x₃)%nat as Hlt₃ by (eapply Nat.lt_trans; eassumption).
rewrite slope_cmp_norm₁₃₁₂; [ idtac | split; assumption ].
rewrite slope_cmp_norm₂₃₁₃; [ idtac | split; assumption ].
reflexivity.
Qed.

Theorem slope_lt_1312_2313 : ∀ pt₁ pt₂ pt₃,
  (fst pt₁ < fst pt₂ < fst pt₃)%nat
  → slope_expr pt₁ pt₃ < slope_expr pt₁ pt₂
    → slope_expr pt₂ pt₃ < slope_expr pt₁ pt₃.
Proof.
intros (x₁, y₁) (x₂, y₂) (x₃, y₃) Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₂; assumption.
Qed.
