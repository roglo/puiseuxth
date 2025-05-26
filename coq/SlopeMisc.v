(* SlopeMisc.v *)

From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith QArith.

Require Import Slope_base.
Require Import Misc.

Theorem Qcmp_eq : ∀ a, (a ?= a) = Eq.
Proof.
intros a; apply Qeq_alt; reflexivity.
Qed.

Theorem Qcmp_lt_gt : ∀ a b, (a ?= b) = Lt → (b ?= a) = Gt.
Proof.
intros a b H; apply Qlt_alt in H; apply Qgt_alt; assumption.
Qed.

Theorem Qcmp_gt_lt : ∀ a b, (a ?= b) = Gt → (b ?= a) = Lt.
Proof.
intros a b H; apply Qgt_alt in H; apply Qlt_alt; assumption.
Qed.

Theorem Qcmp_sym : ∀ a b c d,
  (a ?= b) = (c ?= d)
  → (b ?= a) = (d ?= c).
Proof.
intros a b c d H.
remember (a ?= b) as cmp.
symmetry in Heqcmp, H.
destruct cmp. {
  apply Qeq_alt in Heqcmp.
  apply Qeq_alt in H.
  rewrite Heqcmp, H.
  do 2 rewrite Qcmp_eq.
  reflexivity.
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
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
rewrite Qmult_div_swap.
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
repeat rewrite Qmult_minus_distr_l.
repeat rewrite Qmult_minus_distr_r.
repeat rewrite Qminus_minus_assoc.
repeat rewrite <- Qplus_minus_swap.
repeat rewrite <- Qcmp_plus_minus_cmp_r.
repeat rewrite <- Qplus_minus_swap.
repeat rewrite <- Qplus_cmp_cmp_minus_r.
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
apply Qeq_shift_mult_l in H. {
  symmetry in H.
  rewrite Qmult_div_swap in H.
  apply Qeq_shift_mult_l in H. {
    apply Qeq_shift_div_l. {
      intros HH; apply H₁₂.
      apply Qminus_eq, Qden_cancel in HH.
      now apply Nat2Z.inj in HH.
    }
    symmetry.
    rewrite Qmult_div_swap.
    apply Qeq_shift_div_l. {
      intros HH; apply H₂₃.
      apply Qminus_eq, Qden_cancel in HH.
      now apply Nat2Z.inj in HH.
    }
    setoid_replace ((y₃ - y₁) * (Qnat x₂ - Qnat x₁)) with
     (Qnat x₂ * y₃ - Qnat x₂ * y₁ - Qnat x₁ * y₃ + Qnat x₁ * y₁) in H by ring.
    setoid_replace ((y₂ - y₁) * (Qnat x₃ - Qnat x₁)) with
     (Qnat x₃ * y₂ - Qnat x₃ * y₁ - Qnat x₁ * y₂ + Qnat x₁ * y₁) in H by ring.
    apply Qplus_inj_r in H.
    setoid_replace ((y₃ - y₂) * (Qnat x₂ - Qnat x₁)) with
     (Qnat x₁ * y₂ + Qnat x₂ * y₃ - Qnat x₁ * y₃ - Qnat x₂ * y₂) by ring.
    setoid_replace ((y₂ - y₁) * (Qnat x₃ - Qnat x₂)) with
     (Qnat x₂ * y₁ + Qnat x₃ * y₂ - Qnat x₃ * y₁ - Qnat x₂ * y₂) by ring.
    unfold Qminus at 1.
    unfold Qminus at 2.
    apply Qplus_inj_r.
    do 2 apply Qminus_eq_eq_plus_r in H.
    do 4 rewrite <- Qplus_minus_swap in H.
    symmetry in H.
    do 2 apply Qminus_eq_eq_plus_r in H.
    apply Qeq_plus_minus_eq_r.
    rewrite <- Qplus_minus_swap.
    symmetry.
    apply Qeq_plus_minus_eq_r.
    setoid_replace (Qnat x₂ * y₁ + Qnat x₃ * y₂ + Qnat x₁ * y₃) with
     (Qnat x₃ * y₂ + Qnat x₁ * y₃ + Qnat x₂ * y₁) by ring.
    rewrite H; ring.
  }
  intros HH; apply H₃₁.
  apply Qminus_eq, Qden_cancel in HH.
  now apply Nat2Z.inj in HH.
}
intros HH; apply H₁₂.
symmetry; apply Qminus_eq, Qden_cancel in HH.
now apply Nat2Z.inj in HH.
Qed.

Theorem slope_cmp_norm₁₂₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  (x₁ < x₂ < x₃)%nat
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (Qnat x₁ * y₃ + Qnat x₂ * y₁ + Qnat x₃ * y₂ ?= Qnat x₁ * y₂ + Qnat x₂ * y₃ + Qnat x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃)%nat as Hlt₃ by (eapply Nat.lt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
rewrite <- Q_add_assoc, Q_add_comm, Q_add_assoc.
remember (y₁ * Qnat x₂ + y₃ * Qnat x₁ + y₂ * Qnat x₃ + y₁ * Qnat x₁) as t.
rewrite <- Q_add_assoc, Q_add_comm, Q_add_assoc; subst t.
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
repeat rewrite <- Q_add_assoc.
rewrite <- Qplus_cmp_compat_l.
repeat rewrite Q_add_assoc.
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
