(* $Id: Slope.v,v 1.1 2013-05-15 07:54:23 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Misc.

Lemma Qcmp_eq : ∀ a, (a ?= a) = Eq.
Proof.
intros a; apply Qeq_alt; reflexivity.
Qed.

Lemma Qcmp_lt_gt : ∀ a b, (a ?= b) = Lt → (b ?= a) = Gt.
Proof.
intros a b H; apply Qlt_alt in H; apply Qgt_alt; assumption.
Qed.

Lemma Qcmp_gt_lt : ∀ a b, (a ?= b) = Gt → (b ?= a) = Lt.
Proof.
intros a b H; apply Qgt_alt in H; apply Qlt_alt; assumption.
Qed.

Lemma Qcmp_sym : ∀ a b c d,
  (a ?= b) = (c ?= d)
  → (b ?= a) = (d ?= c).
Proof.
intros a b c d H.
remember (a ?= b) as cmp.
symmetry in Heqcmp, H.
destruct cmp.
 apply Qeq_alt in Heqcmp.
 apply Qeq_alt in H.
 rewrite Heqcmp, H.
 do 2 rewrite Qcmp_eq.
 reflexivity.

 apply Qcmp_lt_gt in Heqcmp.
 apply Qcmp_lt_gt in H.
 rewrite <- H in Heqcmp; assumption.

 apply Qcmp_gt_lt in Heqcmp.
 apply Qcmp_gt_lt in H.
 rewrite <- H in Heqcmp; assumption.
Qed.

Lemma slope_cmp_flatten : ∀ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄,
  x₁ < x₂
  → x₃ < x₄
    → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₃, y₃) (x₄, y₄)) =
      (y₂ * x₄ + y₁ * x₃ + y₃ * x₂ + y₄ * x₁ ?=
       y₄ * x₂ + y₃ * x₁ + y₁ * x₄ + y₂ * x₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ Hlt₁₂ Hlt₃₄.
unfold slope_expr; simpl.
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus; assumption ].
rewrite Qmult_div_swap.
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus; assumption ].
repeat rewrite Qmult_minus_distr_l.
repeat rewrite Qmult_minus_distr_r.
repeat rewrite Qminus_minus_assoc.
repeat rewrite <- Qplus_minus_swap.
repeat rewrite <- Qcmp_plus_minus_cmp_r.
repeat rewrite <- Qplus_minus_swap.
repeat rewrite <- Qplus_cmp_cmp_minus_r.
reflexivity.
Qed.

(* should use 'slope_cmp_flatten' like the other lemmas, but pb with
   conditions... *)
Lemma slope_eq : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  ¬x₁ == x₂
  → ¬x₂ == x₃
    → ¬x₃ == x₁
      → slope_expr (x₁, y₁) (x₂, y₂) == slope_expr (x₁, y₁) (x₃, y₃)
        → slope_expr (x₁, y₁) (x₂, y₂) == slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ H₁₂ H₂₃ H₃₁ H.
unfold slope_expr in H |-*.
apply Qeq_shift_mult_l in H.
 symmetry in H.
 rewrite Qmult_div_swap in H.
 apply Qeq_shift_mult_l in H.
  apply Qeq_shift_div_l.
   intros HH; apply H₁₂.
   symmetry; apply Qminus_eq; assumption.

   symmetry.
   rewrite Qmult_div_swap.
   apply Qeq_shift_div_l.
    intros HH; apply H₂₃.
    symmetry; apply Qminus_eq; assumption.

    setoid_replace ((y₃ - y₁) * (x₂ - x₁)) with
     (x₂ * y₃ - x₂ * y₁ - x₁ * y₃ + x₁ * y₁) in H by ring.
    setoid_replace ((y₂ - y₁) * (x₃ - x₁)) with
     (x₃ * y₂ - x₃ * y₁ - x₁ * y₂ + x₁ * y₁) in H by ring.
    apply Qplus_inj_r in H.
    setoid_replace ((y₃ - y₂) * (x₂ - x₁)) with
     (x₁ * y₂ + x₂ * y₃ - x₁ * y₃ - x₂ * y₂) by ring.
    setoid_replace ((y₂ - y₁) * (x₃ - x₂)) with
     (x₂ * y₁ + x₃ * y₂ - x₃ * y₁ - x₂ * y₂) by ring.
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
    setoid_replace (x₂ * y₁ + x₃ * y₂ + x₁ * y₃) with
     (x₃ * y₂ + x₁ * y₃ + x₂ * y₁) by ring.
    rewrite H; ring.

  intros HH; apply H₃₁.
  apply Qminus_eq; assumption.

 intros HH; apply H₁₂.
 symmetry; apply Qminus_eq; assumption.
Qed.

Lemma slope_cmp_norm₁₂₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (x₁ * y₃ + x₂ * y₁ + x₃ * y₂ ?= x₁ * y₂ + x₂ * y₃ + x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
rewrite <- Qplus_assoc, Qplus_comm, Qplus_assoc.
remember (y₁ * x₂ + y₃ * x₁ + y₂ * x₃ + y₁ * x₁) as t.
rewrite <- Qplus_assoc, Qplus_comm, Qplus_assoc; subst t.
rewrite <- Qplus_cmp_compat_r.
setoid_replace (y₁ * x₂ + y₃ * x₁ + y₂ * x₃) with
 (x₁ * y₃ + x₂ * y₁ + x₃ * y₂) by ring.
setoid_replace (y₁ * x₃ + y₂ * x₁ + y₃ * x₂) with
 (x₁ * y₂ + x₂ * y₃ + x₃ * y₁) by ring.
reflexivity.
Qed.

Lemma slope_cmp_norm₁₃₁₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₂, y₂)) =
    (x₁ * y₂ + x₂ * y₃ + x₃ * y₁ ?= x₁ * y₃ + x₂ * y₁ + x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₂₁₃; assumption.
Qed.

Lemma slope_cmp_norm₁₂₂₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₂, y₂) (x₃, y₃)) =
    (x₁ * y₃ + x₂ * y₁ + x₃ * y₂ ?= x₁ * y₂ + x₂ * y₃ + x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
rewrite Qplus_comm, Qplus_assoc, Qplus_assoc.
rewrite <- Qplus_cmp_compat_r.
setoid_replace (y₃ * x₁ + y₂ * x₃ + y₁ * x₂) with
 (x₁ * y₃ + x₂ * y₁ + x₃ * y₂) by ring.
setoid_replace (y₃ * x₂ + y₂ * x₁ + y₁ * x₃) with
 (x₁ * y₂ + x₂ * y₃ + x₃ * y₁) by ring.
reflexivity.
Qed.

Lemma slope_cmp_norm₂₃₁₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
 → (slope_expr (x₂, y₂) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₂, y₂)) =
   (x₁ * y₂ + x₂ * y₃ + x₃ * y₁ ?= x₁ * y₃ + x₂ * y₁ + x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₂₂₃; assumption.
Qed.

Lemma slope_cmp_norm₁₃₂₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₂, y₂) (x₃, y₃)) =
    (x₁ * y₃ + x₂ * y₁ + x₃ * y₂ ?= x₁ * y₂ + x₂ * y₃ + x₃ * y₁).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_flatten; [ idtac | assumption | assumption ].
repeat rewrite <- Qplus_assoc.
rewrite <- Qplus_cmp_compat_l.
repeat rewrite Qplus_assoc.
setoid_replace (y₁ * x₂ + y₂ * x₃ + y₃ * x₁) with
 (x₁ * y₃ + x₂ * y₁ + x₃ * y₂) by ring.
setoid_replace (y₂ * x₁ + y₁ * x₃ + y₃ * x₂) with
 (x₁ * y₂ + x₂ * y₃ + x₃ * y₁) by ring.
reflexivity.
Qed.

Lemma slope_cmp_norm₂₃₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₂, y₂) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (x₁ * y₂ + x₂ * y₃ + x₃ * y₁ ?= x₁ * y₃ + x₂ * y₁ + x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₃₂₃; assumption.
Qed.

Lemma slope_cmp₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₂, y₂) (x₃, y₃)).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_norm₁₂₁₃; [ idtac | split; assumption ].
rewrite slope_cmp_norm₁₃₂₃; [ idtac | split; assumption ].
reflexivity.
Qed.
Lemma slope_lt₁₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₁, y₁) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₁; assumption.
Qed.
Lemma slope_lt₁₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₂, y₂) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₁, y₁) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
apply slope_cmp₁; assumption.
Qed.

Lemma slope_cmp₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₂, y₂)) =
    (slope_expr (x₂, y₂) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₃, y₃)).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_norm₁₃₁₂; [ idtac | split; assumption ].
rewrite slope_cmp_norm₂₃₁₃; [ idtac | split; assumption ].
reflexivity.
Qed.
Lemma slope_lt₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₁, y₁) (x₂, y₂)
    → slope_expr (x₂, y₂) (x₃, y₃) < slope_expr (x₁, y₁) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₂; assumption.
Qed.

Lemma slope_cmp₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₂, y₂) (x₃, y₃)) =
    (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₂, y₂) (x₃, y₃)).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_norm₁₂₂₃; [ idtac | split; assumption ].
rewrite slope_cmp_norm₁₃₂₃; [ idtac | split; assumption ].
reflexivity.
Qed.
Lemma slope_lt₃₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₂, y₂) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₃; assumption.
Qed.
Lemma slope_lt₃₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₂, y₂) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
apply slope_cmp₃; assumption.
Qed.

Lemma slope_cmp₄ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₂, y₂) (x₃, y₃)).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_norm₁₂₁₃; [ idtac | split; assumption ].
rewrite slope_cmp_norm₁₂₂₃; [ idtac | split; assumption ].
reflexivity.
Qed.
Lemma slope_lt₄₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₁, y₁) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₄; assumption.
Qed.
Lemma slope_lt₄₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₂, y₂) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₁, y₁) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
apply slope_cmp₄; assumption.
Qed.
