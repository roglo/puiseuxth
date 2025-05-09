(* SlopeMisc.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8.

Require Import QGArith.
Require Import Slope_base.
Require Import Misc.

Theorem QG_cmp_eq : ∀ a, (a ?= a) = Eq.
Proof.
intros a; apply QG_compare_eq_iff; reflexivity.
Qed.

Theorem QG_cmp_lt_gt : ∀ a b, (a ?= b) = Lt → (b ?= a) = Gt.
Proof.
now intros a b H; apply QG_compare_lt_iff in H; apply QG_compare_gt_iff.
Qed.

Theorem QG_cmp_gt_lt : ∀ a b, (a ?= b) = Gt → (b ?= a) = Lt.
Proof.
now intros a b H; apply QG_compare_gt_iff in H; apply QG_compare_lt_iff.
Qed.

Theorem Qcmp_sym : ∀ a b c d,
  (a ?= b) = (c ?= d)
  → (b ?= a) = (d ?= c).
Proof.
intros a b c d H.
remember (a ?= b) as cmp.
symmetry in Heqcmp, H.
destruct cmp. {
  apply QG_compare_eq_iff in Heqcmp.
  apply QG_compare_eq_iff in H.
  rewrite Heqcmp, H.
  do 2 rewrite QG_cmp_eq.
  reflexivity.
}
apply QG_cmp_lt_gt in Heqcmp.
apply QG_cmp_lt_gt in H.
rewrite <- H in Heqcmp; assumption.
apply QG_cmp_gt_lt in Heqcmp.
apply QG_cmp_gt_lt in H.
rewrite <- H in Heqcmp; assumption.
Qed.

Theorem slope_cmp_flatten : ∀ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄,
  x₁ < x₂
  → x₃ < x₄
    → (slope_expr (x₁, y₁) (x₂, y₂) ?= slope_expr (x₃, y₃) (x₄, y₄)) =
      (y₂ * x₄ + y₁ * x₃ + y₃ * x₂ + y₄ * x₁ ?=
       y₄ * x₂ + y₃ * x₁ + y₁ * x₄ + y₂ * x₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ Hlt₁₂ Hlt₃₄.
unfold slope_expr; simpl.
rewrite QG_cmp_shift_mul_r; [ | now apply QG_lt_0_sub ].
rewrite QG_mul_div_swap.
rewrite QG_cmp_shift_mul_l; [ | now apply QG_lt_0_sub ].
repeat rewrite QG_mul_sub_distr_l.
repeat rewrite QG_mul_sub_distr_r.
repeat rewrite QG_sub_sub_distr.
repeat rewrite <- QG_add_sub_swap.
repeat rewrite QG_cmp_shift_add_l.
repeat rewrite <- QG_add_sub_swap.
repeat rewrite QG_cmp_shift_add_r.
rewrite QG_add_add_swap.
rewrite (QG_add_add_swap (y₄ * x₂ + _)).
easy.
Qed.

(* should use 'slope_cmp_flatten' like the other theorems, but pb with
   conditions... *)
Theorem slope_eq : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ ≠ x₂
  → x₂ ≠ x₃
  → x₃ ≠ x₁
  → slope_expr (x₁, y₁) (x₂, y₂) = slope_expr (x₁, y₁) (x₃, y₃)
  → slope_expr (x₁, y₁) (x₂, y₂) = slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ H₁₂ H₂₃ H₃₁ H.
unfold slope_expr in H |-*.
cbn in H |-*.
Search (_ / _ = _ → _ = _ * _).
Search (_ / _ = _ ↔ _ = _ * _).
Check QG_mul_move_r.
...
Search (_ = _ * _ ↔ _ / _ = _).
Search (_ / _ = _).
...
Theorem Qeq_shift_mult_l : ∀ x y z, ¬z == 0 → x / z == y → x == y * z.
Proof.
intros x y z Hc H.
rewrite <- H.
rewrite Qmult_div_swap.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.
Check Qeq_shift_mult_l.
...
apply Qeq_shift_mult_l in H. {
  symmetry in H.
  rewrite Qmult_div_swap in H.
  apply Qeq_shift_mult_l in H. {
    apply Qeq_shift_div_l. {
      intros HH; apply H₁₂.
      symmetry; apply Qminus_eq; assumption.
    }
    symmetry.
    rewrite Qmult_div_swap.
    apply Qeq_shift_div_l. {
      intros HH; apply H₂₃.
      symmetry; apply Qminus_eq; assumption.
    }
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
  }
  intros HH; apply H₃₁.
  apply Qminus_eq; assumption.
}
intros HH; apply H₁₂.
symmetry; apply Qminus_eq; assumption.
Qed.

Theorem slope_cmp_norm₁₂₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
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

Theorem slope_cmp_norm₁₃₁₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₁, y₁) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₂, y₂)) =
    (x₁ * y₂ + x₂ * y₃ + x₃ * y₁ ?= x₁ * y₃ + x₂ * y₁ + x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₂₁₃; assumption.
Qed.

Theorem slope_cmp_norm₁₃₂₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
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

Theorem slope_cmp_norm₂₃₁₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (slope_expr (x₂, y₂) (x₃, y₃) ?= slope_expr (x₁, y₁) (x₃, y₃)) =
    (x₁ * y₂ + x₂ * y₃ + x₃ * y₁ ?= x₁ * y₃ + x₂ * y₁ + x₃ * y₂).
Proof.
intros; apply Qcmp_sym, slope_cmp_norm₁₃₂₃; assumption.
Qed.

Theorem slope_cmp₂ : ∀ pt₁ pt₂ pt₃,
  fst pt₁ < fst pt₂ < fst pt₃
  → (slope_expr pt₁ pt₃ ?= slope_expr pt₁ pt₂) =
    (slope_expr pt₂ pt₃ ?= slope_expr pt₁ pt₃).
Proof.
intros (x₁, y₁) (x₂, y₂) (x₃, y₃) (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
rewrite slope_cmp_norm₁₃₁₂; [ idtac | split; assumption ].
rewrite slope_cmp_norm₂₃₁₃; [ idtac | split; assumption ].
reflexivity.
Qed.

Theorem slope_lt_1312_2313 : ∀ pt₁ pt₂ pt₃,
  fst pt₁ < fst pt₂ < fst pt₃
  → slope_expr pt₁ pt₃ < slope_expr pt₁ pt₂
    → slope_expr pt₂ pt₃ < slope_expr pt₁ pt₃.
Proof.
intros (x₁, y₁) (x₂, y₂) (x₃, y₃) Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₂; assumption.
Qed.
