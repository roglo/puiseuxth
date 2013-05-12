(* $Id: NotInSegMisc.v,v 1.33 2013-05-12 19:02:06 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import ConvexHull.
Require Import Puiseux.

Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).

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
Lemma slope_lt₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → slope_expr (x₁, y₁) (x₂, y₂) < slope_expr (x₁, y₁) (x₃, y₃)
    → slope_expr (x₁, y₁) (x₃, y₃) < slope_expr (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ Hlt H.
rewrite Qlt_alt in H |- *; rewrite <- H.
symmetry; apply slope_cmp₁; assumption.
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
unfold slope_expr; simpl.
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus; assumption ].
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus; assumption ].
do 2 rewrite Qmult_div_swap.
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus; assumption ].
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus; assumption ].
do 4 rewrite Qmult_minus_distr_l.
do 7 rewrite Qmult_minus_distr_r.
do 4 rewrite Qminus_minus_assoc.
do 4 rewrite <- Qplus_minus_swap, <- Qplus_minus_assoc.
do 4 rewrite <- Qplus_minus_swap, <- Qplus_minus_assoc.
rewrite <- Qplus_cmp_compat_l.
rewrite Qminus_minus_swap with (y := y₂ * x₂).
do 4 rewrite Qplus_minus_assoc.
rewrite <- Qminus_cmp_compat_r.
do 3 rewrite <- Qcmp_plus_minus_cmp_r.
do 5 rewrite <- Qplus_minus_swap.
do 3 rewrite <- Qplus_cmp_cmp_minus_r.
setoid_replace (y₂ * x₃ + y₁ * x₂ + y₃ * x₁) with
 (y₁ * x₂ + y₃ * x₁ + y₂ * x₃) by ring.
setoid_replace (y₃ * x₂ + y₂ * x₁ + y₁ * x₃) with
 (y₂ * x₁ + y₃ * x₂ + y₁ * x₃) by ring.
reflexivity.
Qed.

(* 1/ two lemmas very close to each other; another lemma to factorize them,
   perhaps? the most part is normalization *)
(* 2/ perhaps could be proved shorter by 'slope_lt₁' or '₂' above? *)
Lemma ad_hoc_lt_lt₂ : ∀ i j k x y z,
  j < i < k
  → (x - z) / (i - j) < (y - x) / (k - i)
    → x + i * ((x - y) / (k - i)) < z + j * ((x - y) / (k - i)).
Proof.
intros i j k x y z (Hji, Hik) H.
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus; assumption ].
rewrite Qmult_comm, Qmult_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus; assumption ].
rewrite Qmult_comm in H.
do 2 rewrite Qmult_minus_distr_l in H.
do 4 rewrite Qmult_minus_distr_r in H.
do 2 rewrite Qminus_minus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
do 2 rewrite <- Qplus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
do 2 rewrite Qplus_assoc in H.
do 2 rewrite Qmult_div_assoc.
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Qlt_minus; assumption | idtac ].
rewrite Qmult_minus_distr_r.
rewrite Qplus_comm, Qmult_comm; apply Qnot_le_lt.
rewrite Qplus_comm, Qmult_comm; apply Qlt_not_le.
do 2 rewrite Qmult_minus_distr_l.
rewrite Qmult_minus_distr_r.
do 2 rewrite Qplus_minus_assoc.
apply Qlt_plus_minus_lt_r; rewrite <- Qplus_minus_swap.
apply Qlt_plus_minus_lt_r; rewrite Qplus_minus_swap.
do 2 rewrite <- Qplus_assoc; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; do 2 rewrite Qplus_assoc.
setoid_replace (x * i + x * k + z * i + y * j) with
 (x * k + z * i + x * i + y * j) by ring.
setoid_replace (x * j + z * k + x * i + y * i) with
 (y * i + x * j + z * k + x * i) by ring.
assumption.
Qed.

Lemma ad_hoc_lt_lt : ∀ i j k x y z,
  i < j ∧ i < k
  → (y - x) / (k - i) < (z - x) / (j - i)
    → x + i * ((x - y) / (k - i)) < z + j * ((x - y) / (k - i)).
Proof.
intros i j k x y z (Hij, Hjk) H.
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus; assumption ].
rewrite Qmult_comm, Qmult_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus; assumption ].
rewrite Qmult_comm in H.
do 2 rewrite Qmult_minus_distr_l in H.
do 4 rewrite Qmult_minus_distr_r in H.
do 2 rewrite Qminus_minus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
do 2 rewrite <- Qplus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
do 2 rewrite Qplus_assoc in H.
do 2 rewrite Qmult_div_assoc.
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Qlt_minus; assumption | idtac ].
rewrite Qmult_minus_distr_r.
rewrite Qplus_comm, Qmult_comm; apply Qnot_le_lt.
rewrite Qplus_comm, Qmult_comm; apply Qlt_not_le.
do 2 rewrite Qmult_minus_distr_l.
rewrite Qmult_minus_distr_r.
do 2 rewrite Qplus_minus_assoc.
apply Qlt_plus_minus_lt_r; rewrite <- Qplus_minus_swap.
apply Qlt_plus_minus_lt_r; rewrite Qplus_minus_swap.
do 2 rewrite <- Qplus_assoc; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; do 2 rewrite Qplus_assoc.
rewrite Qplus_comm, Qplus_assoc, Qplus_assoc; apply Qnot_le_lt.
rewrite <- Qplus_assoc, <- Qplus_assoc, Qplus_comm, Qplus_assoc.
rewrite Qplus_plus_swap; apply Qlt_not_le.
assumption.
Qed.

Section convex_hull.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma minimised_slope_le : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms <= slope_expr pt₁ pt₂.
Proof.
intros pt₁ pt₂ pts ms Hms.
revert ms Hms.
induction pts as [| pt]; intros.
 simpl in Hms.
 subst ms; simpl.
 apply Qle_refl.

 simpl in Hms.
 remember (minimise_slope pt₁ pt pts) as ms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl.
  symmetry in Heqc; apply Qeq_alt in Heqc.
  rewrite Heqc; apply Qle_refl.

  simpl.
  apply Qle_refl.

  symmetry in Heqc; apply Qgt_alt in Heqc.
  apply Qlt_le_weak; eassumption.
Qed.

Lemma minimise_slope_pts_le : ∀ j αj pt pts ms,
  minimise_slope (j, αj) pt pts = ms
  → ∀ h αh,
     (h, αh) ∈ pts
     → slope ms <= slope_expr (j, αj) (h, αh).
Proof.
intros j αj pt pts ms Hms h αh Hαh.
revert pt ms Hms h αh Hαh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hαh as [Hαh| Hαh].
 subst pt₁.
 simpl in Hms.
 remember (minimise_slope (j, αj) (h, αh) pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl.
  eapply minimised_slope_le; eassumption.

  simpl.
  eapply minimised_slope_le in Heqms₁.
  symmetry in Heqc; apply Qlt_alt in Heqc.
  apply Qlt_le_weak.
  eapply Qlt_le_trans; eassumption.

  eapply minimised_slope_le in Heqms₁.
  assumption.

 simpl in Hms.
 remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
 symmetry in Heqc.
 destruct c; subst ms.
  simpl.
  eapply IHpts; eassumption.

  simpl.
  apply Qlt_alt in Heqc.
  apply Qlt_le_weak.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply IHpts; eassumption.

  eapply IHpts; eassumption.
Qed.

Lemma end_pt_in : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → end_pt ms ∈ [pt₂ … pts].
Proof.
intros pt₁ pt₂ pts ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts as [| pt₃]; intros.
 subst ms; simpl.
 left; reflexivity.

 simpl in Hms.
 remember (minimise_slope pt₁ pt₃ pts) as ms₁.
 rename Heqms₁ into Hms₁.
 symmetry in Hms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 remember (end_pt ms) as pt.
 destruct c; subst ms; simpl in Heqpt; subst pt.
  right; eapply IHpts; eassumption.

  left; reflexivity.

  right; eapply IHpts; eassumption.
Qed.

Lemma min_slope_lt_after_k : ∀ j αj k αk pt pts ms,
  LocallySorted fst_lt pts
  → minimise_slope (j, αj) pt pts = ms
    → end_pt ms = (k, αk)
      → ∀ h αh, (h, αh) ∈ pts
        → k < h
          → slope ms < slope_expr (j, αj) (h, αh).
Proof.
intros j αj k αk pt pts ms Hsort Hms Hep h αh Hαh Hkh.
revert pt ms Hms Hep h Hαh Hkh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hαh as [Hαh| Hαh].
 subst pt₁.
 remember Hms as H; clear HeqH.
 apply end_pt_in in Hms.
 rewrite Hep in Hms.
 destruct Hms as [Hms| Hms].
  subst pt.
  simpl in H.
  remember (minimise_slope (j, αj) (h, αh) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr (j, αj) (k, αk) ?= slope ms₁) as c.
  destruct c; subst ms.
   simpl in Hep |- *.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁.
   apply Qle_not_lt in Heqms₁; contradiction.

   simpl in Hep |- *; clear Hep.
   symmetry in Heqc; apply Qlt_alt in Heqc.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   eapply minimised_slope_le; eassumption.

   symmetry in Heqc; apply Qgt_alt in Heqc.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁; simpl in Heqms₁.
   apply Qle_not_lt in Heqms₁.
   contradiction.

  destruct Hms as [Hms| Hms].
   injection Hms; clear Hms; intros; subst h αh.
   apply Qlt_irrefl in Hkh; contradiction.

   eapply LSorted_hd in Hsort; [ idtac | eassumption ].
   simpl in Hsort.
   eapply Qlt_trans in Hsort; [ idtac | eassumption ].
   apply Qlt_irrefl in Hsort; contradiction.

 simpl in Hms.
 remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl in Hep |- *.
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply LSorted_inv_2 in Hsort; destruct Hsort; assumption.

  simpl in Hep |- *.
  subst pt.
  symmetry in Heqc; apply Qlt_alt in Heqc.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimise_slope_pts_le; eassumption.

  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply LSorted_inv_2 in Hsort; destruct Hsort; assumption.
Qed.

Lemma points_after_k : ∀ n pts j αj k αk seg seg₂ hsl γ β,
  LocallySorted fst_lt pts
  → j < k
    → γ = (αj - αk) / (k - j)
      → β = αj + j * γ
        → next_ch_points n pts = [ahs (j, αj) seg; ahs (k, αk) seg₂ … hsl]
          → ∀ h αh, k < h
            → (h, αh) ∈ pts
              → β < αh + h * γ.
Proof.
intros n pts j αj k αk segjk segkx hsl γ β.
intros Hsort Hjk Hγ Hβ Hnp h αh Hkh Hαh.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst h αh.
 eapply Qlt_trans in Hkh; [ idtac | eassumption ].
 apply Qlt_irrefl in Hkh; contradiction.

 destruct Hαh as [Hαh| Hαh]; [ exfalso | idtac ].
  subst pt₁.
  symmetry in Heqms₁.
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
  rewrite Hep₁ in Heqms₁.
  apply Qle_not_lt in Heqms₁.
  contradiction.

  symmetry in Heqms₁.
  symmetry in Hep₁.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in H; [ idtac | eassumption ].
  symmetry in Hep₁.
  eapply min_slope_lt_after_k in Heqms₁; try eassumption.
   rewrite H in Heqms₁.
   subst β γ.
   apply ad_hoc_lt_lt.
    split; [ idtac | assumption ].
    destruct pt₁ as (l, αl).
    apply Qlt_trans with (y := l).
     apply LSorted_inv_2 in Hsort; destruct Hsort; assumption.

     apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
     eapply LSorted_hd in Hsort; [ idtac | eassumption ].
     assumption.

    unfold slope_expr in Heqms₁; simpl in Heqms₁.
    assumption.

   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   destruct pts as [| pt₂]; [ constructor | idtac ].
   apply LSorted_inv_2 in Hsort; destruct Hsort; assumption.
Qed.

Lemma not_seg_min_sl_lt : ∀ j αj k αk pt pts ms h αh,
  LocallySorted fst_lt [(j, αj); pt; (h, αh) … pts]
  → minimise_slope (j, αj) pt [(h, αh) … pts] = ms
    → j < h < k
      → (h, αh) ∉ seg ms
        → end_pt ms = (k, αk)
          → slope ms < slope_expr (j, αj) (h, αh).
Proof.
intros j αj k αk pt pts ms h αh Hsort Hms (Hjh, Hhk) Hseg Hep.
revert ms Hms Hseg Hep.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 remember (slope_expr (j, αj) pt ?= slope_expr (j, αj) (h, αh)) as c.
 symmetry in Heqc.
 destruct c; subst ms; simpl.
  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h αh.
  apply Qlt_irrefl in Hhk; contradiction.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc.
  assumption.

  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h αh.
  apply Qlt_irrefl in Hhk; contradiction.

 remember [pt₁ … pts] as pts₁.
 simpl in Hms.
 remember (minimise_slope (j, αj) (h, αh) pts₁) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr (j, αj) pt ?= slope ms₁) as c₁.
 symmetry in Heqc₁.
 destruct c₁; subst ms; simpl.
  simpl in Hseg, Hep.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hne, Hseg).
  subst pts₁.
  simpl in Heqms₁.
  remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl.
   simpl in Heqc₁, Hseg, Hep.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hne₂, Hseg).
   exfalso; apply Hne₂; reflexivity.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h αh.
   apply Qlt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc; assumption.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc₁.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimised_slope_le; eassumption.

  subst pts₁.
  apply Qgt_alt in Heqc₁.
  simpl in Heqms₁.
  remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl.
   simpl in Heqc₁, Hseg, Hep.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hne₂, Hseg).
   exfalso; apply Hne₂; reflexivity.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h αh.
   apply Qlt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc; assumption.
Qed.

Lemma points_between_j_and_k : ∀ n pts j αj k αk sjk skx hsl γ β,
  LocallySorted fst_lt pts
  → γ = (αj - αk) / (k - j)
    → β = αj + j * γ
      → next_ch_points n pts = [ahs (j, αj) sjk; ahs (k, αk) skx … hsl]
        → ∀ h αh, j < h < k
          → (h, αh) ∈ pts
            → (h, αh) ∉ sjk
              → β < αh + h * γ.
Proof.
intros n pts j αj k αk segjk segkx hsl γ β.
intros Hsort Hγ Hβ Hnp h αh (Hjh, Hhk) Hαh Hseg.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst h αh.
 apply Qlt_irrefl in Hjh; contradiction.

 destruct Hαh as [Hαh| Hαh].
  subst pt₁.
  symmetry in Heqms₁.
  destruct pts as [| pt₁].
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   injection Hep₁; clear Hep₁; intros; subst h αh.
   apply Qlt_irrefl in Hhk; contradiction.

   simpl in Heqms₁.
   remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
   destruct c; subst ms₁.
    simpl in Hep₁, Hseg, Hnp.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (H); exfalso; apply H; reflexivity.

    simpl in Hep₁, Hseg, Hnp.
    injection Hep₁; clear Hep₁; intros; subst h αh.
    apply Qlt_irrefl in Hhk; contradiction.

    symmetry in Hep₁.
    remember Heqms₂ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Heqc; apply Qgt_alt in Heqc.
    rewrite H in Heqc.
    subst β γ.
    apply ad_hoc_lt_lt.
     split; [ assumption | idtac ].
     eapply Qlt_trans; eassumption.

     unfold slope_expr in Heqc; simpl in Heqc.
     assumption.

  symmetry in Heqms₁.
  revert pt₁ ms₁ Hsort Heqms₁ Hep₁ Hseg Hnp.
  induction pts as [| pt₂]; intros.
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   contradiction.

   destruct Hαh as [Hαh| Hαh].
    subst pt₂.
    symmetry in Hep₁.
    remember Heqms₁ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Hep₁.
    eapply not_seg_min_sl_lt in Heqms₁; try eassumption.
     rewrite H in Heqms₁.
     subst β γ.
     apply ad_hoc_lt_lt.
      split; [ assumption | idtac ].
      eapply Qlt_trans; eassumption.

      unfold slope_expr in Heqms₁; simpl in Heqms₁.
      assumption.

     split; assumption.

    simpl in Heqms₁.
    remember (minimise_slope (j, αj) pt₂ pts) as ms₂.
    symmetry in Heqms₂.
    remember (slope_expr (j, αj) pt₁ ?= slope ms₂) as c.
    symmetry in Heqc.
    destruct c; subst ms₁.
     simpl in Hep₁, Hseg, Hnp.
     apply Decidable.not_or in Hseg.
     destruct Hseg as (Hlt₁, Hseg).
     eapply IHpts; try eassumption.
     constructor.
      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; assumption.

      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; eapply Qlt_trans; eassumption.

     simpl in Hep₁, Hseg, Hnp.
     subst pt₁.
     apply LSorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₂, Hsort).
     apply LSorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₃, Hsort).
     eapply LSorted_hd in Hsort; [ idtac | eassumption ].
     unfold fst_lt in Hlt₃.
     simpl in Hlt₃, Hsort.
     clear Hlt₂.
     eapply Qlt_trans in Hlt₃; [ idtac | eassumption ].
     eapply Qlt_trans in Hlt₃; [ idtac | eassumption ].
     apply Qlt_irrefl in Hlt₃; contradiction.

     eapply IHpts; try eassumption.
     constructor.
      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; assumption.

      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; eapply Qlt_trans; eassumption.
Qed.

Lemma sorted_hd_not_in_tl : ∀ k αj αk pts,
  LocallySorted fst_lt [(k, αj) … pts] → (k, αk) ∉ pts.
Proof.
intros k αj αk pts H.
induction pts as [| (h, αh)]; [ intros HH; contradiction | idtac ].
intros HH.
destruct HH as [HH| HH].
 injection HH; clear HH; intros; subst h αh.
 apply LSorted_inv_2 in H; destruct H as (Hlt, H).
 apply Qlt_irrefl in Hlt; assumption.

 revert HH; apply IHpts.
 apply LSorted_inv_2 in H; destruct H as (Hlt₁, H).
 destruct pts as [| pt₂]; [ constructor | idtac ].
 apply LSorted_inv_2 in H; destruct H as (Hlt₂, H).
 constructor; [ assumption | idtac ].
 eapply Qlt_trans; eassumption.
Qed.

Lemma all_fst_is_int : ∀ n cl cn pts h αh,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α n cl cn) = pts
  → (h, αh) ∈ pts
    → (Qden h = 1)%positive.
Proof.
intros n cl cn pts h αh Hpts Hαh.
revert n pts Hpts Hαh.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (is_zero_dec fld cn) as [Hz| Hnz].
  subst pts; contradiction.

  subst pts.
  destruct Hαh as [Hαh| ]; [ idtac | contradiction ].
  injection Hαh; clear Hαh; intros; subst h αh.
  reflexivity.

 simpl in Hpts.
 destruct (is_zero_dec fld c) as [Hz| Hnz].
  eapply IHcl; eassumption.

  subst pts.
  destruct Hαh as [Hαh| Hαh].
   injection Hαh; clear Hαh; intros; subst h αh.
   reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].
Qed.

Lemma eq_k_eq_αk : ∀ pts j αj k αk,
  LocallySorted fst_lt pts
  → (j, αj) ∈ pts
    → (k, αk) ∈ pts
      → j = k
        → αj = αk.
Proof.
intros pts j αj k αk Hpts Hαj Hαk Hjk.
subst j.
induction pts as [| pt]; intros; [ contradiction | idtac ].
destruct Hαj as [Hαj| Hαj]; [ subst pt | idtac ].
 destruct Hαk as [Hαk| Hαk].
  injection Hαk; clear; intros; subst αj; reflexivity.

  exfalso; revert Hαk; eapply sorted_hd_not_in_tl; eassumption.

 destruct Hαk as [Hαk| Hαk]; [ subst pt | idtac ].
  exfalso; revert Hαj; eapply sorted_hd_not_in_tl; eassumption.

  destruct pts as [| pt₂]; [ contradiction | idtac ].
  apply LSorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
  eapply IHpts; eassumption.
Qed.

Lemma fst_is_int : ∀ pol pts h αh,
  points_of_ps_polynom α fld pol = pts
  → (h, αh) ∈ pts
    → (Qden h = 1)%positive.
Proof.
intros pol pts h αh Hpts Hαh.
eapply all_fst_is_int; eassumption.
Qed.

Lemma same_den_qeq_eq : ∀ h i, Qden h = Qden i → h == i → h = i.
Proof.
intros h i Hd Hh.
unfold Qeq in Hh.
rewrite Hd in Hh.
apply Z.mul_reg_r in Hh.
 destruct h, i.
 simpl in Hd, Hh.
 subst Qden Qnum; reflexivity.

 intros H.
 pose proof (Pos2Z.is_pos (Qden i)) as HH.
 rewrite <- H in HH.
 apply Zlt_irrefl in HH; contradiction.
Qed.

Lemma same_k_same_αk : ∀ pol pts j αj k αk,
  points_of_ps_polynom α fld pol = pts
  → (j, αj) ∈ pts
    → (k, αk) ∈ pts
      → j == k
        → αj = αk.
Proof.
intros pos pts j αj k αk Hpts Hj Hk Hjk.
remember Hpts as Hsort; clear HeqHsort.
symmetry in Hsort.
unfold points_of_ps_polynom in Hsort.
apply points_of_polyn_sorted in Hsort.
eapply eq_k_eq_αk; try eassumption.
eapply all_fst_is_int in Hj; try eassumption.
eapply all_fst_is_int in Hk; try eassumption.
rewrite <- Hk in Hj.
apply same_den_qeq_eq; assumption.
Qed.

Lemma rem_pts_in : ∀ pt₁ pt₂ pts₂ ms pt,
  minimise_slope pt₁ pt₂ pts₂ = ms
  → pt ∈ rem_pts ms
    → pt ∈ pts₂.
Proof.
intros pt₁ pt₂ pts₂ ms pt Hms Hpt.
revert pt₁ pt₂ ms Hms Hpt.
induction pts₂ as [| pt₃]; intros; [ subst ms; contradiction | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts₂) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; simpl in Hpt.
 right; eapply IHpts₂; eassumption.

 assumption.

 right; eapply IHpts₂; eassumption.
Qed.

Lemma in_ch_in_pts : ∀ n pts pt s,
  ahs pt s ∈ next_ch_points n pts
  → pt ∈ pts.
Proof.
intros n pts pt s Hhs.
remember (next_ch_points n pts) as hsl.
rename Heqhsl into Hhsl.
revert n pts pt s Hhsl Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct n; [ discriminate Hhsl | idtac ].
simpl in Hhsl.
destruct pts as [| pt₁]; [ discriminate Hhsl | idtac ].
destruct pts as [| pt₂].
 injection Hhsl; clear Hhsl; intros; subst hs₁ hsl.
 destruct Hhs as [Hhs| ]; [ idtac | contradiction ].
 injection Hhs; clear Hhs; intros; subst pt s.
 left; reflexivity.

 injection Hhsl; clear Hhsl; intros.
 destruct Hhs as [Hhs| Hhs].
  subst hs₁.
  injection H0; clear H0; intros; subst pt₁.
  left; reflexivity.

  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  eapply IHhsl in H; [ idtac | eassumption ].
  destruct H as [H| H].
   apply end_pt_in in Heqms₁.
   subst pt.
   right; assumption.

   eapply rem_pts_in in H; [ idtac | eassumption ].
   right; right; assumption.
Qed.

End convex_hull.
