(* $Id: NotInSegMisc.v,v 1.15 2013-05-09 14:12:58 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import ConvexHull.
Require Import Puiseux.

Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).

Definition gen_slope pt₁ pt₂ := (snd pt₂ - snd pt₁) / (fst pt₂ - fst pt₁).

Lemma slope_eq : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  ¬x₁ == x₂
  → ¬x₂ == x₃
    → ¬x₃ == x₁
      → gen_slope (x₁, y₁) (x₂, y₂) == gen_slope (x₁, y₁) (x₃, y₃)
        → gen_slope (x₁, y₁) (x₂, y₂) == gen_slope (x₂, y₂) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ H₁₂ H₂₃ H₃₁ H.
unfold gen_slope in H |-*.
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

Lemma Qmult_cmp_compat_r : ∀ x y z,
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

Lemma Qcmp_shift_mult_l : ∀ x y z,
  0 < z
  → (x / z ?= y) = (x ?= y * z).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Qmult_div_swap.
unfold Qdiv.
rewrite <- Qmult_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Qmult_1_r; reflexivity.
Qed.

Lemma Qcmp_shift_mult_r : ∀ x y z,
  0 < z
  → (x ?= y / z) = (x * z ?= y).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Qmult_div_swap.
unfold Qdiv.
rewrite <- Qmult_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Qmult_1_r; reflexivity.
Qed.

Lemma Qplus_cmp_cmp_minus_r : ∀ x y z,
  (x + y ?= z) = (x ?= z - y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - y).
rewrite <- Qplus_assoc.
rewrite Qplus_opp_r, Qplus_0_r.
reflexivity.
Qed.

Lemma Qplus_cmp_compat_l : ∀ x y z,
  (x ?= y) = (z + x ?= z + y).
Proof.
intros x y z.
do 2 rewrite (Qplus_comm z).
apply Qplus_cmp_compat_r.
Qed.

Lemma slope_cmp₁ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → (gen_slope (x₁, y₁) (x₂, y₂) ?= gen_slope (x₁, y₁) (x₃, y₃)) =
    (gen_slope (x₁, y₁) (x₃, y₃) ?= gen_slope (x₂, y₂) (x₃, y₃)).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
unfold gen_slope; simpl.
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus; assumption ].
rewrite Qcmp_shift_mult_r; [ idtac | apply Qlt_minus; assumption ].
do 2 rewrite Qmult_div_swap.
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus; assumption ].
rewrite Qcmp_shift_mult_l; [ idtac | apply Qlt_minus; assumption ].
do 4 rewrite Qmult_minus_distr_l.
do 7 rewrite Qmult_minus_distr_r.
do 4 rewrite Qminus_minus_assoc.
rewrite <- Qplus_cmp_compat_r.
do 4 rewrite <- Qplus_minus_swap, <- Qplus_minus_assoc.
rewrite <- Qplus_cmp_compat_l.
do 4 rewrite <- Qcmp_plus_minus_cmp_r.
do 8 rewrite <- Qplus_minus_swap.
do 4 rewrite <- Qplus_cmp_cmp_minus_r.
rewrite Qplus_plus_swap, Qplus_comm, Qplus_assoc.
symmetry; rewrite Qplus_plus_swap.
remember (y₁ * x₂ + y₂ * x₃ + y₃ * x₁) as t.
do 2 rewrite Qplus_comm, Qplus_assoc.
reflexivity.
Qed.

(*
Lemma slope_lt₃ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → gen_slope (x₁, y₁) (x₂, y₂) < gen_slope (x₂, y₂) (x₃, y₃)
    → gen_slope (x₁, y₁) (x₂, y₂) < gen_slope (x₁, y₁) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
intros H.
bbb.
*)

Lemma slope_lt₂ : ∀ x₁ y₁ x₂ y₂ x₃ y₃,
  x₁ < x₂ < x₃
  → gen_slope (x₁, y₁) (x₃, y₃) < gen_slope (x₁, y₁) (x₂, y₂)
    → gen_slope (x₂, y₂) (x₃, y₃) < gen_slope (x₁, y₁) (x₃, y₃).
Proof.
intros x₁ y₁ x₂ y₂ x₃ y₃ (Hlt₁, Hlt₂).
assert (x₁ < x₃) as Hlt₃ by (eapply Qlt_trans; eassumption).
intros H.
unfold gen_slope in H |-*.
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus; assumption ].
apply Qlt_shift_div_r; [ apply Qlt_minus; assumption | idtac ].
rewrite Qmult_comm, Qmult_div_assoc in H |- *.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus; assumption ].
apply Qlt_shift_div_l; [ apply Qlt_minus; assumption | idtac ].
setoid_replace ((x₂ - x₁) * (y₃ - y₁)) with
 (x₂ * y₃ - x₂ * y₁ - x₁ * y₃ + x₁ * y₁) in H by ring.
setoid_replace ((y₂ - y₁) * (x₃ - x₁)) with
 (x₃ * y₂ - x₃ * y₁ - x₁ * y₂ + x₁ * y₁) in H by ring.
setoid_replace ((y₃ - y₂) * (x₃ - x₁)) with
 (x₁ * y₂ - x₃ * y₂ - x₁ * y₃ + x₃ * y₃) by ring.
setoid_replace ((x₃ - x₂) * (y₃ - y₁)) with
 (x₂ * y₁ - x₃ * y₁ - x₂ * y₃ + x₃ * y₃) by ring.
apply Qplus_lt_l in H.
apply Qplus_lt_l.
apply Qminus_lt_lt_plus_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
rewrite <- Qplus_minus_swap in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
apply Qlt_plus_minus_lt_r.
apply Qlt_plus_minus_lt_r.
do 2 rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r.
do 2 rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r.
setoid_replace (x₁ * y₂ + x₂ * y₃ + x₃ * y₁) with
 (x₂ * y₃ + x₁ * y₂ + x₃ * y₁) by ring.
setoid_replace (x₂ * y₁ + x₁ * y₃ + x₃ * y₂) with
 (x₃ * y₂ + x₁ * y₃ + x₂ * y₁) by ring.
assumption.
Qed.

(* 1/ two lemmas very close to each other; another lemma to factorize them,
   perhaps? the most part is normalization *)
(* 2/ perhaps could be proved shorter by 'slope_lt₁' or '₂' above? *)
Lemma ad_hoc_lt_lt₂ : ∀ i j k x y z,
  (j < i < k)%nat
  → (x - z) / (Qnat i - Qnat j) < (y - x) / (Qnat k - Qnat i)
    → x + Qnat i * ((x - y) / Qnat (k - i)) <
      z + Qnat j * ((x - y) / Qnat (k - i)).
Proof.
intros i j k x y z (Hji, Hik) H.
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
rewrite Qmult_comm, Qmult_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
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
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Qnat_lt_0_lt; assumption | idtac ].
rewrite Qnat_minus_distr; [ idtac | apply lt_le_weak; assumption ].
rewrite Qplus_comm, Qmult_comm; apply Qnot_le_lt.
rewrite Qplus_comm, Qmult_comm; apply Qlt_not_le.
do 2 rewrite Qmult_minus_distr_l.
do 2 rewrite Qmult_minus_distr_r.
do 2 rewrite Qplus_minus_assoc.
apply Qlt_plus_minus_lt_r; rewrite <- Qplus_minus_swap.
apply Qlt_plus_minus_lt_r; rewrite Qplus_minus_swap.
do 2 rewrite <- Qplus_assoc; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; do 2 rewrite Qplus_assoc.
setoid_replace (x * Qnat i + x * Qnat k + z * Qnat i + y * Qnat j) with
 (x * Qnat k + z * Qnat i + x * Qnat i + y * Qnat j) by ring.
setoid_replace (x * Qnat j + z * Qnat k + x * Qnat i + y * Qnat i) with
 (y * Qnat i + x * Qnat j + z * Qnat k + x * Qnat i) by ring.
assumption.
Qed.

Lemma ad_hoc_lt_lt : ∀ i j k x y z,
  (i < j ∧ i < k)%nat
  → (y - x) / (Qnat k - Qnat i) < (z - x) / (Qnat j - Qnat i)
    → x + Qnat i * ((x - y) / Qnat (k - i)) <
      z + Qnat j * ((x - y) / Qnat (k - i)).
Proof.
intros i j k x y z (Hij, Hjk) H.
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
rewrite Qmult_comm, Qmult_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
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
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Qnat_lt_0_lt; assumption | idtac ].
rewrite Qnat_minus_distr; [ idtac | apply lt_le_weak; assumption ].
rewrite Qplus_comm, Qmult_comm; apply Qnot_le_lt.
rewrite Qplus_comm, Qmult_comm; apply Qlt_not_le.
do 2 rewrite Qmult_minus_distr_l.
do 2 rewrite Qmult_minus_distr_r.
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
  minimise_slope α pt₁ pt₂ pts = ms
  → slope ms <= slope_expr α pt₁ pt₂.
Proof.
intros pt₁ pt₂ pts ms Hms.
revert ms Hms.
induction pts as [| pt]; intros.
 simpl in Hms.
 subst ms; simpl.
 apply Qle_refl.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt pts) as ms₁.
 remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl.
  symmetry in Heqc; apply Qeq_alt in Heqc.
  rewrite Heqc; apply Qle_refl.

  simpl.
  apply Qle_refl.

  symmetry in Heqc; apply Qgt_alt in Heqc.
  apply Qlt_le_weak; eassumption.
Qed.

Lemma minimise_slope_pts_le : ∀ j jps pt pts ms,
  minimise_slope α (j, jps) pt pts = ms
  → ∀ h hps,
     (h, hps) ∈ pts
     → slope ms <= slope_expr α (j, jps) (h, hps).
Proof.
intros j jps pt pts ms Hms h hps Hhps.
revert pt ms Hms h hps Hhps.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 simpl in Hms.
 remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
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
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
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
  minimise_slope α pt₁ pt₂ pts = ms
  → end_pt ms ∈ [pt₂ … pts].
Proof.
intros pt₁ pt₂ pts ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts as [| pt₃]; intros.
 subst ms; simpl.
 left; reflexivity.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
 rename Heqms₁ into Hms₁.
 symmetry in Hms₁.
 remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 remember (end_pt ms) as pt.
 destruct c; subst ms; simpl in Heqpt; subst pt.
  right; eapply IHpts; eassumption.

  left; reflexivity.

  right; eapply IHpts; eassumption.
Qed.

Lemma min_slope_lt_after_k : ∀ j jps k kps pt pts ms,
  LocallySorted fst_lt pts
  → minimise_slope α (j, jps) pt pts = ms
    → end_pt ms = (k, kps)
      → ∀ h hps, (h, hps) ∈ pts
        → (k < h)%nat
          → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms Hsort Hms Hep h hps Hhps Hkh.
revert pt ms Hms Hep h Hhps Hkh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 remember Hms as H; clear HeqH.
 apply end_pt_in in Hms.
 rewrite Hep in Hms.
 destruct Hms as [Hms| Hms].
  subst pt.
  simpl in H.
  remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α (j, jps) (k, kps) ?= slope ms₁) as c.
  destruct c; subst ms.
   simpl in Hep |- *.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁.
   apply le_not_lt in Heqms₁; contradiction.

   simpl in Hep |- *; clear Hep.
   symmetry in Heqc; apply Qlt_alt in Heqc.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   eapply minimised_slope_le; eassumption.

   symmetry in Heqc; apply Qgt_alt in Heqc.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁; simpl in Heqms₁.
   apply le_not_lt in Heqms₁.
   contradiction.

  destruct Hms as [Hms| Hms].
   injection Hms; clear Hms; intros; subst h hps.
   apply lt_irrefl in Hkh; contradiction.

   eapply LSorted_hd in Hsort; [ idtac | eassumption ].
   simpl in Hsort.
   eapply lt_trans in Hsort; [ idtac | eassumption ].
   apply lt_irrefl in Hsort; contradiction.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
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

Lemma points_after_k : ∀ n pts j jps k kps seg seg₂ hsl γ β,
  LocallySorted fst_lt pts
  → (j < k)%nat
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → next_ch_points α n pts = [ahs (j, jps) seg; ahs (k, kps) seg₂ … hsl]
          → ∀ h hps, (k < h)%nat
            → (h, hps) ∈ pts
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx hsl γ β.
intros Hsort Hjk Hγ Hβ Hnp h hps Hkh Hhps.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hhps as [Hhps| Hhps].
 injection Hhps; clear Hhps; intros; subst h hps.
 eapply lt_trans in Hkh; [ idtac | eassumption ].
 apply lt_irrefl in Hkh; contradiction.

 destruct Hhps as [Hhps| Hhps]; [ exfalso | idtac ].
  subst pt₁.
  symmetry in Heqms₁.
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
  rewrite Hep₁ in Heqms₁.
  apply le_not_lt in Heqms₁.
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
    destruct pt₁ as (l, lps).
    apply lt_trans with (m := l).
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

Lemma not_seg_min_sl_lt : ∀ j jps k kps pt pts ms h hps,
  LocallySorted fst_lt [(j, jps); pt; (h, hps) … pts]
  → minimise_slope α (j, jps) pt [(h, hps) … pts] = ms
    → (j < h <  k)%nat
      → (h, hps) ∉ seg ms
        → end_pt ms = (k, kps)
          → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms h hps Hsort Hms (Hjh, Hhk) Hseg Hep.
revert ms Hms Hseg Hep.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 remember (slope_expr α (j, jps) pt ?= slope_expr α (j, jps) (h, hps)) as c.
 symmetry in Heqc.
 destruct c; subst ms; simpl.
  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h hps.
  apply lt_irrefl in Hhk; contradiction.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc.
  assumption.

  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h hps.
  apply lt_irrefl in Hhk; contradiction.

 remember [pt₁ … pts] as pts₁.
 simpl in Hms.
 remember (minimise_slope α (j, jps) (h, hps) pts₁) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c₁.
 symmetry in Heqc₁.
 destruct c₁; subst ms; simpl.
  simpl in Hseg, Hep.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hne, Hseg).
  subst pts₁.
  simpl in Heqms₁.
  remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl.
   simpl in Heqc₁, Hseg, Hep.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hne₂, Hseg).
   exfalso; apply Hne₂; reflexivity.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc; assumption.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc₁.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimised_slope_le; eassumption.

  subst pts₁.
  apply Qgt_alt in Heqc₁.
  simpl in Heqms₁.
  remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl.
   simpl in Heqc₁, Hseg, Hep.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hne₂, Hseg).
   exfalso; apply Hne₂; reflexivity.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc; assumption.
Qed.

Lemma points_between_j_and_k : ∀ n pts j jps k kps sjk skx hsl γ β,
  LocallySorted fst_lt pts
  → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
    → β = valuation α jps + Qnat j * γ
      → next_ch_points α n pts = [ahs (j, jps) sjk; ahs (k, kps) skx … hsl]
        → ∀ h hps, (j < h < k)%nat
          → (h, hps) ∈ pts
            → (h, hps) ∉ sjk
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx hsl γ β.
intros Hsort Hγ Hβ Hnp h hps (Hjh, Hhk) Hhps Hseg.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hhps as [Hhps| Hhps].
 injection Hhps; clear Hhps; intros; subst h hps.
 apply lt_irrefl in Hjh; contradiction.

 destruct Hhps as [Hhps| Hhps].
  subst pt₁.
  symmetry in Heqms₁.
  destruct pts as [| pt₁].
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   injection Hep₁; clear Hep₁; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   simpl in Heqms₁.
   remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
   destruct c; subst ms₁.
    simpl in Hep₁, Hseg, Hnp.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (H); exfalso; apply H; reflexivity.

    simpl in Hep₁, Hseg, Hnp.
    injection Hep₁; clear Hep₁; intros; subst h hps.
    apply lt_irrefl in Hhk; contradiction.

    symmetry in Hep₁.
    remember Heqms₂ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Heqc; apply Qgt_alt in Heqc.
    rewrite H in Heqc.
    subst β γ.
    apply ad_hoc_lt_lt.
     split; [ assumption | idtac ].
     eapply lt_trans; eassumption.

     unfold slope_expr in Heqc; simpl in Heqc.
     assumption.

  symmetry in Heqms₁.
  revert pt₁ ms₁ Hsort Heqms₁ Hep₁ Hseg Hnp.
  induction pts as [| pt₂]; intros.
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   contradiction.

   destruct Hhps as [Hhps| Hhps].
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
      eapply lt_trans; eassumption.

      unfold slope_expr in Heqms₁; simpl in Heqms₁.
      assumption.

     split; assumption.

    simpl in Heqms₁.
    remember (minimise_slope α (j, jps) pt₂ pts) as ms₂.
    symmetry in Heqms₂.
    remember (slope_expr α (j, jps) pt₁ ?= slope ms₂) as c.
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
      destruct Hsort; eapply lt_trans; eassumption.

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
     eapply lt_trans in Hlt₃; [ idtac | eassumption ].
     eapply lt_trans in Hlt₃; [ idtac | eassumption ].
     apply lt_irrefl in Hlt₃; contradiction.

     eapply IHpts; try eassumption.
     constructor.
      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; assumption.

      apply LSorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LSorted_inv_2 in Hsort.
      destruct Hsort; eapply lt_trans; eassumption.
Qed.

Lemma sorted_hd_not_in_tl : ∀ k (jps : puiseux_series α) kps pts,
  LocallySorted fst_lt [(k, jps) … pts] → (k, kps) ∉ pts.
Proof.
intros k jps kps pts H.
induction pts as [| (h, hps)]; [ intros HH; contradiction | idtac ].
intros HH.
destruct HH as [HH| HH].
 injection HH; clear HH; intros; subst h hps.
 apply LSorted_inv_2 in H; destruct H as (Hlt, H).
 apply lt_irrefl in Hlt; assumption.

 revert HH; apply IHpts.
 apply LSorted_inv_2 in H; destruct H as (Hlt₁, H).
 destruct pts as [| pt₂]; [ constructor | idtac ].
 apply LSorted_inv_2 in H; destruct H as (Hlt₂, H).
 constructor; [ assumption | idtac ].
 eapply lt_trans; eassumption.
Qed.

Lemma same_k_same_kps : ∀ pts j jps k (kps : puiseux_series α),
  LocallySorted fst_lt pts
  → (j, jps) ∈ pts
    → (k, kps) ∈ pts
      → j = k
        → jps = kps.
Proof.
intros pts j jps k kps Hpts Hjps Hkps Hjk.
subst j.
induction pts as [| pt]; intros; [ contradiction | idtac ].
destruct Hjps as [Hjps| Hjps]; [ subst pt | idtac ].
 destruct Hkps as [Hkps| Hkps].
  injection Hkps; clear; intros; subst jps; reflexivity.

  exfalso; revert Hkps; eapply sorted_hd_not_in_tl; eassumption.

 destruct Hkps as [Hkps| Hkps]; [ subst pt | idtac ].
  exfalso; revert Hjps; eapply sorted_hd_not_in_tl; eassumption.

  destruct pts as [| pt₂]; [ contradiction | idtac ].
  apply LSorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
  eapply IHpts; eassumption.
Qed.

Lemma rem_pts_in : ∀ pt₁ pt₂ pts₂ ms pt,
  minimise_slope α pt₁ pt₂ pts₂ = ms
  → pt ∈ rem_pts ms
    → pt ∈ pts₂.
Proof.
intros pt₁ pt₂ pts₂ ms pt Hms Hpt.
revert pt₁ pt₂ ms Hms Hpt.
induction pts₂ as [| pt₃]; intros; [ subst ms; contradiction | idtac ].
simpl in Hms.
remember (minimise_slope α pt₁ pt₃ pts₂) as ms₁.
symmetry in Heqms₁.
remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; simpl in Hpt.
 right; eapply IHpts₂; eassumption.

 assumption.

 right; eapply IHpts₂; eassumption.
Qed.

Lemma in_ch_in_pts : ∀ n pts pt s,
  ahs pt s ∈ next_ch_points α n pts
  → pt ∈ pts.
Proof.
intros n pts pt s Hhs.
remember (next_ch_points α n pts) as hsl.
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

  remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
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
