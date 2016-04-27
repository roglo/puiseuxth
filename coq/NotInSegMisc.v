(* NotInSegMisc.v *)

Require Import Utf8 QArith Sorting.

Require Import Misc.
Require Import Slope_base.
Require Import ConvexHull.
Require Import ConvexHullMisc.

(* 1/ two theorems very close to each other; another theorem to factorise them,
   perhaps? the most part is normalisation *)
(* 2/ perhaps could be proved shorter by the theorems of Slope.v? *)
Theorem ad_hoc_lt_lt₂ : ∀ i j k x y z,
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

Theorem ad_hoc_lt_lt : ∀ i j k x y z,
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

Theorem minimised_slope_le : ∀ pt₁ pt₂ pts ms,
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
  rewrite Heqc.
  unfold slope at 1; simpl.
  rewrite slope_slope_expr; [ idtac | symmetry; eassumption ].
  apply Qle_refl.

  simpl.
  apply Qle_refl.

  symmetry in Heqc; apply Qgt_alt in Heqc.
  apply Qlt_le_weak; eassumption.
Qed.

Theorem minimise_slope_pts_le : ∀ j αj pt pts ms,
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
  unfold slope; simpl.
  rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
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
  unfold slope; simpl.
  rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  eapply IHpts; eassumption.

  simpl.
  apply Qlt_alt in Heqc.
  apply Qlt_le_weak.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply IHpts; eassumption.

  eapply IHpts; eassumption.
Qed.

Theorem min_slope_lt_after_k : ∀ j αj k αk pt pts ms,
  Sorted fst_lt pts
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

   eapply Sorted_hd in Hsort; [ idtac | eassumption ].
   simpl in Hsort.
   eapply Qlt_trans in Hsort; [ idtac | eassumption ].
   apply Qlt_irrefl in Hsort; contradiction.

 simpl in Hms.
 remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl in Hep |- *.
  unfold slope; simpl.
  rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.

  simpl in Hep |- *.
  subst pt.
  symmetry in Heqc; apply Qlt_alt in Heqc.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimise_slope_pts_le; eassumption.

  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.
Qed.

Theorem points_after_k : ∀ n pts j αj k αk seg hsl γ β,
  Sorted fst_lt pts
  → j < k
    → γ = (αj - αk) / (k - j)
      → β = αj + j * γ
        → next_ch_points n pts = [mkns (j, αj) (k, αk) seg … hsl]
          → ∀ h αh, k < h
            → (h, αh) ∈ pts
              → β < αh + h * γ.
Proof.
intros n pts j αj k αk seg hsl γ β.
intros Hsort Hjk Hγ Hβ Hnp h αh Hkh Hαh.
destruct n; [ discriminate Hnp | simpl in Hnp ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
rewrite minimised_slope_beg_pt in Hnp.
injection Hnp; clear Hnp; intros Hnp Hseg Hep₁ Hp₁; subst seg pt₁.
rewrite Hep₁ in Hnp.
remember (minimise_slope (j, αj) pt₂ pts) as ms₁.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst h αh.
 eapply Qlt_trans in Hkh; [ idtac | eassumption ].
 apply Qlt_irrefl in Hkh; contradiction.

 destruct Hαh as [Hαh| Hαh]; [ exfalso | idtac ].
  subst pt₂.
  symmetry in Heqms₁.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
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
    eapply Qlt_trans; eassumption.

    unfold slope_expr in Heqms₁; simpl in Heqms₁.
    assumption.

   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   apply Sorted_inv_1 in Hsort; assumption.
Qed.

Theorem not_seg_min_sl_lt : ∀ j αj k αk pt pts ms h αh,
  Sorted fst_lt [(j, αj); pt; (h, αh) … pts]
  → minimise_slope (j, αj) pt [(h, αh) … pts] = ms
    → j < h < k
      → (h, αh) ∉ seg ms
        → end_pt ms = (k, αk)
          → slope ms < slope_expr (j, αj) (h, αh).
Proof.
intros j αj k αk pt pts ms h αh Hsort Hms (Hjh, Hhk) Hseg Hep.
rewrite slope_slope_expr; [ idtac | eassumption ].
revert ms Hms Hseg Hep.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 unfold slope in Hms; simpl in Hms.
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
   negation Hne₂.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h αh.
   apply Qlt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc.
   rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
   assumption.

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
   negation Hne₂.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h αh.
   apply Qlt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc.
   rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
   assumption.
Qed.

Theorem points_between_j_and_k : ∀ n pts j αj k αk oth hsl γ β,
  Sorted fst_lt pts
  → γ = (αj - αk) / (k - j)
    → β = αj + j * γ
      → next_ch_points n pts = [mkns (j, αj) (k, αk) oth … hsl]
        → ∀ h αh, j < h < k
          → (h, αh) ∈ pts
            → (h, αh) ∉ oth
              → β < αh + h * γ.
Proof.
intros n pts j αj k αk oth hsl γ β.
intros Hsort Hγ Hβ Hnp h αh (Hjh, Hhk) Hαh Hseg.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst oth.
remember H as Hnp; clear HeqHnp.
rename H1 into Hep₁.
clear H.
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
    destruct Hseg as (H, _); negation H.

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
  revert pt₁ ms₁ Hsort Heqms₁ Hep₁ Hseg Hnp H2.
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
      eapply Sorted_minus_2nd; [ idtac | eassumption ].
      intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

      rewrite <- Heqms₂, minimised_slope_beg_pt; reflexivity.

     simpl in Hep₁, Hseg, Hnp.
     subst pt₁.
     apply Sorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₂, Hsort).
     apply Sorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₃, Hsort).
     eapply Sorted_hd in Hsort; [ idtac | eassumption ].
     unfold fst_lt in Hlt₃.
     simpl in Hlt₃, Hsort.
     clear Hlt₂.
     eapply Qlt_trans in Hlt₃; [ idtac | eassumption ].
     eapply Qlt_trans in Hlt₃; [ idtac | eassumption ].
     apply Qlt_irrefl in Hlt₃; contradiction.

     eapply IHpts; try eassumption.
     eapply Sorted_minus_2nd; [ idtac | eassumption ].
     intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem in_ch_in_pts : ∀ n pts pt₁ pt₂ s,
  mkns pt₁ pt₂ s ∈ next_ch_points n pts
  → pt₁ ∈ pts ∧ pt₂ ∈ pts.
Proof.
intros n pts pt₁ pt₂ s Hhs.
remember (next_ch_points n pts) as hsl.
rename Heqhsl into Hhsl.
revert n pts pt₁ pt₂ s Hhsl Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct n; [ discriminate Hhsl | idtac ].
simpl in Hhsl.
destruct pts as [| pt₃]; [ discriminate Hhsl | idtac ].
destruct pts as [| pt₄]; [ discriminate Hhsl | idtac ].
injection Hhsl; clear Hhsl; intros; subst hs₁ hsl.
destruct Hhs as [Hhs| ].
 rewrite minimised_slope_beg_pt in Hhs.
 injection Hhs; clear Hhs; intros; subst pt₃ s.
 split; [ left; reflexivity | idtac ].
 rewrite <- H0; right.
 eapply end_pt_in; reflexivity.

 remember (minimise_slope pt₃ pt₄ pts) as ms₁.
 symmetry in Heqms₁.
 eapply IHhsl in H; [ idtac | reflexivity ].
 destruct H as (H₁, H₂).
 split.
  destruct H₁ as [H| H].
   apply end_pt_in in Heqms₁.
   subst pt₁.
   right; assumption.

   eapply rem_pts_in in H; [ idtac | eassumption ].
   right; right; assumption.

  destruct H₂ as [H| H].
   subst pt₂.
   apply end_pt_in in Heqms₁.
   right; assumption.

   right; right.
   eapply rem_pts_in; eassumption.
Qed.

Theorem sorted_qeq_eq : ∀ pts j αj k αk,
  Sorted fst_lt pts
  → (j, αj) ∈ pts
    → (k, αk) ∈ pts
      → j == k
        → (j, αj) = (k, αk).
Proof.
intros pts j αj k αk Hsort Hj Hk Hjk.
induction pts as [| (l, αl)]; [ contradiction | idtac ].
destruct Hj as [Hj| Hj].
 destruct Hk as [Hk| Hk].
  rewrite Hj in Hk; assumption.

  injection Hj; clear Hj; intros; subst l αl.
  clear IHpts.
  exfalso.
  induction pts as [| (l, αl)]; [ contradiction | idtac ].
  destruct Hk as [Hk| Hk].
   injection Hk; clear Hk; intros; subst l αl.
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
   unfold fst_lt in Hlt; simpl in Hlt; rewrite Hjk in Hlt.
   apply Qlt_irrefl in Hlt; contradiction.

   apply IHpts; [ assumption | idtac ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 destruct Hk as [Hk| Hk].
  injection Hk; clear Hk; intros; subst l αl.
  clear IHpts.
  exfalso.
  induction pts as [| (l, αl)]; [ contradiction | idtac ].
  destruct Hj as [Hj| Hj].
   injection Hj; clear Hj; intros; subst l αl.
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
   unfold fst_lt in Hlt; simpl in Hlt; rewrite Hjk in Hlt.
   apply Qlt_irrefl in Hlt; contradiction.

   apply IHpts; [ assumption | idtac ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  apply Sorted_inv_1 in Hsort.
  apply IHpts; assumption.
Qed.

Theorem qeq_eq_ini : ∀ n pts h αh j αj ptj s hsl₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) ptj s … hsl]
    → (h, αh) ∈ pts
      → h == j
        → h = j.
Proof.
intros n pts h αh j αj ptj s hsl₁ hsl Hpts Hhsl Hαh Hhk.
eapply sorted_qeq_eq with (αk := αj) in Hhk; try eassumption.
 injection Hhk; intros; subst; reflexivity.

 apply in_ch_in_pts with (n := n) (s := s) (pt₂ := ptj).
 rewrite Hhsl.
 apply List.in_app_iff.
 right; left; reflexivity.
Qed.

Theorem qeq_eq_fin : ∀ n pts h αh k αk ptk s hsl₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns ptk (k, αk) s … hsl]
    → (h, αh) ∈ pts
      → h == k
        → h = k.
Proof.
intros n pts h αh k αk ptk s hsl₁ hsl Hpts Hhsl Hαh Hhk.
eapply sorted_qeq_eq with (αk := αk) in Hhk; try eassumption.
 injection Hhk; intros; subst; reflexivity.

 apply in_ch_in_pts with (n := n) (s := s) (pt₁ := ptk).
 rewrite Hhsl.
 apply List.in_app_iff.
 right; left; reflexivity.
Qed.
