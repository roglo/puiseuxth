(* InSegment.v *)

(* points in newton segment *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import Slope_base.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Newton.

(* à voir... ça dépend de ce qu'on veut...
Lemma min_sl_pt_in_newt_segm : ∀ j αy k αk β γ pt pts ms segkx hsl n,
  Sorted fst_lt [(j, αy); pt … pts]
  → β = αy + j * γ
    → γ = (αy - αk) / (k - j)
      → minimise_slope (j, αy) pt pts = ms
        → next_ch_points n [end_pt ms … rem_pts ms] =
            [ahs (k, αk) segkx … hsl]
          → ∀ i αi, (i, αi) ∈ seg ms
            → αi + i * γ == β.
Proof.
intros j αy k αk β γ pt pts ms segkx hsl n.
intros Hsort Hβ Hγ Hms Hnp i αi Hαi.
revert pt ms hsl n i αi Hsort Hαi Hms Hnp.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 subst ms; simpl in Hnp, Hαi.
 contradiction.

 simpl in Hms.
 remember (minimise_slope (j, αy) pt₁ pts) as ms₁.
 remember (slope_expr (j, αy) pt ?= slope ms₁) as c.
 destruct c; subst ms; simpl in Hnp, Hαi; [ idtac | contradiction | idtac ].
  symmetry in Heqms₁.
  symmetry in Heqc.
  apply Qeq_alt in Heqc.
  remember Hnp as Hnp₁; clear HeqHnp₁.
  apply next_ch_points_hd in Hnp.
  symmetry in Hnp.
  remember Heqms₁ as Hms; clear HeqHms.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  rewrite <- Heqc in Heqms₁.
  destruct Hαi as [Hαi| Hαi].
   subst pt.
   subst β.
   unfold slope_expr in Heqms₁; simpl in Heqms₁.
   remember (αk) as v₃.
   subst γ.
   do 2 rewrite Qdiv_minus_distr_r in Heqms₁.
   rewrite Qdiv_minus_distr_r.
   apply Qeq_opp_r in Heqms₁.
   do 2 rewrite Qopp_minus in Heqms₁.
   rewrite <- Heqms₁.
   field.
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   apply Qgt_0_not_0, Qlt_minus; assumption.

   eapply IHpts; try eassumption.
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  symmetry in Heqms₁.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma in_newt_segm : ∀ j αy k αk γ β n pts segjk segkx hsl₁ hsl,
  Sorted fst_lt pts
  → β = αy + j * γ
    → γ = (αy - αk) / (k - j)
      → next_ch_points n pts =
          hsl₁ ++ [ ahs (j, αy) segjk; ahs (k, αk) segkx … hsl]
        → ∀ i αi, (i, αi) ∈ segjk
          → αi + i * γ == β.
Proof.
intros j αy k αk γ β n pts segjk segkx hsl₁ hsl.
intros Hsort Hβ Hγ Hch i αi Hαi.
rename Hch into Hnp.
destruct n; [ apply List.app_cons_not_nil in Hnp; contradiction | idtac ].
destruct pts as [| pt₁].
 apply List.app_cons_not_nil in Hnp; contradiction.

 destruct pts as [| pt₂].
  destruct hsl₁ as [| pt₂]; [ discriminate Hnp | idtac ].
  destruct hsl₁; discriminate Hnp.

  revert n pt₁ pt₂ pts Hnp Hsort.
  induction hsl₁ as [| hs₁]; intros.
   injection Hnp; clear Hnp; intros; subst segjk.
   rewrite H1 in H, Hαi, Hsort.
   eapply min_sl_pt_in_newt_segm; try eassumption; reflexivity.

   injection Hnp; clear Hnp; intros; subst hs₁.
   rename H into Hnp.
   destruct n; [ apply List.app_cons_not_nil in Hnp; contradiction | idtac ].
   remember (minimise_slope pt₁ pt₂ pts) as ms₁.
   symmetry in Heqms₁.
   eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
   remember (rem_pts ms₁) as pts₁.
   destruct pts₁ as [| pt₃].
    destruct hsl₁ as [| pt₃]; [ discriminate Hnp | idtac ].
    destruct hsl₁; discriminate Hnp.

    eapply IHhsl₁; eassumption.
Qed.
*)

Lemma points_in_any_newton_segment₁ : ∀ ns pts,
  Sorted fst_lt pts
  → ns ∈ lower_convex_hull_points pts
    → ∀ h αh, (h, αh) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns == αh + h * γ ns.
Proof.
intros ns pts Hsort Hns h αh Hαh.
remember Hsort as Hsort₂; clear HeqHsort₂.
eapply lower_convex_hull_points_sorted in Hsort; [ idtac | reflexivity ].
unfold lower_convex_hull_points in Hns.
remember (length pts) as n; clear Heqn.
revert n ns Hns Hαh.
induction pts as [| pt₁]; intros; [ destruct n; contradiction | idtac ].
destruct n; [ contradiction | simpl in Hns ].
destruct pts as [| pt₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl.
 simpl in Hαh.
 unfold β, γ; simpl.
 destruct Hαh as [Hαh| Hαh].
  subst pt₁; reflexivity.

  remember (minimise_slope pt₁ pt₂ pts) as ms.
  destruct Hαh as [Hαh| Hαh].
   rewrite Hαh; simpl.
   remember (beg_pt ms) as j.
   symmetry in Heqj.
   destruct j as (j, αj).
   remember Heqj as Hαj; clear HeqHαj.
   rewrite Heqms in Heqj.
   rewrite minimised_slope_beg_pt in Heqj.
   rewrite Heqj; simpl.
   field.
   apply Qgt_0_not_0, Qlt_minus.
   symmetry in Heqms.
   apply beg_lt_end_pt in Heqms; [ idtac | assumption ].
   rewrite Hαj, Hαh in Heqms; assumption.
bbb.

intros ns pts Hsort Hns h αh Hαh.
remember Hsort as Hsort₂; clear HeqHsort₂.
eapply lower_convex_hull_points_sorted in Hsort; [ idtac | reflexivity ].
unfold lower_convex_hull_points in Hns.
remember (length pts) as n; clear Heqn.
revert n pts ns Hsort Hsort₂ Hhsl Hns Hαh.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
simpl in Hns.
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 destruct hs₁ as ((j, αy), seg₁).
 destruct hs₂ as ((k, αk), seg₂).
 subst ns; simpl.
 simpl in Hαh.
 destruct Hαh as [Hαh| Hαh].
  injection Hαh; clear Hαh; intros; subst h αh; reflexivity.

  destruct Hαh as [Hαh| Hαh].
   injection Hαh; clear Hαh; intros; subst h αh.
   eapply two_pts_slope_form; eassumption.

   destruct pts as [| pt₁].
    unfold lower_convex_hull_points in Hhsl.
    destruct n; discriminate Hhsl.

    symmetry.
    eapply in_newt_segm with (hsl₁ := []); try eassumption; try reflexivity.

 destruct n; [ discriminate Hhsl | idtac ].
 simpl in Hhsl.
 destruct pts as [| pt₁]; [ discriminate Hhsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hhsl | idtac ].
 injection Hhsl; clear Hhsl; intros.
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 apply Sorted_inv_1 in Hsort.
 eapply minimise_slope_sorted in Hsort₂; [ idtac | eassumption ].
 eapply IHhsl; eassumption.
Qed.
