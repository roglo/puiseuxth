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
unfold lower_convex_hull_points in Hns.
remember (length pts) as n; clear Heqn.
remember (next_ch_points n pts) as nsl eqn:Hnsl .
revert ns pts n h αh Hsort Hnsl Hns Hαh.
induction nsl as [| ns₁]; intros; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns.
 destruct n; [ discriminate Hnsl | simpl in Hnsl ].
 destruct pts as [| pt₁]; [ discriminate Hnsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnsl | idtac ].
 injection Hnsl; clear Hnsl; intros Hnsl Hns₁; subst nsl.
 rewrite Hns₁ in Hαh.
 remember cons as f; simpl in Hαh; subst f.
 remember (minimise_slope pt₁ pt₂ pts) as ms eqn:Hms .
 destruct Hαh as [Hαh| Hαh].
  subst pt₁ ns₁; simpl.
  reflexivity.

  destruct Hαh as [Hαh| Hαh].
   subst ns₁; simpl.
   rewrite Hαh; simpl.
   unfold β, γ; simpl.
   field.
   apply Qgt_0_not_0, Qlt_minus.
   remember (beg_pt ms) as pt₄.
   remember Heqpt₄ as H; clear HeqH.
   rewrite Hms in Heqpt₄.
   rewrite minimised_slope_beg_pt in Heqpt₄.
   rewrite H in Heqpt₄; clear H.
   rewrite <- Heqpt₄.
   remember (fst (end_pt ms)) as x.
   remember Heqx as H; clear HeqH.
   rewrite Hαh in Heqx; simpl in Heqx.
   subst x h.
   eapply beg_lt_end_pt; [ eassumption | symmetry; eassumption ].

   clear IHnsl.
   subst ns₁.
   unfold β, γ; simpl.
   revert pt₁ pt₂ n h αh ms Hms Hsort Hαh.
   induction pts as [| pt₃]; intros.
    simpl in Hms.
    subst ms; contradiction.

    simpl in Hms.
    remember (minimise_slope pt₁ pt₃ pts) as ms₁ eqn:Hms₁ .
    remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
    symmetry in Heqc.
    rewrite slope_slope_expr in Heqc; [ idtac | symmetry; eassumption ].
    destruct c.
     subst ms.
     simpl in Hαh; simpl.
     apply Qeq_alt in Heqc.
     unfold slope_expr in Heqc.
     destruct Hαh as [Hαh| Hαh].
      subst pt₂.
      simpl in Heqc; simpl.
      do 2 rewrite Qdiv_minus_distr_r in Heqc.
      rewrite Qdiv_minus_distr_r.
      apply Qeq_opp_r in Heqc.
      do 2 rewrite Qopp_minus in Heqc.
      rewrite <- Heqc.
      field.
      apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
      apply Qgt_0_not_0, Qlt_minus; assumption.

      eapply IHpts; try eassumption.
      eapply Sorted_minus_2nd; [ idtac | eassumption ].
      intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

     subst ms; contradiction.

     subst ms.
     eapply IHpts; try eassumption.
     eapply Sorted_minus_2nd; [ idtac | eassumption ].
     intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 destruct n; [ discriminate Hnsl | simpl in Hnsl ].
 destruct pts as [| pt₁]; [ discriminate Hnsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnsl | idtac ].
 injection Hnsl; clear Hnsl; intros; subst ns₁ nsl.
 remember (minimise_slope pt₁ pt₂ pts) as ms eqn:Hms .
 eapply IHnsl; try reflexivity; try assumption.
 eapply minimise_slope_sorted; [ eassumption | idtac ].
 symmetry; assumption.
Qed.
