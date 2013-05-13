(* $Id: NotInSegment.v,v 1.150 2013-05-13 21:05:57 deraugla Exp $ *)

(* points not in newton segment *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Puiseux.
Require Import NotInSegMisc.

Section convex_hull.

Variable α : Type.
Variable fld : field (puiseux_series α).

Theorem points_not_in_newton_segment : ∀ pol pts ns nsl,
  pts = points_of_ps_polynom α fld pol
  → newton_segments fld pol = [ns … nsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
        → β ns < αh + h * (γ ns).
Proof.
intros pol pts ns nsl Hpts Hns h αh Hαh Hnαh.
remember Hαh as Hint; clear HeqHint.
eapply fst_is_int in Hint; [ idtac | symmetry; eassumption ].
remember Hpts as HHpts; clear HeqHHpts.
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points pts) as hsl.
destruct hsl as [| ((j, αj), segjx)]; [ discriminate Hns | idtac ].
destruct hsl as [| ((k, αk), segkx)]; [ discriminate Hns | idtac ].
injection Hns; clear Hns; intros; subst ns.
simpl in H |- *.
rename H into Hhsl.
symmetry in Heqhsl.
destruct (Qlt_le_dec k h) as [Hlt| Hge].
 unfold points_of_ps_polynom in Hpts.
 apply points_of_polyn_sorted in Hpts.
 remember Hpts as Hpts₂; clear HeqHpts₂.
 eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
 apply LSorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
 unfold hs_x_lt in Hlt; simpl in Hlt.
 eapply points_after_k; try eassumption; reflexivity.

 destruct (Qeq_dec h k) as [Heq| Hne].
  symmetry in HHpts.
  eapply same_k_same_αk with (αk := αk) in Hαh; try eassumption.
   unfold lower_convex_hull_points in Heqhsl.
   assert ((k, αk) ∈ pts).
    apply in_ch_in_pts with (n := length pts) (s := segkx).
    rewrite Heqhsl.
    right; left; reflexivity.

    eapply fst_is_int in H; [ idtac | symmetry; eassumption ].
    rewrite <- H in Hint.
    apply same_den_qeq_eq in Hint; [ idtac | assumption ].
    subst h αh.
    simpl in Hnαh.
    apply Decidable.not_or in Hnαh.
    destruct Hnαh as (_, Hnαh).
    apply Decidable.not_or in Hnαh.
    destruct Hnαh as (Hnαh, _).
    exfalso; apply Hnαh; reflexivity.

   eapply in_ch_in_pts with (n := length pts).
   unfold lower_convex_hull_points in Heqhsl; rewrite Heqhsl.
   right; left; reflexivity.

  apply Qle_neq_lt in Hge; [ idtac | assumption ].
  destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
   unfold points_of_ps_polynom in Hpts.
   apply points_of_polyn_sorted in Hpts.
   remember Hpts as Hpts₂; clear HeqHpts₂.
   eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
   unfold hs_x_lt in Hlt; simpl in Hlt.
   eapply points_between_j_and_k; try eassumption; try reflexivity.
    split; assumption.

    simpl in Hnαh.
    apply Decidable.not_or in Hnαh.
    destruct Hnαh as (_, Hnαh).
    apply Decidable.not_or in Hnαh.
    destruct Hnαh as (_, Hnαh).
    assumption.

   unfold points_of_ps_polynom in Hpts.
   apply points_of_polyn_sorted in Hpts.
   unfold lower_convex_hull_points in Heqhsl.
   remember (length pts) as n; clear Heqn.
   destruct n.
    simpl in Heqhsl.
    discriminate Heqhsl.

    simpl in Heqhsl.
    destruct pts as [| (l, αl)]; [ discriminate Heqhsl | idtac ].
    destruct pts as [| (m, αm)]; [ discriminate Heqhsl | idtac ].
    injection Heqhsl; clear Heqhsl; intros; subst l αl.
    destruct Hαh as [Hαh| Hαh].
     injection Hαh; clear Hαh; intros; subst h αh.
     simpl in Hnαh.
     apply Decidable.not_or in Hnαh.
     destruct Hnαh as (HH); exfalso; apply HH; reflexivity.

     eapply LSorted_hd in Hpts; [ idtac | eassumption ].
     apply Qle_not_lt in Hge₂; contradiction.
Qed.

(* is there a way to group together the cases c = Eq and c = Gt? *)
Lemma aft_end_in_rem : ∀ pt₁ pt₂ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → ∀ h αh, (h, αh) ∈ [pt₁; pt₂ … pts] 
      → fst (end_pt ms) < h
        → (h, αh) ∈ rem_pts ms.
Proof.
intros pt₁ pt₂ pts ms Hsort Hms h αh Hαh Hlt.
destruct Hαh as [Hαh| Hαh].
 subst pt₁.
 apply minimise_slope_le in Hms.
  apply LSorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₁).
  eapply Qlt_trans in Hlt₁; [ idtac | eassumption ].
  apply Qle_not_lt in Hms; contradiction.

  eapply LSorted_inv_1; eassumption.

 destruct Hαh as [Hαh| Hαh].
  subst pt₂.
  apply minimise_slope_le in Hms.
   apply Qle_not_lt in Hms; contradiction.

   eapply LSorted_inv_1; eassumption.

  revert pt₁ pt₂ ms Hsort Hms Hαh Hlt.
  induction pts as [| pt₃]; [ contradiction | intros ].
  simpl in Hms.
  remember (minimise_slope pt₁ pt₃ pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
  symmetry in Heqc.
  destruct c; subst ms; simpl in Hlt |- *.
   destruct Hαh as [Hαh| Hαh].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply Qle_not_lt in Heqms₁; contradiction.

     do 2 apply LSorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    eapply LSorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   assumption.

   destruct Hαh as [Hαh| Hαh].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply Qle_not_lt in Heqms₁; contradiction.

     do 2 apply LSorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    eapply LSorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma consec_end_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → minimise_slope (end_pt ms₁) pt₃ pts₃ = ms₂
      → rem_pts ms₁ = [pt₃ … pts₃]
        → fst (end_pt ms₁) < fst (end_pt ms₂).
Proof.
intros pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂ Hsort Hms₁ Hms₂ Hrem₁.
apply minimise_slope_le in Hms₂.
 eapply Qlt_le_trans; [ idtac | eassumption ].
 apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
 rewrite Hrem₁ in Hms₁.
 apply LSorted_inv_2 in Hms₁.
 destruct Hms₁; assumption.

 rewrite <- Hrem₁.
 apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
 eapply LSorted_inv_1; eassumption.
Qed.

Lemma min_slope_lt : ∀ pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃,
  LocallySorted fst_lt [pt₁; pt₂; pt₃ … pts]
  → minimise_slope pt₁ pt₃ pts = ms₁₃
    → minimise_slope pt₂ pt₃ pts = ms₂₃
      → slope_expr pt₁ pt₂ < slope ms₁₃
        → slope ms₁₃ < slope ms₂₃.
Proof.
intros pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃ Hsort Hms₁₃ Hms₂₃ Heqc.
revert pt₁ pt₂ pt₃ ms₂₃ ms₁₃ Heqc Hsort Hms₁₃ Hms₂₃.
induction pts as [| pt₄]; intros.
 subst ms₁₃ ms₂₃; simpl in Heqc |- *.
 apply slope_lt₁₁; [ idtac | assumption ].
 apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
 apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
 split; assumption.

 simpl in Hms₁₃.
 remember (minimise_slope pt₁ pt₄ pts) as ms₁₄.
 rename Heqms₁₄ into Hms₁₄; symmetry in Hms₁₄.
 remember (slope_expr pt₁ pt₃ ?= slope ms₁₄) as c₁.
 symmetry in Heqc₁.
 simpl in Hms₂₃.
 remember (minimise_slope pt₂ pt₄ pts) as ms₂₄.
 rename Heqms₂₄ into Hms₂₄; symmetry in Hms₂₄.
 remember (slope_expr pt₂ pt₃ ?= slope ms₂₄) as c₂.
 symmetry in Heqc₂.
 destruct c₁.
  apply Qeq_alt in Heqc₁.
  subst ms₁₃; simpl in Heqc |- *.
  destruct c₂.
   apply Qeq_alt in Heqc₂.
   subst ms₂₃; simpl.
   eapply IHpts; try eassumption.
   eapply LSorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   rewrite <- Heqc₁.
   rewrite <- Heqc₁ in Heqc.
   apply slope_lt₁₁; [ idtac | assumption ].
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply IHpts; try eassumption.
   eapply LSorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  apply Qlt_alt in Heqc₁.
  subst ms₁₃; simpl in Heqc |- *.
  destruct c₂.
   apply Qeq_alt in Heqc₂.
   subst ms₂₃; simpl.
   rewrite <- Heqc₂.
   apply slope_lt₁₁; [ idtac | assumption ].
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   apply slope_lt₁₁; [ idtac | assumption ].
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply Qlt_trans; [ eassumption | idtac ].
   eapply IHpts with (pt₂ := pt₂); try eassumption.
    eapply Qlt_trans; eassumption.

    eapply LSorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  apply Qgt_alt in Heqc₁.
  subst ms₁₃.
  destruct c₂.
   apply Qeq_alt in Heqc₂.
   subst ms₂₃; simpl.
   eapply IHpts; try eassumption.
   eapply LSorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   eapply Qlt_trans; [ eassumption | idtac ].
   eapply Qlt_trans in Heqc₁; [ idtac | eassumption ].
   apply slope_lt₁₁; [ idtac | assumption ].
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply IHpts; try eassumption.
   eapply LSorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma consec_slope_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → minimise_slope (end_pt ms₁) pt₃ pts₃ = ms₂
      → rem_pts ms₁ = [pt₃ … pts₃]
        → slope ms₁ < slope ms₂.
Proof.
intros pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂ Hsort Hms₁ Hms₂ Hrem₁.
revert pt₁ pt₂ pt₃ pts₃ ms₁ ms₂ Hsort Hms₁ Hms₂ Hrem₁.
induction pts as [| pt₄]; intros.
 simpl in Hms₁; subst ms₁.
 simpl in Hms₂, Hrem₁ |- *.
 discriminate Hrem₁.

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₄ pts) as ms₃.
 rename Heqms₃ into Hms₃; symmetry in Hms₃.
 remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
 symmetry in Heqc.
 destruct c.
  subst ms₁.
  simpl in Hms₂, Hrem₁ |- *.
  apply Qeq_alt in Heqc.
  eapply IHpts; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms₁.
  simpl in Hms₂, Hrem₁ |- *.
  injection Hrem₁; clear Hrem₁; intros; subst pt₄ pts₃.
  apply Qlt_alt in Heqc.
  eapply Qlt_trans; [ eassumption | idtac ].
  eapply min_slope_lt; eassumption.

  subst ms₁.
  eapply IHpts; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma j_aft_prev_end :
  ∀ n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j αj segjk k αk segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → rem_pts ms = [pt₃ … pts₃]
      → minimise_slope (end_pt ms) pt₃ pts₃ = ms₁
        → next_ch_points n [end_pt ms₁ … rem_pts ms₁] =
          hsl₁ ++
          [{| pt := (j, αj); oth := segjk |};
          {| pt := (k, αk); oth := segkx |} … hsl]
          → fst (end_pt ms) < j.
Proof.
intros n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j αj segjk k αk segkx hsl.
intros Hsort Hms Hrem Hms₁ Hnp.
revert pt₁ pt₂ pt₃ pts pts₃ ms ms₁ hsl₁ Hms Hrem Hms₁ Hnp Hsort.
induction n; intros; [ destruct hsl₁; discriminate Hnp | idtac ].
simpl in Hnp.
remember (rem_pts ms₁) as pts₂.
destruct pts₂ as [| pt₄].
 destruct hsl₁ as [| hs₁]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros.
 destruct hsl₁; discriminate H.

 remember (minimise_slope (end_pt ms₁) pt₄ pts₂) as ms₂.
 symmetry in Heqms₂.
 destruct hsl₁ as [| h₁].
  injection Hnp; clear Hnp; intros; subst segjk.
  rename H into Hnp.
  rename H1 into Hend.
  replace j with (fst (j, αj)) by reflexivity.
  rewrite <- Hend.
  eapply consec_end_lt; eassumption.

  simpl in Hnp.
  injection Hnp; clear Hnp; intros.
  rename H into Hnp; subst h₁.
  assert (fst (end_pt ms₁) < j).
   symmetry in Heqpts₂.
   eapply IHn; try eassumption.
   rewrite <- Hrem.
   eapply minimise_slope_sorted; eassumption.

   eapply Qlt_trans; [ idtac | eassumption ].
   eapply consec_end_lt; eassumption.
Qed.

Lemma aft_j_in_rem :
  ∀ n pt₁ pt₂ pts ms hsl₁ j αj segjk k αk segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → next_ch_points n [end_pt ms … rem_pts ms] =
       hsl₁ ++
       [{| pt := (j, αj); oth := segjk |};
        {| pt := (k, αk); oth := segkx |} … hsl]
      → ∀ h αh, (h, αh) ∈ [pt₁; pt₂ … pts]
        → j < h
          → (h, αh) ∈ rem_pts ms.
Proof.
intros n pt₁ pt₂ pts ms hsl₁ j αj segjk k αk segkx hsl.
intros Hsort Hms Hnp h αh Hαh Hjh.
destruct n; [ destruct hsl₁; discriminate Hnp | simpl in Hnp ].
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃].
 destruct hsl₁ as [| hs₁]; [ discriminate Hnp | simpl in Hnp ].
 injection Hnp; clear Hnp; intros; subst hs₁.
 destruct hsl₁; discriminate H.

 remember (minimise_slope (end_pt ms) pt₃ pts₁) as ms₁.
 symmetry in Heqms₁.
 rewrite <- Hrem.
 destruct hsl₁ as [| hs₁].
  injection Hnp; clear Hnp; intros.
  rename H into Hnp; rename H1 into Hend.
  subst segjk.
  remember Hsort as Hsort₂; clear HeqHsort₂.
  eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
  rewrite Hend, Hrem in Hsort.
  eapply aft_end_in_rem in Hsort₂; try eassumption.
  rewrite Hend; assumption.

  eapply aft_end_in_rem; try eassumption.
  eapply Qlt_trans; [ idtac | eassumption ].
  injection Hnp; clear Hnp; intros.
  eapply j_aft_prev_end; eassumption.
Qed.

Lemma lt_aft_k : ∀ n pts hsl₁ hsl j αj segjk k αk segkx,
  LocallySorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → k < h
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts hsl₁ hsl j αj segjk k αk segkx Hsort Hnp h αh Hαh Hkh.
revert n pts Hsort Hnp Hαh.
induction hsl₁ as [| hs₁]; intros.
 remember Hsort as Hsort₂; clear HeqHsort₂.
 eapply points_after_k; try reflexivity; try eassumption.
 apply next_points_sorted in Hnp; [ idtac | assumption ].
 apply LSorted_inv_2 in Hnp.
 destruct Hnp; assumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  destruct hsl₁ as [| pt₂]; [ discriminate Hnp | idtac ].
  destruct hsl₁; discriminate Hnp.

  injection Hnp; clear Hnp; intros.
  remember Hsort as Hsort₂; clear HeqHsort₂.
  eapply minimise_slope_sorted in Hsort; [ idtac | reflexivity ].
  eapply IHhsl₁; try eassumption.
  right.
  eapply aft_j_in_rem; try eassumption; [ reflexivity | idtac ].
  eapply Qlt_trans; [ idtac | eassumption ].
  apply next_points_sorted in H; [ idtac | assumption ].
  revert H; clear; intros.
  induction hsl₁ as [| hs₁].
   apply LSorted_inv_2 in H.
   destruct H; assumption.

   simpl in H.
   apply LSorted_inv_1 in H.
   apply IHhsl₁; assumption.
Qed.

Lemma not_k : ∀ n pol pts hsl₁ hsl j αj segjk k αk segkx,
  points_of_ps_polynom α fld pol = pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … segjk]
        → h ≠ k.
Proof.
intros n pol pts hsl₁ hsl j αj segjk k αk segkx.
intros Hsort Hnp h αh Hαh Hnαh Hhk.
eapply same_k_same_αk with (αk := αk) in Hαh; try eassumption.
 subst h αh.
 simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (_, Hnαh).
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 exfalso; apply Hnαh; reflexivity.

 eapply in_ch_in_pts with (n := n).
 rewrite Hnp.
 apply List.in_or_app.
 right; right; left; reflexivity.

 subst h; reflexivity.
Qed.

Lemma next_ch_points_sorted : ∀ n pt₁ pt₂ pts h₁ hsl₁ hsl sg,
  LocallySorted fst_lt [pt₁ … pts]
  → next_ch_points n [pt₁ … pts] =
      [h₁ … hsl₁] ++ [{| pt := pt₂; oth := sg |} … hsl]
    → fst pt₁ < fst pt₂.
Proof.
intros n pt₁ pt₂ pts h₁ hsl₁ hsl sg.
intros Hsort Hnp.
revert n pt₁ pt₂ pts h₁ hsl sg Hsort Hnp.
induction hsl₁ as [| h₂]; intros.
 simpl in Hnp.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₁.
 symmetry in Heqms₁.
 apply next_ch_points_hd in Hnp.
 rewrite <- Hnp.
 eapply Qlt_le_trans.
  apply LSorted_inv_2 in Hsort.
  destruct Hsort; eassumption.

  eapply minimise_slope_le; [ idtac | eassumption ].
  eapply LSorted_inv_1; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₂.
 symmetry in Heqms₂.
 eapply IHhsl₁ in Hnp.
  apply LSorted_inv_2 in Hsort.
  destruct Hsort.
  eapply Qlt_trans; [ eassumption | idtac ].
  apply minimise_slope_le in Heqms₂.
   eapply Qle_lt_trans; eassumption.

   assumption.

  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bet_j_and_k : ∀ n pts hsl₁ hsl j αj segjk k αk segkx,
  LocallySorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … segjk]
        → j < h < k
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts hsl₁ hsl j αj segjk k αk segkx Hsort Hnp.
intros h αh Hαh Hnαh Hjhk.
simpl in Hnαh.
apply Decidable.not_or in Hnαh.
destruct Hnαh as (_, Hnαh).
apply Decidable.not_or in Hnαh.
destruct Hnαh as (_, Hnαh).
destruct hsl₁ as [| h₁].
 eapply points_between_j_and_k; try eassumption; try reflexivity.

 revert pts h₁ hsl₁ Hsort Hnp Hαh.
 induction n; intros; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ destruct hsl₁; discriminate Hnp | idtac ].
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 rename Heqms₁ into Hms₁; symmetry in Hms₁.
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 destruct hsl₁ as [| h₁].
  remember Hms₁ as Hsort₂; clear HeqHsort₂.
  eapply minimise_slope_sorted in Hsort₂; [ idtac | eassumption ].
  eapply points_between_j_and_k; try eassumption; try reflexivity.
  right; destruct Hjhk.
  eapply aft_j_in_rem with (hsl₁ := []); simpl; try eassumption.

  remember Hms₁ as Hsort₂; clear HeqHsort₂.
  eapply minimise_slope_sorted in Hsort₂; [ idtac | eassumption ].
  eapply IHn; try eassumption.
  right.
  eapply aft_end_in_rem; try eassumption.
  eapply Qlt_trans; [ idtac | destruct Hjhk; eassumption ].
  replace j with (fst (j, αj)) by reflexivity.
  apply next_ch_points_sorted in Hnp; [ assumption | idtac ].
  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma not_j : ∀ n pol pts hsl₁ j αj k αk segjk segkx hsl,
  points_of_ps_polynom α fld pol = pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … segjk]
        → h ≠ j.
Proof.
intros n pol pts hsl₁ j αj k αk segjk segkx hsl.
intros Hpts Hnp h αh Hαh Hnαh Hne.
eapply same_k_same_αk with (αk := αj) in Hαh; try eassumption.
 subst h αh.
 simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 exfalso; apply Hnαh; reflexivity.

 eapply in_ch_in_pts with (n := n).
 rewrite Hnp.
 apply List.in_or_app.
 right; left; reflexivity.

 subst h; reflexivity.
Qed.

Lemma slope_expr_eq : ∀ pt₁ pt₂ pt₃ pts,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → pt₃ ∈ pts
    → slope_expr pt₁ pt₂ == slope_expr pt₁ pt₃
      → slope_expr pt₁ pt₂ == slope_expr pt₂ pt₃.
Proof.
intros pt₁ pt₂ pt₃ pts Hsort Hin H.
apply slope_eq; [ idtac | idtac | idtac | assumption ].
 intros HH.
 apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
 unfold fst_lt in Hlt.
 rewrite HH in Hlt.
 apply Qlt_irrefl in Hlt; contradiction.

 intros HH.
 clear H.
 induction pts as [| pt₄]; [ contradiction | idtac ].
 simpl in Hin.
 destruct Hin as [Hin| Hin].
  subst pt₄.
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  unfold fst_lt in Hlt₂.
  rewrite HH in Hlt₂.
  apply Qlt_irrefl in Hlt₂; contradiction.

  apply IHpts; [ idtac | assumption ].
  eapply LSorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 intros HH.
 clear H.
 induction pts as [| pt₄]; [ contradiction | idtac ].
 simpl in Hin.
 destruct Hin as [Hin| Hin].
  subst pt₄.
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  unfold fst_lt in Hlt₂.
  rewrite HH in Hlt₂.
  eapply Qlt_trans in Hlt₂; [ idtac | eassumption ].
  apply Qlt_irrefl in Hlt₂; contradiction.

  apply IHpts; [ idtac | assumption ].
  eapply LSorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma minimise_slope_expr_le : ∀ pt₁ pt₂ pt₃ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → end_pt ms = pt₃
      → fst pt₂ < fst pt₃
        → slope_expr pt₂ pt₃ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pts ms Hsort Hms Hend Hlt.
revert pt₁ pt₂ pt₃ ms Hsort Hms Hend Hlt.
induction pts as [| pt₄]; intros.
 subst pt₃ ms; apply Qlt_irrefl in Hlt; contradiction.

 simpl in Hms.
 remember (minimise_slope pt₁ pt₄ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 destruct c.
  subst ms; simpl in Hend |- *.
  apply Qeq_alt in Heqc.
  symmetry in Hend.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  rewrite <- Heqc in Heqms₁ |- *.
  eapply slope_expr_eq in Heqms₁; try eassumption.
   rewrite Heqms₁; apply Qle_refl.

   rewrite Hend.
   eapply end_pt_in; eassumption.

  subst ms; simpl in Hend |- *.
  subst pt₃.
  apply LSorted_inv_2 in Hsort; destruct Hsort as (_, Hsort).
  apply LSorted_inv_2 in Hsort; destruct Hsort as (H).
  apply Qlt_irrefl in Hlt; contradiction.

  move Hms at top; subst ms₁.
  apply Qgt_alt in Heqc.
  clear IHpts.
  revert pt₁ pt₂ pt₃ pt₄ ms Hsort Hend Hlt Heqms₁ Heqc.
  induction pts as [| pt₅]; intros.
   simpl in Heqms₁.
   subst ms; simpl.
   simpl in Hend, Heqc.
   subst pt₄.
   apply Qlt_le_weak.
   apply slope_lt₂; [ idtac | assumption ].
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   simpl in Heqms₁.
   remember (minimise_slope pt₁ pt₅ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr pt₁ pt₄ ?= slope ms₂) as c₁.
   symmetry in Heqc₁.
   destruct c₁.
    subst ms; simpl in Hend, Heqc |- *.
    eapply IHpts; try eassumption.
    eapply LSorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

    subst ms; simpl in Hend, Heqc |- *.
    subst pt₄.
    apply Qlt_le_weak.
    apply slope_lt₂; [ idtac | assumption ].
    apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
    apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    split; assumption.

    subst ms; simpl in Hend |- *.
    eapply IHpts; try eassumption.
    eapply LSorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma min_slope_le : ∀ pt₁ pt₂ pt₃ pt₄ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → pt₃ ∈ pts
      → end_pt ms = pt₄
        → fst pt₃ < fst pt₄
          → slope_expr pt₃ pt₄ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pt₄ pts ms Hsort Hms Hpt Hend Hlt.
revert pt₁ pt₂ pt₃ pt₄ ms Hsort Hms Hpt Hend Hlt.
induction pts as [| pt₅]; [ contradiction | intros ].
simpl in Hms.
remember (minimise_slope pt₁ pt₅ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
destruct c.
 subst ms; simpl in Hend |- *.
 destruct Hpt as [Hpt| Hpt].
  subst pt₅.
  eapply minimise_slope_expr_le; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  eapply IHpts; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 subst ms; simpl in Hend |- *; subst pt₄.
 apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
 apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
 eapply Qlt_trans in Hlt₂; [ idtac | eassumption ].
 exfalso; revert Hpt.
 eapply LSorted_not_in; [ idtac | idtac | eassumption | eassumption ].
  intros x H; apply Qlt_irrefl in H; contradiction.

  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 move Hms at top; subst ms₁.
 destruct Hpt as [Hpt| Hpt].
  subst pt₅.
  eapply minimise_slope_expr_le; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  eapply IHpts; try eassumption.
  eapply LSorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma yyy : ∀ n pts h αh i αi j αj l αl segjx hsl₁ hsl ms,
  LocallySorted fst_lt [(h, αh); (i, αi) … pts]
  → h < l < j
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (l, αl)
        → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [{| pt := (j, αj); oth := segjx |} … hsl]
          → slope_expr (h, αh) (j, αj) < slope_expr (l, αl) (j, αj).
Proof.
intros n pts h αh i αi j αj l αl segjx hsl₁ hsl ms.
intros Hsort (Hhl, Hlj) Hms Hend Hnp.
revert n pts h αh i αi j αj l αl segjx hsl ms Hsort Hhl Hlj Hms Hnp Hend.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 rewrite Hend in Hnp.
 destruct pts₁ as [| pt₁].
  injection Hnp; clear Hnp; intros; subst l αl.
  apply Qlt_irrefl in Hlj; contradiction.

  injection Hnp; clear Hnp; intros; subst l αl.
  apply Qlt_irrefl in Hlj; contradiction.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 destruct pts₁ as [| pt₁]; [ destruct hsl₁; discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
 remember (minimise_slope (end_pt ms) pt₁ pts₁) as ms₁.
 symmetry in Heqms₁.
 rewrite Hend in Heqms₁.
 destruct pt₁ as (m, αm).
 remember (end_pt ms₁) as pt₂.
 destruct pt₂ as (p, αp).
 rewrite Heqpt₂ in Hnp.
 destruct hsl₁ as [| hs₁].
  remember Hnp as HHnp; clear HeqHHnp.
  apply next_ch_points_hd in Hnp.
  rewrite <- Heqpt₂ in Hnp.
  injection Hnp; clear Hnp; intros; subst p αp.
  apply slope_lt₃₁; [ split; assumption | idtac ].
  rewrite <- minimised_slope.
   3: symmetry in Hend; eassumption.

   2: eassumption.

   rewrite <- minimised_slope.
    3: eassumption.

    2: eassumption.

    eapply consec_slope_lt; try eassumption.
     rewrite Hend; eassumption.

     symmetry; eassumption.

  remember Hnp as Hnp₁; clear HeqHnp₁.
  eapply IHhsl₁ in Hnp.
   5: eassumption.

   5: symmetry in Heqpt₂; eassumption.

   Focus 2.
   rewrite <- Hend, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.

   Focus 2.
   apply Qlt_le_trans with (y := m).
    apply minimise_slope_sorted in Hms; [ idtac | assumption ].
    rewrite Hend, <- Heqpts₁ in Hms.
    apply LSorted_inv_2 in Hms; destruct Hms; assumption.

    apply minimise_slope_le in Heqms₁.
     rewrite <- Heqpt₂ in Heqms₁; assumption.

     apply minimise_slope_sorted in Hms.
      rewrite <- Heqpts₁ in Hms.
      eapply LSorted_inv_1; eassumption.

      assumption.

   Focus 2.
   apply next_ch_points_sorted in Hnp.
    rewrite <- Heqpt₂ in Hnp; assumption.

    eapply minimise_slope_sorted; [ idtac | eassumption ].
    rewrite <- Hend, Heqpts₁.
    eapply minimise_slope_sorted; eassumption.

   apply slope_lt₃₁.
    split; assumption.

    apply Qlt_trans with (y := slope_expr (l, αl) (p, αp)).
     Focus 2.
     apply slope_lt₁₂.
      Focus 2.
      assumption.

      Unfocus.
      rewrite <- minimised_slope.
       2: eassumption.

       2: symmetry; eassumption.

       rewrite <- minimised_slope.
        2: eassumption.

        2: eassumption.

        eapply consec_slope_lt.
         2: eassumption.

         2: rewrite Hend; eassumption.

         assumption.

         symmetry; assumption.

     split.
      eapply minimise_slope_sorted in Hms.
       rewrite Hend, <- Heqpts₁ in Hms.
       apply LSorted_inv_2 in Hms.
       destruct Hms as (Hlt, Hms).
       eapply Qlt_le_trans; [ eassumption | idtac ].
       simpl.
       eapply minimise_slope_le in Heqms₁.
        rewrite <- Heqpt₂ in Heqms₁; assumption.

        assumption.

       assumption.

      apply next_ch_points_sorted in Hnp₁.
       rewrite <- Heqpt₂ in Hnp₁; assumption.

       eapply minimise_slope_sorted; [ idtac | eassumption ].
       rewrite <- Hend, Heqpts₁.
       eapply minimise_slope_sorted; eassumption.
Qed.

Lemma zzz : ∀ n pts h αh i αi j αj k αk segjk segkx hsl₁ hsl ms,
  LocallySorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++
        [{| pt := (j, αj); oth := segjk |};
         {| pt := (k, αk); oth := segkx |} … hsl]
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts h αh i αi j αj k αk segjk segkx hsl₁ hsl ms.
intros Hsort Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
apply slope_lt₃₂; [ assumption | idtac ].
revert n ms h αh i αi j αj k αk segjk segkx hsl pts Hms Hnp Hsort Hhjk.
induction hsl₁ as [| hs₁]; intros.
 eapply yyy with (hsl₁ := [ahs (j, αj) segjk]).
  5: simpl.
  5: eassumption.

  3: eassumption.

  assumption.

  assumption.

  apply next_ch_points_hd in Hnp; assumption.

 remember Hnp as HHnp; clear HeqHHnp.
 remember (end_pt ms) as pt₁ in |- *.
 destruct pt₁ as (l, αl).
 eapply Qlt_trans.
  eapply
   yyy
    with
      (l := l)
      (αl := αl)
      (hsl₁ := [hs₁ … hsl₁] ++ [{| pt := (j, αj); oth := segjk |}]).
   3: eassumption.

   4: rewrite <- List.app_assoc.
   4: simpl; eassumption.

   assumption.

   split.
    apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
    apply minimise_slope_le in Hms; [ idtac | assumption ].
    rewrite <- Heqpt₁ in Hms.
    eapply Qlt_le_trans; eassumption.

    rewrite <- Heqpt₁ in Hnp.
    replace l with (fst (l, αl)) by reflexivity.
    replace k with (fst (k, αk)) by reflexivity.
    eapply
     next_ch_points_sorted
      with (hsl₁ := hsl₁ ++ [{| pt := (j, αj); oth := segjk |}]).
     rewrite Heqpt₁.
     eapply minimise_slope_sorted; eassumption.

     simpl in Hnp |- *.
     rewrite <- List.app_assoc.
     simpl; eassumption.

   symmetry in Heqpt₁; assumption.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  remember (rem_pts ms) as pts₁.
  destruct pts₁ as [| (m, αm)]; [ destruct hsl₁; discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
  remember (minimise_slope (end_pt ms) (m, αm) pts₁) as ms₁.
  symmetry in Heqms₁.
  eapply IHhsl₁.
   rewrite <- Heqpt₁ in Heqms₁; eassumption.

   eassumption.

   rewrite Heqpt₁, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.

   split; [ idtac | destruct Hhjk; assumption ].
   rewrite <- Heqpt₁ in HHnp.
   apply next_ch_points_sorted in HHnp; [ assumption | idtac ].
   rewrite Heqpt₁, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bef_j₁ : ∀ n pts j αj segjk k αk segkx hs₁ hsl,
  LocallySorted fst_lt pts
  → next_ch_points n pts =
      [hs₁;
       {| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
(* à nettoyer *)
intros n pts j αj segjk k αk segkx hs₁ hsl.
intros Hpts Hnp h αh Hαh (Hhj, Hjk).
rename Hnp into Hhsl.
destruct n; [ discriminate Hhsl | simpl in Hhsl ].
destruct pts as [| (l, αl)]; [ discriminate Hhsl | idtac ].
destruct pts as [| (m, αm)]; [ discriminate Hhsl | idtac ].
injection Hhsl; clear Hhsl; intros Hnp; intros; subst hs₁.
remember (minimise_slope (l, αl) (m, αm) pts) as ms₁.
symmetry in Heqms₁.
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
rename H into Hend₁.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst l αl.
 eapply zzz with (hsl₁ := []); try eassumption.
 split; assumption.

(**)
 destruct Hαh as [Hαh| Hαh].
  injection Hαh; clear Hαh; intros; subst m αm.
  assert (slope_expr (h, αh) (j, αj) < slope_expr (j, αj) (k, αk))
   as Hhjk.
   apply Qle_lt_trans with (y := slope_expr (l, αl) (j, αj)).
    rewrite <- Hend₁ in |- * at 2.
    remember Heqms₁ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | reflexivity ].
    rewrite <- H.
    eapply minimise_slope_expr_le; eassumption.

    remember Heqms₁ as H; clear HeqH.
    symmetry in Hend₁.
    eapply minimised_slope in H; [ idtac | eassumption ].
    rewrite <- H.
    destruct n; [ discriminate Hnp | simpl in Hnp ].
    remember (rem_pts ms₁) as pts₁.
    destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
    injection Hnp; clear Hnp; intros Hnp; intros.
    remember (minimise_slope (end_pt ms₁) pt₁ pts₁) as ms₂.
    symmetry in Heqms₂.
    subst segjk.
    remember Heqms₂ as H₂; clear HeqH₂.
    eapply minimised_slope in H₂; [ idtac | reflexivity ].
    remember Hnp as H₃; clear HeqH₃.
    apply next_ch_points_hd in H₃.
    rewrite <- H1, <- H₃, <- H₂.
    symmetry in Heqpts₁.
    eapply consec_slope_lt; eassumption.

   eapply ad_hoc_lt_lt₂; try eassumption.
   split; assumption.

  assert (slope_expr (h, αh) (j, αj) < slope_expr (j, αj) (k, αk))
   as Hhjk.
   apply Qle_lt_trans with (y := slope_expr (l, αl) (j, αj)).
    rewrite <- Hend₁ in |- * at 2.
    remember Heqms₁ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | reflexivity ].
    rewrite <- H.
    eapply min_slope_le; try eassumption.

    remember Heqms₁ as H; clear HeqH.
    symmetry in Hend₁.
    eapply minimised_slope in H; [ idtac | eassumption ].
    rewrite <- H.
    destruct n; [ discriminate Hnp | simpl in Hnp ].
    remember (rem_pts ms₁) as pts₁.
    destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
    injection Hnp; clear Hnp; intros Hnp; intros.
    remember (minimise_slope (end_pt ms₁) pt₁ pts₁) as ms₂.
    symmetry in Heqms₂.
    subst segjk.
    remember Heqms₂ as H₂; clear HeqH₂.
    eapply minimised_slope in H₂; [ idtac | reflexivity ].
    remember Hnp as H₃; clear HeqH₃.
    apply next_ch_points_hd in H₃.
    rewrite <- H1, <- H₃, <- H₂.
    symmetry in Heqpts₁.
    eapply consec_slope_lt; eassumption.

   eapply ad_hoc_lt_lt₂; try eassumption.
   split; assumption.
Qed.

(**)
Lemma lt_bef_j : ∀ n pts j αj segjk k αk segkx hsl₁ hsl,
  LocallySorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts j αj segjk k αk segkx hsl₁ hsl.
intros Hpts Hnp h αh Hαh (Hhj, Hjk).
destruct hsl₁ as [| hs₁].
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros; subst pt₁.
 rename H into Hnp.
 rename H0 into Hseg.
 destruct Hαh as [Hαh| Hαh].
  injection Hαh; clear Hαh; intros; subst h αh.
  apply Qlt_irrefl in Hhj; contradiction.

  eapply LSorted_hd in Hpts; [ idtac | eassumption ].
  eapply Qlt_trans in Hhj; [ idtac | eassumption ].
  apply Qlt_irrefl in Hhj; contradiction.

 revert n pts hs₁ Hpts Hnp Hαh.
 induction hsl₁ as [| hs₂]; intros.
  simpl in Hnp.
  eapply conj in Hjk; [ idtac | eexact Hhj ].
  eapply lt_bef_j₁; try eassumption.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
  destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp Hhs₁.
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  destruct Hαh as [Hαh| Hαh].
   subst pt₁ hs₁.
   destruct pt₂.
   eapply conj in Hjk; [ idtac | eexact Hhj ].
   eapply zzz with (hsl₁ := [hs₂ … hsl₁]); eassumption.

bbb.
*)

Lemma lt_bef_j₀ : ∀ n pts j αj segjk k αk segkx hsl,
  LocallySorted fst_lt pts
  → next_ch_points n pts =
      [{| pt := (j, αj); oth := segjk |};
       {| pt := (k, αk); oth := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts j αj segjk k αk segkx hsl.
intros Hpts Hnp h αh Hαh Hhj.
destruct n; [ discriminate Hnp | simpl in Hnp ].
destruct pts as [| (l, αl)]; [ discriminate Hnp | idtac ].
destruct pts as [| (m, αm)]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros; subst l αl.
rename H into Hnp.
rename H0 into Hseg.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst h αh.
 apply Qlt_irrefl in Hhj; contradiction.

 eapply LSorted_hd in Hpts; [ idtac | eassumption ].
 eapply Qlt_trans in Hhj; [ idtac | eassumption ].
 apply Qlt_irrefl in Hhj; contradiction.
Qed.

Lemma qeq_eq : ∀ n pol pts h αh k αk s hsl₁ hsl,
  points_of_ps_polynom α fld pol = pts
  → next_ch_points n pts = hsl₁ ++ [{| pt := (k, αk); oth := s |} … hsl]
    → (h, αh) ∈ pts
      → h == k
        → h = k.
Proof.
intros n pol pts h αh k αk s hsl₁ hsl Hpts Hhsl Hαh Hhk.
apply same_den_qeq_eq; [ idtac | assumption ].
eapply fst_is_int in Hαh; [ idtac | eassumption ].
rewrite Hαh.
assert ((k, αk) ∈ pts) as Hαk.
 apply in_ch_in_pts with (n := n) (s := s).
 rewrite Hhsl.
 apply List.in_app_iff.
 right; left; reflexivity.

 eapply fst_is_int in Hαk; [ idtac | eassumption ].
 rewrite Hαk; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment : ∀ pol pts ns,
  pts = points_of_ps_polynom α fld pol
  → ns ∈ newton_segments fld pol
    → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < αh + h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h αh (Hαh, Hnαh).
remember Hpts as HHpts; clear HeqHHpts; symmetry in HHpts.
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points pts) as hsl.
symmetry in Heqhsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hhsl.
remember (length pts) as n; clear Heqn.
unfold points_of_ps_polynom in Hpts.
apply points_of_polyn_sorted in Hpts.
remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
rename Heqnsl into Hnsl.
symmetry in Hnsl.
revert n pts ns hsl Hpts HHpts Hαh Hhsl Hnsl Hns Hnαh.
induction nsl as [| ns₁]; [ contradiction | intros ].
destruct Hns as [Hns| Hns].
 subst ns₁.
 clear IHnsl.
 destruct hsl as [| ((j, αj), segjk)]; [ discriminate Hnsl | idtac ].
 destruct hsl as [| ((k, αk), segkx)]; [ discriminate Hnsl | idtac ].
 simpl in Hnsl.
 injection Hnsl; clear Hnsl; intros Hns; intros.
 unfold newton_segment_of_pair in Hns; simpl in Hns.
 subst ns; simpl in Hnαh |- *.
 destruct (Qlt_le_dec k h) as [Hgt| Hge].
  eapply lt_aft_k with (hsl₁ := []); eassumption.

  destruct (Qeq_dec h k) as [Heq| Hne].
   remember [{| pt := (j, αj); oth := segjk |}] as x.
   eapply qeq_eq with (hsl₁ := x) in Heq; subst x; simpl; try eassumption.
   exfalso; revert Heq.
   eapply not_k with (hsl₁ := []); eassumption.

   destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
    apply Qle_neq_lt in Hge; [ idtac | assumption ].
    eapply conj in Hge; [ idtac | eassumption ].
    eapply lt_bet_j_and_k with (hsl₁ := []); eassumption.

    destruct (Qeq_dec h j) as [Heq| Hne₂].
     eapply qeq_eq with (hsl₁ := [ ]) in Heq; simpl; try eassumption.
     exfalso; revert Heq.
     eapply not_j with (hsl₁ := []); eassumption.

     apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
     eapply lt_bef_j₀; eassumption.

 clear IHnsl.
 revert n pts ns ns₁ hsl Hpts HHpts Hαh Hhsl Hnsl Hns Hnαh.
 induction nsl as [| ns₂]; [ contradiction | intros ].
 destruct Hns as [Hns| Hns].
  subst ns.
  clear IHnsl.
  destruct hsl as [| hs₁]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((j, αj), segjk)]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((k, αk), segkx)]; [ discriminate Hnsl | idtac ].
  simpl in Hnsl.
  remember Hhsl as Hjk; clear HeqHjk.
  apply next_points_sorted in Hjk; [ idtac | assumption ].
  apply LSorted_inv_2 in Hjk.
  destruct Hjk as (_, Hjk); simpl in Hjk.
  apply LSorted_inv_2 in Hjk.
  destruct Hjk as (Hjk); simpl in Hjk.
  unfold hs_x_lt in Hjk; simpl in Hjk.
  injection Hnsl; clear Hnsl; intros.
  subst ns₁ ns₂; simpl in Hnαh |- *.
  destruct (Qlt_le_dec k h) as [Hlt| Hge].
   eapply lt_aft_k with (hsl₁ := [hs₁]); simpl; try eassumption.

   destruct (Qeq_dec h k) as [Heq| Hne].
    remember [hs₁; {| pt := (j, αj); oth := segjk |} … []] as x.
    eapply qeq_eq with (hsl₁ := x) in Heq; subst x; simpl; try eassumption.
    exfalso; revert Heq.
    eapply not_k with (hsl₁ := [hs₁]); simpl; eassumption.

    destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
     apply Qle_neq_lt in Hge; [ idtac | assumption ].
     eapply conj in Hge; [ idtac | eassumption ].
     eapply lt_bet_j_and_k with (hsl₁ := [hs₁]); simpl; eassumption.

     destruct (Qeq_dec h j) as [Heq| Hne₂].
      eapply qeq_eq with (hsl₁ := [hs₁]) in Heq; simpl; try eassumption.
      exfalso; revert Heq.
      eapply not_j with (hsl₁ := [hs₁]); simpl; eassumption.

      apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
      eapply conj in Hjk; [ idtac | eexact Hge₂ ].
      eapply lt_bef_j₁; eassumption.

  clear IHnsl.
  revert n pts ns ns₁ ns₂ hsl Hpts HHpts Hαh Hhsl Hnsl Hns Hnαh.
  induction nsl as [| ns₃]; [ contradiction | intros ].
  destruct Hns as [Hns| Hns].
   subst ns.
   clear IHnsl.
   destruct hsl as [| hs₁]; [ discriminate Hnsl | idtac ].
   destruct hsl as [| hs₂]; [ discriminate Hnsl | idtac ].
   destruct hsl as [| ((j, αj), segjk)]; [ discriminate Hnsl | idtac ].
   destruct hsl as [| ((k, αk), segkx)]; [ discriminate Hnsl | idtac ].
   simpl in Hnsl.
   remember Hhsl as Hjk; clear HeqHjk.
   apply next_points_sorted in Hjk; [ idtac | assumption ].
   apply LSorted_inv_2 in Hjk.
   destruct Hjk as (_, Hjk); simpl in Hjk.
   apply LSorted_inv_2 in Hjk.
   destruct Hjk as (_, Hjk); simpl in Hjk.
   apply LSorted_inv_2 in Hjk.
   destruct Hjk as (Hjk); simpl in Hjk.
   unfold hs_x_lt in Hjk; simpl in Hjk.
   injection Hnsl; clear Hnsl; intros.
   subst ns₁ ns₂ ns₃; simpl in Hnαh |- *.
   destruct (Qlt_le_dec k h) as [Hlt| Hge].
    eapply lt_aft_k with (hsl₁ := [hs₁; hs₂ … []]); simpl; try eassumption.

    destruct (Qeq_dec h k) as [Heq| Hne].
     remember [hs₁; hs₂; {| pt := (j, αj); oth := segjk |} … []] as x.
     eapply qeq_eq with (hsl₁ := x) in Heq; subst x; simpl; try eassumption.
     exfalso; revert Heq.
     eapply not_k with (hsl₁ := [hs₁; hs₂ … []]); simpl; eassumption.

     destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
      apply Qle_neq_lt in Hge; [ idtac | assumption ].
      eapply conj in Hge; [ idtac | eassumption ].
      eapply lt_bet_j_and_k with (hsl₁ := [hs₁; hs₂ … []]); simpl;
       eassumption.

      destruct (Qeq_dec h j) as [Heq| Hne₂].
       eapply qeq_eq with (hsl₁ := [hs₁; hs₂ … []]) in Heq; simpl;
        try eassumption.
       exfalso; revert Heq.
       eapply not_j with (hsl₁ := [hs₁; hs₂ … []]); simpl; eassumption.

       apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
       eapply conj in Hjk; [ idtac | eexact Hge₂ ].
       eapply lt_bef_j with (hsl₁ := [hs₁; hs₂ … []]); simpl; try eassumption.
bbb.

End convex_hull.

Record branch α :=
  { initial_polynom : polynomial (puiseux_series α);
    cγl : list (α * Q);
    step : nat;
    rem_steps : nat;
    pol : polynomial (puiseux_series α) }.
Arguments initial_polynom : default implicits.
Arguments cγl : default implicits.
Arguments step : default implicits.
Arguments rem_steps : default implicits.
Arguments pol : default implicits.

(*
Definition phony_monom {α β} : monomial (polynomial α β) nat :=
  {| coeff := {| monoms := [] |}; power := 0%nat |}.
Arguments phony_monom : default implicits.

Definition puiseux_iteration k br r m γ β sol_list :=
  let pol :=
    let y :=
      {| monoms :=
           [{| coeff := {| monoms := [{| coeff := r; power := γ |}] |};
               power := 0 |},
            {| coeff := {| monoms := [{| coeff := one k; power := γ |}] |};
               power := 1 |} … [] ] |}
    in
    let pol := apply_poly_dp_pol k br.pol y in
    let pol := pol_div_x_power pol β in
    let pol := cancel_pol_constant_term_if_any fld pol in
    dp_float_round_zero fld pol
  in
  let finite := zero_is_root pol in
  let cγl := [(r, γ) … br.cγl] in
  if br.rem_steps = 0 || finite then
    let sol := make_solution cγl in
    Left [(sol, finite) … sol_list]
  else if br.rem_steps > 0 then Right (pol, cγl)
  else Left sol_list.

Fixpoint puiseux_branch {α} (k : alg_cl_field α) (br : branch α Q)
    (sol_list : list (polynomial α Q * bool)) (γβ : Q * Q) :=
  let (γ, β) := γβ in
  let hl :=
    List.filter
      (λ m,
         let αi := valuation (coeff m) in
         let βi := αi + (Z.of_nat (power m) # 1) * γ in
         Qeq_bool₁ β βi)
      (monoms (pol br))
  in
  let j := power (List.hd (phony_monom α Q) hl) in
  let ml :=
    List.map
      (λ m,
         {| coeff := valuation_coeff k (coeff m);
            power := (power m - j)%nat |})
      hl
  in
  let rl := roots k {| monoms := ml |} in
  List.fold_left
    (λ sol_list rm,
       let (r, m) := rm in
       if eq k r then sol_list
       else
         match puiseux_iteration k br r m γ β sol_list with
         | Right (pol, cγl) => next_step k br sol_list col cγl
         | Left sol_list => sol_list
         end)
    rl sol_list.

Definition puiseux k nb_steps pol :=
  let nsl := newton_segments pol in
  let rem_steps := (nb_steps - 1)%nat in
  List.fold_left
    (λ sol_list γβ₁,
       let br :=
         {| initial_polynom := pol; cγl := []; step := 1%nat;
            rem_steps := rem_steps; pol := pol |}
       in
       puiseux_branch k br sol_list γβ₁)
    nsl [].
*)
