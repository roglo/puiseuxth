(* $Id: NotInSegment.v,v 1.40 2013-05-04 20:23:46 deraugla Exp $ *)

(* points not in newton segment *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import ConvexHull.
Require Import Puiseux.
Require Import NotInSegMisc.

Section convex_hull.

Variable α : Type.
Variable fld : field (puiseux_series α).

Theorem points_not_in_newton_segment : ∀ pol pts ns nsl,
  pts = points_of_ps_polynom α fld pol
  → newton_segments fld pol = [ns … nsl]
    → ∀ h hps, (h, hps) ∈ pts ∧ (h, hps) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < valuation α hps + Qnat h * (γ ns).
Proof.
intros pol pts ns nsl Hpts Hns h hps (Hhps, Hnhps).
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points α pts) as hsl.
destruct hsl as [| ((j, jps), segjx)]; [ discriminate Hns | idtac ].
destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hns | idtac ].
injection Hns; clear Hns; intros; subst ns.
simpl in H |- *.
rename H into Hhsl.
symmetry in Heqhsl.
destruct (lt_dec k h) as [Hlt| Hge].
 unfold points_of_ps_polynom in Hpts.
 apply points_of_polyn_sorted in Hpts.
 remember Hpts as Hpts₂; clear HeqHpts₂.
 eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
 apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
 unfold hs_x_lt in Hlt; simpl in Hlt.
 eapply points_after_k; try eassumption; reflexivity.

 apply not_gt in Hge.
 destruct (eq_nat_dec h k) as [Heq| Hne].
  unfold points_of_ps_polynom in Hpts.
  apply points_of_polyn_sorted in Hpts.
  eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
   subst h hps.
   simpl in Hnhps.
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (_, Hnhps).
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (Hnhps, _).
   exfalso; apply Hnhps; reflexivity.

   eapply in_ch_in_pts with (n := length pts).
   unfold lower_convex_hull_points in Heqhsl; rewrite Heqhsl.
   right; left; reflexivity.

  apply le_neq_lt in Hge; [ idtac | assumption ].
  destruct (lt_dec j h) as [Hlt| Hge₂].
   unfold points_of_ps_polynom in Hpts.
   apply points_of_polyn_sorted in Hpts.
   remember Hpts as Hpts₂; clear HeqHpts₂.
   eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
   unfold hs_x_lt in Hlt; simpl in Hlt.
   eapply points_between_j_and_k; try eassumption; try reflexivity.
    split; assumption.

    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    assumption.

   apply not_gt in Hge₂.
   unfold points_of_ps_polynom in Hpts.
   apply points_of_polyn_sorted in Hpts.
   unfold lower_convex_hull_points in Heqhsl.
   remember (length pts) as n; clear Heqn.
   destruct n.
    simpl in Heqhsl.
    discriminate Heqhsl.

    simpl in Heqhsl.
    destruct pts as [| (l, lps)]; [ discriminate Heqhsl | idtac ].
    destruct pts as [| (m, mps)]; [ discriminate Heqhsl | idtac ].
    injection Heqhsl; clear Heqhsl; intros; subst l lps.
    destruct Hhps as [Hhps| Hhps].
     injection Hhps; clear Hhps; intros; subst h hps.
     simpl in Hnhps.
     apply Decidable.not_or in Hnhps.
     destruct Hnhps as (HH); exfalso; apply HH; reflexivity.

     eapply LocallySorted_hd in Hpts; [ idtac | eassumption ].
     apply le_not_lt in Hge₂; contradiction.
Qed.

Lemma end_in : ∀ pt₁ pt₂ pts ms,
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

(* is there a way to group together the cases c = Eq and c = Gt? *)
Lemma aft_end_in_rem : ∀ pt₁ pt₂ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → ∀ h hps, (h, hps) ∈ [pt₁; pt₂ … pts] 
      → (fst (end_pt ms) < h)%nat
        → (h, hps) ∈ rem_pts ms.
Proof.
intros pt₁ pt₂ pts ms Hsort Hms h hps Hhps Hlt.
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 apply minimise_slope_le in Hms.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₁).
  eapply lt_trans in Hlt₁; [ idtac | eassumption ].
  apply le_not_lt in Hms; contradiction.

  eapply LocallySorted_inv_1; eassumption.

 destruct Hhps as [Hhps| Hhps].
  subst pt₂.
  apply minimise_slope_le in Hms.
   apply le_not_lt in Hms; contradiction.

   eapply LocallySorted_inv_1; eassumption.

  revert pt₁ pt₂ ms Hsort Hms Hhps Hlt.
  induction pts as [| pt₃]; [ contradiction | intros ].
  simpl in Hms.
  remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
  symmetry in Heqc.
  destruct c; subst ms; simpl in Hlt |- *.
   destruct Hhps as [Hhps| Hhps].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply le_not_lt in Heqms₁; contradiction.

     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    constructor.
     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
     eapply lt_trans; eassumption.

   assumption.

   destruct Hhps as [Hhps| Hhps].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply le_not_lt in Heqms₁; contradiction.

     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    constructor.
     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
     eapply lt_trans; eassumption.
Qed.

Lemma consec_end_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms₁
    → minimise_slope α (end_pt ms₁) pt₃ pts₃ = ms₂
      → rem_pts ms₁ = [pt₃ … pts₃]
        → (fst (end_pt ms₁) < fst (end_pt ms₂))%nat.
Proof.
intros pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂ Hsort Hms₁ Hms₂ Hrem₁.
apply minimise_slope_le in Hms₂.
 eapply lt_le_trans; [ idtac | eassumption ].
 apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
 rewrite Hrem₁ in Hms₁.
 apply LocallySorted_inv_2 in Hms₁.
 destruct Hms₁; assumption.

 rewrite <- Hrem₁.
 apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
 eapply LocallySorted_inv_1; eassumption.
Qed.

Lemma j_aft_prev_end :
  ∀ n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j jps segjk k kps segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → rem_pts ms = [pt₃ … pts₃]
      → minimise_slope α (end_pt ms) pt₃ pts₃ = ms₁
        → next_ch_points α n [end_pt ms₁ … rem_pts ms₁] =
          hsl₁ ++
          [{| pt := (j, jps); oth := segjk |};
          {| pt := (k, kps); oth := segkx |} … hsl]
          → (fst (end_pt ms) < j)%nat.
Proof.
intros n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j jps segjk k kps segkx hsl.
intros Hsort Hms Hrem Hms₁ Hnp.
revert pt₁ pt₂ pt₃ pts pts₃ ms ms₁ hsl₁ Hms Hrem Hms₁ Hnp Hsort.
induction n; intros; [ destruct hsl₁; discriminate Hnp | idtac ].
simpl in Hnp.
remember (rem_pts ms₁) as pts₂.
destruct pts₂ as [| pt₄].
 destruct hsl₁ as [| hs₁]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros.
 destruct hsl₁; discriminate H.

 remember (minimise_slope α (end_pt ms₁) pt₄ pts₂) as ms₂.
 symmetry in Heqms₂.
 destruct hsl₁ as [| h₁].
  injection Hnp; clear Hnp; intros; subst segjk.
  rename H into Hnp.
  rename H1 into Hend.
  replace j with (fst (j, jps)) by reflexivity.
  rewrite <- Hend.
  eapply consec_end_lt; eassumption.

  simpl in Hnp.
  injection Hnp; clear Hnp; intros.
  rename H into Hnp; subst h₁.
  assert (fst (end_pt ms₁) < j)%nat.
   symmetry in Heqpts₂.
   eapply IHn; try eassumption.
   rewrite <- Hrem.
   eapply minimise_slope_sorted; eassumption.

   eapply lt_trans; [ idtac | eassumption ].
   eapply consec_end_lt; eassumption.
Qed.

Lemma aft_j_in_rem :
  ∀ n pt₁ pt₂ pts ms hsl₁ j jps segjk k kps segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → next_ch_points α n [end_pt ms … rem_pts ms] =
       hsl₁ ++
       [{| pt := (j, jps); oth := segjk |};
        {| pt := (k, kps); oth := segkx |} … hsl]
      → ∀ h hps, (h, hps) ∈ [pt₁; pt₂ … pts]
        → (j < h)%nat
          → (h, hps) ∈ rem_pts ms.
Proof.
intros n pt₁ pt₂ pts ms hsl₁ j jps segjk k kps segkx hsl.
intros Hsort Hms Hnp h hps Hhps Hjh.
destruct n; [ destruct hsl₁; discriminate Hnp | simpl in Hnp ].
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃].
 destruct hsl₁ as [| hs₁]; [ discriminate Hnp | simpl in Hnp ].
 injection Hnp; clear Hnp; intros; subst hs₁.
 destruct hsl₁; discriminate H.

 remember (minimise_slope α (end_pt ms) pt₃ pts₁) as ms₁.
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
  eapply lt_trans; [ idtac | eassumption ].
  injection Hnp; clear Hnp; intros.
  eapply j_aft_prev_end; eassumption.
Qed.

Lemma lt_aft_k : ∀ n pts hsl₁ hsl j jps segjk k kps segkx,
  LocallySorted fst_lt pts
  → next_ch_points α n pts =
      hsl₁ ++
      [{| pt := (j, jps); oth := segjk |};
       {| pt := (k, kps); oth := segkx |} … hsl]
    → ∀ h hps, (h, hps) ∈ pts
      → (k < h)%nat
        → valuation α jps +
          Qnat j * ((valuation α jps - valuation α kps) / Qnat (k - j)) <
          valuation α hps +
          Qnat h * ((valuation α jps - valuation α kps) / Qnat (k - j)).
Proof.
intros n pts hsl₁ hsl j jps segjk k kps segkx Hsort Hnp h hps Hhps Hkh.
revert n pts Hsort Hnp Hhps.
induction hsl₁ as [| hs₁]; intros.
 remember Hsort as Hsort₂; clear HeqHsort₂.
 eapply points_after_k; try reflexivity; try eassumption.
 apply next_points_sorted in Hnp; [ idtac | assumption ].
 apply LocallySorted_inv_2 in Hnp.
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
  eapply lt_trans; [ idtac | eassumption ].
  apply next_points_sorted in H; [ idtac | assumption ].
  revert H; clear; intros.
  induction hsl₁ as [| hs₁].
   apply LocallySorted_inv_2 in H.
   destruct H; assumption.

   simpl in H.
   apply LocallySorted_inv_1 in H.
   apply IHhsl₁; assumption.
Qed.

Lemma not_k : ∀ n pts hsl₁ hsl j jps segjk k kps segkx,
  LocallySorted fst_lt pts
  → next_ch_points α n pts =
      hsl₁ ++
      [{| pt := (j, jps); oth := segjk |};
       {| pt := (k, kps); oth := segkx |} … hsl]
    → ∀ h hps, (h, hps) ∈ pts
      → (h, hps) ∉ [(j, jps); (k, kps) … segjk]
        → h ≠ k.
Proof.
intros n pts hsl₁ hsl j jps segjk k kps segkx Hsort Hnp h hps Hhps Hnhps Hhk.
eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
 subst h hps.
 simpl in Hnhps.
 apply Decidable.not_or in Hnhps.
 destruct Hnhps as (_, Hnhps).
 apply Decidable.not_or in Hnhps.
 destruct Hnhps as (Hnhps, _).
 exfalso; apply Hnhps; reflexivity.

 eapply in_ch_in_pts with (n := n).
 rewrite Hnp.
 apply List.in_or_app.
 right; right; left; reflexivity.
Qed.

Lemma next_ch_points_sorted : ∀ n pt₁ pt₂ pts h₁ hsl₁ hsl sg,
  LocallySorted fst_lt [pt₁ … pts]
  → next_ch_points α n [pt₁ … pts] =
      [h₁ … hsl₁] ++ [{| pt := pt₂; oth := sg |} … hsl]
    → (fst pt₁ < fst pt₂)%nat.
Proof.
intros n pt₁ pt₂ pts h₁ hsl₁ hsl sg.
intros Hsort Hnp.
revert n pt₁ pt₂ pts h₁ hsl sg Hsort Hnp.
induction hsl₁ as [| h₂]; intros.
 simpl in Hnp.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
 symmetry in Heqms₁.
 apply next_ch_points_hd in Hnp.
 rewrite <- Hnp.
 eapply lt_le_trans.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort; eassumption.

  eapply minimise_slope_le; [ idtac | eassumption ].
  eapply LocallySorted_inv_1; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope α pt₁ pt₃ pts) as ms₂.
 symmetry in Heqms₂.
 eapply IHhsl₁ in Hnp.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort.
  eapply lt_trans; [ eassumption | idtac ].
  apply minimise_slope_le in Heqms₂.
   eapply le_lt_trans; eassumption.

   assumption.

  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bet_j_and_k : ∀ n pts hsl₁ hsl j jps segjk k kps segkx,
  LocallySorted fst_lt pts
  → next_ch_points α n pts =
      hsl₁ ++
      [{| pt := (j, jps); oth := segjk |};
       {| pt := (k, kps); oth := segkx |} … hsl]
    → ∀ h hps, (h, hps) ∈ pts
      → (h, hps) ∉ [(j, jps); (k, kps) … segjk]
        → j < h < k
          → valuation α jps +
            Qnat j * ((valuation α jps - valuation α kps) / Qnat (k - j)) <
            valuation α hps +
            Qnat h * ((valuation α jps - valuation α kps) / Qnat (k - j)).
Proof.
intros n pts hsl₁ hsl j jps segjk k kps segkx Hsort Hnp.
intros h hps Hhps Hnhps Hjhk.
simpl in Hnhps.
apply Decidable.not_or in Hnhps.
destruct Hnhps as (_, Hnhps).
apply Decidable.not_or in Hnhps.
destruct Hnhps as (_, Hnhps).
destruct hsl₁ as [| h₁].
 eapply points_between_j_and_k; try eassumption; try reflexivity.

 revert pts h₁ hsl₁ Hsort Hnp Hhps.
 induction n; intros; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ destruct hsl₁; discriminate Hnp | idtac ].
 remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
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
  eapply lt_trans; [ idtac | destruct Hjhk; eassumption ].
  replace j with (fst (j, jps)) by reflexivity.
  apply next_ch_points_sorted in Hnp; [ assumption | idtac ].
  eapply minimise_slope_sorted; eassumption.
Qed.

Theorem points_not_in_any_newton_segment : ∀ pol pts ns,
  pts = points_of_ps_polynom α fld pol
  → ns ∈ newton_segments fld pol
    → ∀ h hps, (h, hps) ∈ pts ∧ (h, hps) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < valuation α hps + Qnat h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h hps (Hhps, Hnhps).
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points α pts) as hsl.
symmetry in Heqhsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hhsl.
remember (length pts) as n; clear Heqn.
unfold points_of_ps_polynom in Hpts.
apply points_of_polyn_sorted in Hpts.
clear pol.
remember (list_map_pairs (newton_segment_of_pair α) hsl) as nsl.
rename Heqnsl into Hnsl.
symmetry in Hnsl.
revert n pts ns hsl Hpts Hhps Hhsl Hnsl Hns Hnhps.
induction nsl as [| ns₁]; [ contradiction | intros ].
destruct Hns as [Hns| Hns].
 subst ns₁.
 clear IHnsl.
 destruct hsl as [| ((j, jps), segjk)]; [ discriminate Hnsl | idtac ].
 destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hnsl | idtac ].
 simpl in Hnsl.
 injection Hnsl; clear Hnsl; intros.
 rename H0 into Hns.
 unfold newton_segment_of_pair in Hns; simpl in Hns.
 subst ns; simpl in Hnhps |- *.
 destruct (lt_dec k h) as [Hgt| Hge].
  eapply lt_aft_k with (hsl₁ := []); eassumption.

  destruct (eq_nat_dec h k) as [Heq| Hne].
   exfalso; revert Heq.
   eapply not_k with (hsl₁ := []); eassumption.

   apply not_gt in Hge.
   destruct (lt_dec j h) as [Hlt| Hge₂].
    apply le_neq_lt in Hge; [ idtac | assumption ].
    eapply conj in Hge; [ idtac | eassumption ].
    eapply lt_bet_j_and_k with (hsl₁ := []); eassumption.

bbb.
    apply not_gt in Hge₂.
    destruct n; [ discriminate Hhsl | idtac ].
    simpl in Hhsl.
    destruct pts as [| (l, lps)]; [ discriminate Hhsl | idtac ].
    destruct pts as [| (m, mps)]; [ discriminate Hhsl | idtac ].
    injection Hhsl; clear Hhsl; intros; subst l lps.
    rename H into Hhsl.
    rename H0 into Hseg.
    destruct Hhps as [Hhps| Hhps].
     injection Hhps; clear Hhps; intros; subst h hps.
     simpl in Hnhps.
     apply Decidable.not_or in Hnhps.
     destruct Hnhps as (H); exfalso; apply H; reflexivity.

     eapply LocallySorted_hd in Hpts; [ idtac | eassumption ].
     apply le_not_lt in Hge₂; contradiction.

 clear IHnsl.
 revert n pts ns ns₁ hsl Hpts Hhps Hhsl Hnsl Hns Hnhps.
 induction nsl as [| ns₂]; [ contradiction | intros ].
 destruct Hns as [Hns| Hns].
  subst ns.
  clear IHnsl.
  destruct hsl as [| hs₁]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((j, jps), segjk)]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hnsl | idtac ].
  simpl in Hnsl.
  injection Hnsl; clear Hnsl; intros.
  subst ns₁ ns₂; simpl in Hnhps |- *.
  destruct (lt_dec k h) as [Hlt| Hge].
   eapply lt_aft_k with (hsl₁ := [hs₁]); simpl; try eassumption.

   destruct (eq_nat_dec h k) as [Heq| Hne].
    exfalso; revert Heq.
    eapply not_k with (hsl₁ := [hs₁]); simpl; eassumption.

    apply not_gt in Hge.
    destruct (lt_dec j h) as [Hlt| Hge₂].
     apply le_neq_lt in Hge; [ idtac | assumption ].
     eapply conj in Hge; [ idtac | eassumption ].
     eapply lt_bet_j_and_k with (hsl₁ := [hs₁]); simpl; eassumption.

     apply not_gt in Hge₂.
     clear Hge Hne.
     destruct n; [ discriminate Hhsl | idtac ].
     simpl in Hhsl.
     destruct pts as [| (l, lps)]; [ discriminate Hhsl | idtac ].
     destruct pts as [| (m, mps)]; [ discriminate Hhsl | idtac ].
     injection Hhsl; clear Hhsl; intros.
     rename H0 into Hnp.
     subst hs₁.
     remember (minimise_slope α (l, lps) (m, mps) pts) as ms₁.
     symmetry in Heqms₁.
     destruct (eq_nat_dec h j) as [Heq| Hne].
      symmetry in Heq.
      eapply same_k_same_kps with (jps := jps) in Hhps; try eassumption.
       subst h hps.
       apply Decidable.not_or in Hnhps.
       destruct Hnhps as (Hnhps); exfalso; apply Hnhps; reflexivity.

       rename H into Hhsl.
       remember Hnp as H; clear HeqH.
       apply next_ch_points_hd in H.
       right; rewrite <- H.
       eapply end_in; eassumption.

      rename H into Hhsl.
      remember Hnp as H; clear HeqH.
      apply next_ch_points_hd in H.
      rename H into Hend₁.
      destruct Hhps as [Hhps| Hhps].
       injection Hhps; clear Hhps; intros; subst l lps.
       symmetry in Hend₁.
       remember Heqms₁ as H; clear HeqH.
       eapply minimised_slope in H; [ idtac | eassumption ].

bbb.
     Focus 2.
     clear IHnsl.
     revert n pts ns ns₁ hsl Hpts Hhps Hhsl Hnsl Hns Hnhps.
     induction nsl as [| ns₃]; [ contradiction | intros ].
     destruct Hns as [Hns| Hns].
      subst ns.
      clear IHnsl.
      destruct hsl as [| hs₁]; [ discriminate Hnsl | idtac ].
      destruct hsl as [| hs₂]; [ discriminate Hnsl | idtac ].
      destruct hsl as [| ((j, jps), segjk)]; [ discriminate Hnsl | idtac ].
      destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hnsl | idtac ].
      simpl in Hnsl.
      injection Hnsl; clear Hnsl; intros.
      subst ns₁ ns₂ ns₃; simpl in Hnhps |- *.
      destruct (lt_dec k h) as [Hlt| Hge].
       eapply lt_aft_k with (hsl₁ := [hs₁; hs₂ … []]); simpl; try eassumption.

       apply not_gt in Hge.
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
