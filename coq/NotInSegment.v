(* NotInSegment.v *)

(* points not in newton segment *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import Misc.
Require Import Slope_base.
Require Import SlopeMisc.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Newton.
Require Import NotInSegMisc.

(* is there a way to group together the cases c = Eq and c = Gt? *)
Lemma aft_end_in_rem : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → ∀ h αh, (h, αh) ∈ [pt₁; pt₂ … pts] 
      → fst (end_pt ms) < h
        → (h, αh) ∈ rem_pts ms.
Proof.
intros pt₁ pt₂ pts ms Hsort Hms h αh Hαh Hlt.
destruct Hαh as [Hαh| Hαh].
 subst pt₁.
 apply minimise_slope_le in Hms.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₁).
  eapply Qlt_trans in Hlt₁; [ idtac | eassumption ].
  apply Qle_not_lt in Hms; contradiction.

  eapply Sorted_inv_1; eassumption.

 destruct Hαh as [Hαh| Hαh].
  subst pt₂.
  apply minimise_slope_le in Hms.
   apply Qle_not_lt in Hms; contradiction.

   eapply Sorted_inv_1; eassumption.

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

     do 2 apply Sorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   assumption.

   destruct Hαh as [Hαh| Hαh].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply Qle_not_lt in Heqms₁; contradiction.

     do 2 apply Sorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma consec_end_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  Sorted fst_lt [pt₁; pt₂ … pts]
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
 apply Sorted_inv_2 in Hms₁.
 destruct Hms₁; assumption.

 rewrite <- Hrem₁.
 apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
 eapply Sorted_inv_1; eassumption.
Qed.

Lemma min_slope_lt : ∀ pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃,
  Sorted fst_lt [pt₁; pt₂; pt₃ … pts]
  → minimise_slope pt₁ pt₃ pts = ms₁₃
    → minimise_slope pt₂ pt₃ pts = ms₂₃
      → slope_expr pt₁ pt₂ < slope ms₁₃
        → slope ms₁₃ < slope ms₂₃.
Proof.
intros pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃ Hsort Hms₁₃ Hms₂₃ Heqc.
revert pt₁ pt₂ pt₃ ms₂₃ ms₁₃ Heqc Hsort Hms₁₃ Hms₂₃.
induction pts as [| pt₄]; intros.
 subst ms₁₃ ms₂₃; simpl in Heqc |- *.
 apply slope_lt_1213_1323; [ idtac | assumption ].
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
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
   eapply Sorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   rewrite <- Heqc₁.
   rewrite <- Heqc₁ in Heqc.
   apply slope_lt_1213_1323; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply IHpts; try eassumption.
   eapply Sorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  apply Qlt_alt in Heqc₁.
  subst ms₁₃; simpl in Heqc |- *.
  destruct c₂.
   apply Qeq_alt in Heqc₂.
   subst ms₂₃; simpl.
   rewrite <- Heqc₂.
   apply slope_lt_1213_1323; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   apply slope_lt_1213_1323; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply Qlt_trans; [ eassumption | idtac ].
   eapply IHpts with (pt₂ := pt₂); try eassumption.
    eapply Qlt_trans; eassumption.

    eapply Sorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  apply Qgt_alt in Heqc₁.
  subst ms₁₃.
  destruct c₂.
   apply Qeq_alt in Heqc₂.
   subst ms₂₃; simpl.
   eapply IHpts; try eassumption.
   eapply Sorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   apply Qlt_alt in Heqc₂.
   subst ms₂₃; simpl.
   eapply Qlt_trans; [ eassumption | idtac ].
   eapply Qlt_trans in Heqc₁; [ idtac | eassumption ].
   apply slope_lt_1213_1323; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   apply Qgt_alt in Heqc₂.
   move Hms₂₃ at top; subst ms₂₄.
   eapply IHpts; try eassumption.
   eapply Sorted_minus_3rd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma consec_slope_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  Sorted fst_lt [pt₁; pt₂ … pts]
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
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms₁.
  simpl in Hms₂, Hrem₁ |- *.
  injection Hrem₁; clear Hrem₁; intros; subst pt₄ pts₃.
  apply Qlt_alt in Heqc.
  eapply Qlt_trans; [ eassumption | idtac ].
  eapply min_slope_lt; eassumption.

  subst ms₁.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma j_aft_prev_end :
  ∀ n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j αj segjk k αk segkx hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → rem_pts ms = [pt₃ … pts₃]
      → minimise_slope (end_pt ms) pt₃ pts₃ = ms₁
        → next_ch_points n [end_pt ms₁ … rem_pts ms₁] =
          hsl₁ ++
          [{| vert := (j, αj); edge := segjk |};
          {| vert := (k, αk); edge := segkx |} … hsl]
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
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → next_ch_points n [end_pt ms … rem_pts ms] =
       hsl₁ ++
       [{| vert := (j, αj); edge := segjk |};
        {| vert := (k, αk); edge := segkx |} … hsl]
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
  Sorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
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
 apply Sorted_inv_2 in Hnp.
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
   apply Sorted_inv_2 in H.
   destruct H; assumption.

   simpl in H.
   apply Sorted_inv_1 in H.
   apply IHhsl₁; assumption.
Qed.

Lemma not_k : ∀ n pts hsl₁ hsl j αj segjk k αk segkx,
  Sorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … segjk]
        → h ≠ k.
Proof.
intros n pts hsl₁ hsl j αj segjk k αk segkx.
intros Hpts Hnp h αh Hαh Hnαh Hhk.
eapply sorted_qeq_eq with (k := k) (αk := αk) in Hαh.
 rewrite Hαh in Hnαh; simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (_, Hnαh).
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 negation Hnαh.

 assumption.

 eapply in_ch_in_pts with (n := n).
 rewrite Hnp.
 apply List.in_or_app.
 right; right; left; reflexivity.

 subst h; reflexivity.
Qed.

Lemma next_ch_points_sorted : ∀ n pt₁ pt₂ pts h₁ hsl₁ hsl sg,
  Sorted fst_lt [pt₁ … pts]
  → next_ch_points n [pt₁ … pts] =
      [h₁ … hsl₁] ++ [{| vert := pt₂; edge := sg |} … hsl]
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
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; eassumption.

  eapply minimise_slope_le; [ idtac | eassumption ].
  eapply Sorted_inv_1; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₂.
 symmetry in Heqms₂.
 eapply IHhsl₁ in Hnp.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort.
  eapply Qlt_trans; [ eassumption | idtac ].
  apply minimise_slope_le in Heqms₂.
   eapply Qle_lt_trans; eassumption.

   assumption.

  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bet_j_and_k : ∀ n pts hsl₁ hsl j αj segjk k αk segkx,
  Sorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
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

Lemma not_j : ∀ n pts hsl₁ j αj k αk segjk segkx hsl,
  Sorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … segjk]
        → h ≠ j.
Proof.
intros n pts hsl₁ j αj k αk segjk segkx hsl.
intros Hpts Hnp h αh Hαh Hnαh Hne.
eapply sorted_qeq_eq with (k := j) (αk := αj) in Hαh; try eassumption.
 rewrite Hαh in Hnαh.
 simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 negation Hnαh.

 eapply in_ch_in_pts with (n := n).
 rewrite Hnp.
 apply List.in_or_app.
 right; left; reflexivity.

 subst h; reflexivity.
Qed.

Lemma slope_expr_eq : ∀ pt₁ pt₂ pt₃ pts,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → pt₃ ∈ pts
    → slope_expr pt₁ pt₂ == slope_expr pt₁ pt₃
      → slope_expr pt₁ pt₂ == slope_expr pt₂ pt₃.
Proof.
intros pt₁ pt₂ pt₃ pts Hsort Hin H.
apply slope_eq; [ idtac | idtac | idtac | assumption ].
 intros HH.
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
 unfold fst_lt in Hlt.
 rewrite HH in Hlt.
 apply Qlt_irrefl in Hlt; contradiction.

 intros HH.
 clear H.
 induction pts as [| pt₄]; [ contradiction | idtac ].
 simpl in Hin.
 destruct Hin as [Hin| Hin].
  subst pt₄.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  unfold fst_lt in Hlt₂.
  rewrite HH in Hlt₂.
  apply Qlt_irrefl in Hlt₂; contradiction.

  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 intros HH.
 clear H.
 induction pts as [| pt₄]; [ contradiction | idtac ].
 simpl in Hin.
 destruct Hin as [Hin| Hin].
  subst pt₄.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  unfold fst_lt in Hlt₂.
  rewrite HH in Hlt₂.
  eapply Qlt_trans in Hlt₂; [ idtac | eassumption ].
  apply Qlt_irrefl in Hlt₂; contradiction.

  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

(* réunion avec 'min_slope_le' ? *)
Lemma minimise_slope_expr_le : ∀ pt₁ pt₂ pt₃ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
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
  apply Sorted_inv_2 in Hsort; destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (H).
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
   apply slope_lt_1312_2313; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   split; assumption.

   simpl in Heqms₁.
   remember (minimise_slope pt₁ pt₅ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr pt₁ pt₄ ?= slope ms₂) as c₁.
   symmetry in Heqc₁.
   destruct c₁.
    subst ms; simpl in Hend, Heqc |- *.
    eapply IHpts; try eassumption.
    eapply Sorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

    subst ms; simpl in Hend, Heqc |- *.
    subst pt₄.
    apply Qlt_le_weak.
    apply slope_lt_1312_2313; [ idtac | assumption ].
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    split; assumption.

    subst ms; simpl in Hend |- *.
    eapply IHpts; try eassumption.
    eapply Sorted_minus_3rd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

(* réunion avec 'minimise_slope_expr_le' ? *)
Lemma min_slope_le : ∀ pt₁ pt₂ pt₃ pt₄ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
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
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 subst ms; simpl in Hend |- *; subst pt₄.
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
 eapply Qlt_trans in Hlt₂; [ idtac | eassumption ].
 exfalso; revert Hpt.
 eapply Sorted_not_in; [ idtac | idtac | eassumption | eassumption ].
  intros x H; apply Qlt_irrefl in H; contradiction.

  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 move Hms at top; subst ms₁.
 destruct Hpt as [Hpt| Hpt].
  subst pt₅.
  eapply minimise_slope_expr_le; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma sl_lt_bef_j_in_ch : ∀ n pts h αh i αi j αj k αk segkx hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (j, αj)
        → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [{| vert := (k, αk); edge := segkx |} … hsl]
          → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts h αh i αi j αj k αk segkx hsl₁ hsl ms.
intros Hsort (Hhj, Hjk) Hms Hend Hnp.
revert n pts h αh i αi k αk j αj segkx hsl ms Hsort Hhj Hjk Hms Hnp Hend.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 rewrite Hend in Hnp.
 destruct pts₁ as [| pt₁].
  injection Hnp; clear Hnp; intros; subst j αj.
  apply Qlt_irrefl in Hjk; contradiction.

  injection Hnp; clear Hnp; intros; subst j αj.
  apply Qlt_irrefl in Hjk; contradiction.

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
  apply slope_lt_1223_1323; [ split; assumption | idtac ].
  symmetry in Hend.
  rewrite <- minimised_slope; try eassumption.
  symmetry in Heqpts₁.
  rewrite <- minimised_slope; try eassumption.
  rewrite Hend in Heqms₁.
  eapply consec_slope_lt; eassumption.

  remember Hnp as Hnp₁; clear HeqHnp₁.
  symmetry in Heqpt₂.
  eapply IHhsl₁ with (h := j) (j := p) in Hnp; try eassumption.
   apply slope_lt_1223_1323; [ split; assumption | idtac ].
   apply Qlt_trans with (y := slope_expr (j, αj) (p, αp)).
    symmetry in Hend.
    rewrite <- minimised_slope; try eassumption.
    symmetry in Heqpt₂.
    rewrite <- minimised_slope; try eassumption.
    symmetry in Heqpts₁.
    rewrite Hend in Heqms₁.
    eapply consec_slope_lt; eassumption.

    apply slope_lt_1323_1213; [ idtac | assumption ].
    split.
     eapply minimise_slope_sorted in Hms; [ idtac | assumption ].
     rewrite Hend, <- Heqpts₁ in Hms.
     apply Sorted_inv_2 in Hms.
     destruct Hms as (Hlt, Hms).
     eapply Qlt_le_trans; [ eassumption | idtac ].
     simpl.
     eapply minimise_slope_le in Heqms₁; [ idtac | eassumption ].
     rewrite Heqpt₂ in Heqms₁; assumption.

     apply next_ch_points_sorted in Hnp₁.
      rewrite Heqpt₂ in Hnp₁; assumption.

      eapply minimise_slope_sorted; [ idtac | eassumption ].
      rewrite <- Hend, Heqpts₁.
      eapply minimise_slope_sorted; eassumption.

   rewrite <- Hend, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.

   apply Qlt_le_trans with (y := m).
    apply minimise_slope_sorted in Hms; [ idtac | assumption ].
    rewrite Hend, <- Heqpts₁ in Hms.
    apply Sorted_inv_2 in Hms; destruct Hms; assumption.

    apply minimise_slope_le in Heqms₁.
     rewrite Heqpt₂ in Heqms₁; assumption.

     apply minimise_slope_sorted in Hms; [ idtac | assumption ].
     rewrite <- Heqpts₁ in Hms.
     eapply Sorted_inv_1; eassumption.

   apply next_ch_points_sorted in Hnp.
    rewrite Heqpt₂ in Hnp; assumption.

    eapply minimise_slope_sorted; [ idtac | eassumption ].
    rewrite <- Hend, Heqpts₁.
    eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_expr_bef_j_in_ch :
  ∀ n pts h αh i αi j αj k αk segjk segkx hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++
        [{| vert := (j, αj); edge := segjk |};
         {| vert := (k, αk); edge := segkx |} … hsl]
        → slope_expr (h, αh) (j, αj) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts h αh i αi j αj k αk segjk segkx hsl₁ hsl ms.
intros Hsort Hhjk Hms Hnp.
apply slope_lt_1323_1223; [ assumption | idtac ].
revert n ms h αh i αi j αj k αk segjk segkx hsl pts Hms Hnp Hsort Hhjk.
induction hsl₁ as [| hs₁]; intros.
 remember Hnp as H; clear HeqH.
 eapply next_ch_points_hd in H.
 eapply sl_lt_bef_j_in_ch with (hsl₁ := [ahs (j, αj) segjk]); try eassumption.
 simpl; eassumption.

 remember Hnp as HHnp; clear HeqHHnp.
 remember (end_pt ms) as pt₁ in |- *.
 destruct pt₁ as (l, αl).
 apply Qlt_trans with (y := slope_expr (l, αl) (k, αk)).
  remember ([hs₁ … hsl₁] ++ [{| vert := (j, αj); edge := segjk |}]) as hsl₂.
  symmetry in Heqpt₁.
  eapply sl_lt_bef_j_in_ch with (j := l) (hsl₁ := hsl₂); try eassumption.
   split.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
    apply minimise_slope_le in Hms; [ idtac | assumption ].
    rewrite Heqpt₁ in Hms.
    eapply Qlt_le_trans; eassumption.

    rewrite Heqpt₁ in Hnp.
    replace l with (fst (l, αl)) by reflexivity.
    replace k with (fst (k, αk)) by reflexivity.
    eapply
     next_ch_points_sorted
      with (hsl₁ := hsl₁ ++ [{| vert := (j, αj); edge := segjk |}]).
     rewrite <- Heqpt₁.
     eapply minimise_slope_sorted; eassumption.

     simpl in Hnp |- *.
     rewrite <- List.app_assoc; simpl; eassumption.

   subst hsl₂; rewrite <- List.app_assoc; simpl; eassumption.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  remember (rem_pts ms) as pts₁.
  destruct pts₁ as [| (m, αm)]; [ destruct hsl₁; discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
  remember (minimise_slope (end_pt ms) (m, αm) pts₁) as ms₁.
  symmetry in Heqms₁.
  rewrite <- Heqpt₁ in Heqms₁.
  eapply IHhsl₁; try eassumption.
   rewrite Heqpt₁, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.

   split; [ idtac | destruct Hhjk; assumption ].
   rewrite <- Heqpt₁ in HHnp.
   apply next_ch_points_sorted in HHnp; [ assumption | idtac ].
   rewrite Heqpt₁, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bef_j_in_ch : ∀ n pts h αh pt₂ j αj k αk segjk segkx hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); pt₂ … pts]
  → h < j < k
    → minimise_slope (h, αh) pt₂ pts = ms
      → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++
        [{| vert := (j, αj); edge := segjk |};
         {| vert := (k, αk); edge := segkx |} … hsl]
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts h αh (i, αi) j αj k αk segjk segkx hsl₁ hsl ms.
intros Hsort Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
eapply lt_expr_bef_j_in_ch; eassumption.
Qed.

Lemma sl_lt_bef_j_any : ∀ n pts pt₁ pt₂ h αh j αj k αk segkx hsl₁ hsl ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → end_pt ms = (j, αj)
          → next_ch_points n [end_pt ms … rem_pts ms] =
              hsl₁ ++ [{| vert := (k, αk); edge := segkx |} … hsl]
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts (g, αg) pt₂ h αh j αj k αk segkx hsl₁ hsl ms.
intros Hsort Hh (Hhj, Hjk) Hms Hend Hnp.
apply slope_lt_1223_1323; [ split; assumption | idtac ].
apply Qle_lt_trans with (y := slope_expr (g, αg) (j, αj)).
 remember Hms as Hms₁; clear HeqHms₁.
 symmetry in Hend.
 eapply minimised_slope in Hms; [ idtac | eassumption ].
 rewrite <- Hms.
 symmetry in Hend.
 destruct Hh as [Hh| Hh].
  subst pt₂.
  eapply minimise_slope_expr_le; eassumption.

  eapply min_slope_le; eassumption.

 apply slope_lt_1323_1223.
  split; [ idtac | assumption ].
  apply Sorted_inv_2 in Hsort.
  eapply Qlt_trans; [ idtac | eassumption ].
  destruct Hsort as (Hle, Hsort).
  eapply Qlt_le_trans; [ eassumption | idtac ].
  replace h with (fst (h, αh)) by reflexivity.
  eapply Sorted_in; eassumption.

  destruct hsl₁ as [| hs₁].
   remember Hnp as HHnp; clear HeqHHnp.
   apply next_ch_points_hd in Hnp.
   rewrite Hend in Hnp.
   injection Hnp; clear Hnp; intros; subst j αj.
   apply Qlt_irrefl in Hjk; contradiction.

   destruct pt₂ as (i, αi).
   eapply sl_lt_bef_j_in_ch; try eassumption.
   split; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort.
   destruct Hsort.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   apply minimise_slope_le in Hms; [ idtac | assumption ].
   rewrite Hend in Hms; assumption.
Qed.

Lemma sl_lt_1st_ns_any_hp : ∀ n pt₁ pt₂ pt₃ pt₄ pts pts₁ ms₁ ms₂ sg₄ hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → rem_pts ms₁ = [pt₃ … pts₁]
      → minimise_slope (end_pt ms₁) pt₃ pts₁ = ms₂
        → next_ch_points n [end_pt ms₂ … rem_pts ms₂] =
          hsl₁ ++ [ahs pt₄ sg₄ … hsl]
          → slope_expr pt₁ (end_pt ms₁) < slope_expr (end_pt ms₁) pt₄.
Proof.
intros n pt₁ pt₂ pt₃ pt₄ pts pts₁ ms₁ ms₂ sg₄ hsl₁ hsl.
intros Hsort Hms₁ Hrem₁ Hms₂ Hnp.
revert n pt₁ pt₂ pt₃ pts pts₁ ms₁ ms₂ Hsort Hms₁ Hrem₁ Hms₂ Hnp.
induction hsl₁ as [| hs₁]; intros.
 apply next_ch_points_hd in Hnp.
 rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
 symmetry in Hnp.
 rewrite <- minimised_slope; [ idtac | eassumption | assumption ].
 eapply consec_slope_lt; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms₂) as pts₂.
 destruct pts₂ as [| pt₅]; [ destruct hsl₁; discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope (end_pt ms₂) pt₅ pts₂) as ms₃.
 symmetry in Heqms₃.
 apply Qlt_trans with (y := slope_expr (end_pt ms₁) (end_pt ms₂)).
  rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  symmetry in Heqpts₂.
  eapply consec_slope_lt; eassumption.

  apply slope_lt_1223_1213.
   split.
    apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
    rewrite Hrem₁ in Hms₁.
    apply Sorted_inv_2 in Hms₁; destruct Hms₁ as (Hlt, Hms₁).
    eapply Qlt_le_trans; [ eassumption | idtac ].
    apply minimise_slope_le in Hms₂; assumption.

    remember Hms₂ as HHms₂; clear HeqHHms₂.
    apply minimise_slope_sorted in Hms₂.
     rewrite <- Heqpts₂ in Hms₂.
     apply Sorted_inv_2 in Hms₂; destruct Hms₂ as (Hlt, Hms₂).
     eapply Qlt_le_trans; [ eassumption | idtac ].
     remember Heqms₃ as Hms₃; clear HeqHms₃.
     apply minimise_slope_le in Heqms₃; [ idtac | assumption ].
     eapply Qle_trans; [ eassumption | idtac ].
     apply next_ch_points_le in Hnp; [ assumption | idtac ].
     eapply minimise_slope_sorted; [ idtac | eassumption ].
     rewrite Heqpts₂.
     eapply minimise_slope_sorted; [ idtac | eassumption ].
     rewrite <- Hrem₁.
     eapply minimise_slope_sorted; eassumption.

     rewrite <- Hrem₁.
     eapply minimise_slope_sorted; eassumption.

   symmetry in Heqpts₂.
   eapply IHhsl₁; try eassumption.
   rewrite <- Hrem₁.
   eapply minimise_slope_sorted; eassumption.
Qed.

Lemma sl_lt_any_ns : ∀ n pt₁ pt₂ pt₃ pt₄ pts sg₃ sg₄ ms hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++ [ahs pt₃ sg₃; ahs pt₄ sg₄ … hsl]
      → slope_expr pt₁ pt₃ < slope_expr pt₃ pt₄.
Proof.
intros n pt₁ pt₂ pt₃ pt₄ pts sg₃ sg₄ ms hsl₁ hsl.
intros Hsort Hms Hnp.
revert n pt₁ pt₂ pts ms Hnp Hsort Hms.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 destruct pts₁ as [| pt₅]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros H Hend; subst sg₃.
 remember (minimise_slope (end_pt ms) pt₅ pts₁) as ms₁.
 symmetry in Heqms₁.
 symmetry in Heqpts₁.
 eapply consec_slope_lt in Hsort; try eassumption.
 eapply minimised_slope in Hms; [ idtac | reflexivity ].
 rewrite Hms, Hend in Hsort.
 eapply minimised_slope in Heqms₁; [ idtac | reflexivity ].
 apply next_ch_points_hd in Hnp.
 rewrite Heqms₁, Hend, Hnp in Hsort.
 assumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 destruct pts₁ as [| pt₅]; [ destruct hsl₁; discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros H; subst hs₁.
 remember (minimise_slope (end_pt ms) pt₅ pts₁) as ms₁.
 symmetry in Heqms₁.
 remember Heqms₁ as Hms₁; clear HeqHms₁.
 eapply IHhsl₁ in Heqms₁; try eassumption.
  eapply Qlt_trans; [ idtac | eassumption ].
  apply slope_lt_1223_1323.
   split.
    eapply Qlt_le_trans.
     apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
     unfold fst_lt in Hlt; simpl in Hlt; eassumption.

     eapply Sorted_inv_1 in Hsort.
     apply minimise_slope_le in Hms; assumption.

    remember Hms as Hms₂; clear HeqHms₂.
    apply minimise_slope_sorted in Hms; [ idtac | assumption ].
    rewrite <- Heqpts₁ in Hms.
    apply Sorted_inv_2 in Hms; destruct Hms as (Hlt, Hms).
    eapply Qlt_le_trans; [ eassumption | idtac ].
    remember Hms₁ as Hms₃; clear HeqHms₃.
    apply minimise_slope_le in Hms₁; [ idtac | eassumption ].
    eapply Qle_trans; [ eassumption | idtac ].
    apply next_ch_points_le in Hnp; [ assumption | idtac ].
    eapply minimise_slope_sorted; [ idtac | eassumption ].
    rewrite Heqpts₁.
    eapply minimise_slope_sorted; eassumption.

   symmetry in Heqpts₁.
   eapply sl_lt_1st_ns_any_hp; eassumption.

  rewrite Heqpts₁.
  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma sl_lt_bef_j : ∀ n pt₁ pt₂ pts h αh j αj k αk ms segjk segkx hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → fst pt₁ < h <= fst (end_pt ms)
          → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [ahs (j, αj) segjk; ahs (k, αk) segkx … hsl]
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n (g, αg) pt₂ pts h αh j αj k αk ms segjk segkx hsl₁ hsl.
intros Hsort Hh (Hhj, Hjk) Hms (H₁h, Hhe) Hnp.
destruct hsl₁ as [| hs₁]; intros.
 remember Hnp as H; clear HeqH.
 eapply next_ch_points_hd in H.
 eapply sl_lt_bef_j_any with (hsl₁ := [ahs (j, αj) segjk]); try eassumption.
  split; assumption.

  simpl; eassumption.

 remember Hnp as HHnp; clear HeqHHnp.
 remember (end_pt ms) as pt₁ in |- *.
 destruct pt₁ as (l, αl).
 rewrite <- Heqpt₁ in Hhe; simpl in H₁h, Hhe.
 destruct (Qeq_dec h l) as [Heq| Hne].
  eapply sorted_qeq_eq with (αj := αh) (αk := αl) in Heq; try eassumption.
   rewrite Heq.
   apply slope_lt_1223_1323.
    injection Heq; intros; subst l; split; assumption.

    destruct n; [ discriminate Hnp | simpl in Hnp ].
    remember (rem_pts ms) as pts₁.
    destruct pts₁ as [| (m, αm)]; [ destruct hsl₁; discriminate Hnp | idtac ].
    remember (minimise_slope (end_pt ms) (m, αm) pts₁) as ms₁.
    symmetry in Heqms₁.
    rewrite <- Heqpt₁ in Heqms₁.
    injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
    eapply lt_expr_bef_j_in_ch; try eassumption.
     rewrite Heqpt₁, Heqpts₁.
     eapply minimise_slope_sorted; eassumption.

     injection Heq; intros; subst l; split; assumption.

   right; assumption.

   apply end_pt_in in Hms.
   rewrite <- Heqpt₁ in Hms.
   right; assumption.

  apply slope_lt_1223_1323; [ split; assumption | idtac ].
  apply Qlt_trans with (y := slope_expr (l, αl) (j, αj)).
   symmetry in Heqpt₁.
   apply Qle_neq_lt in Hhe; [ idtac | assumption ].
   eapply sl_lt_bef_j_any; try eassumption.
   split; [ assumption | idtac ].
   apply next_ch_points_sorted in Hnp.
    rewrite Heqpt₁ in Hnp; assumption.

    eapply minimise_slope_sorted; eassumption.

   destruct n; [ discriminate Hnp | idtac ].
   simpl in Hnp.
   remember (rem_pts ms) as pts₁.
   destruct pts₁ as [| pt₁]; [ destruct hsl₁; discriminate Hnp | idtac ].
   injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
   remember (minimise_slope (end_pt ms) pt₁ pts₁) as ms₁.
   symmetry in Heqms₁.
   rewrite <- Heqpt₁ in Heqms₁.
   apply minimise_slope_sorted in Hms; [ idtac | assumption ].
   rewrite <- Heqpt₁, <- Heqpts₁ in Hms.
   eapply sl_lt_any_ns; try eassumption.
Qed.

Lemma lt_bef_j_aft_1st_ch :
  ∀ n pts pt₁ pt₂ h αh j αj k αk segjk segkx hsl₁ hsl ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → next_ch_points n [end_pt ms … rem_pts ms] =
          hsl₁ ++
          [{| vert := (j, αj); edge := segjk |};
           {| vert := (k, αk); edge := segkx |} … hsl]
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts pt₁ pt₂ h αh j αj k αk segjk segkx hsl₁ hsl ms.
intros Hsort Hh Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
apply slope_lt_1323_1223; [ assumption | idtac ].
remember (end_pt ms) as pt₃ in |- *.
destruct pt₃ as (l, αl).
destruct (Qlt_le_dec l h) as [Hgt| Hle].
 revert n pt₁ pt₂ h αh j αj k αk segjk segkx pts hsl ms l αl Hsort Hh Hhjk
  Hms Hnp Heqpt₃ Hgt.
 induction hsl₁ as [| hs₁]; intros.
  remember Hnp as H; clear HeqH.
  eapply next_ch_points_hd in H.
  eapply sl_lt_bef_j_any with (hsl₁ := [ahs (j, αj) segjk]); try eassumption.
  simpl; eassumption.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  remember (rem_pts ms) as pts₁.
  destruct pts₁ as [| pt₄]; [ destruct hsl₁; discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
  remember (minimise_slope (end_pt ms) pt₄ pts₁) as ms₁.
  symmetry in Heqms₁.
  remember (end_pt ms₁) as pt₅ in |- *.
  destruct pt₅ as (m, αm).
  destruct (Qlt_le_dec m h) as [Hgt₁| Hle₁].
   eapply IHhsl₁ with (pt₂ := pt₄); try eassumption.
    rewrite Heqpts₁.
    eapply minimise_slope_sorted; eassumption.

    rewrite Heqpts₁.
    eapply aft_end_in_rem; try eassumption; [ right; assumption | idtac ].
    rewrite <- Heqpt₃; assumption.

   eapply sl_lt_bef_j with (pt₂ := pt₄); try eassumption.
    rewrite Heqpts₁.
    eapply minimise_slope_sorted; eassumption.

    rewrite Heqpts₁.
    eapply aft_end_in_rem; try eassumption; [ right; assumption | idtac ].
    rewrite <- Heqpt₃; assumption.

    rewrite <- Heqpt₃, <- Heqpt₅; split; assumption.

 eapply sl_lt_bef_j; try eassumption.
 rewrite <- Heqpt₃.
 split; [ idtac | assumption ].
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
 eapply Qlt_le_trans; [ eassumption | idtac ].
 replace h with (fst (h, αh)) by reflexivity.
 eapply Sorted_in; eassumption.
Qed.

Lemma lt_bef_j₁ : ∀ n pts j αj segjk k αk segkx hs₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts =
      [hs₁;
       {| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
(* à nettoyer *)
intros n pts j αj segjk k αk segkx hs₁ hsl.
intros Hsort Hnp h αh Hαh (Hhj, Hjk).
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
 eapply lt_bef_j_in_ch with (hsl₁ := []); try eassumption.
 split; assumption.

 destruct Hαh as [Hαh| Hαh].
  injection Hαh; clear Hαh; intros; subst m αm.
  eapply conj in Hjk; [ idtac | eexact Hhj ].
  eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
  do 2 rewrite fold_slope_expr.
  apply slope_lt_1323_1223; [ assumption | idtac ].
  eapply sl_lt_bef_j with (hsl₁ := []); try eassumption.
   left; reflexivity.

   split.
    apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.

    rewrite Hend₁; apply Qlt_le_weak; destruct Hjk; assumption.

  eapply conj in Hjk; [ idtac | eexact Hhj ].
  eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
  do 2 rewrite fold_slope_expr.
  apply slope_lt_1323_1223; [ assumption | idtac ].
  eapply sl_lt_bef_j with (hsl₁ := []); try eassumption.
   right; assumption.

   split.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
    eapply Qlt_le_trans; [ eassumption | idtac ].
    replace h with (fst (h, αh)) by reflexivity.
    eapply Sorted_in; [ eassumption | idtac ].
    right; assumption.

    rewrite Hend₁; apply Qlt_le_weak; destruct Hjk; assumption.
Qed.

Lemma lt_bef_j : ∀ n pts j αj segjk k αk segkx hsl₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts =
      hsl₁ ++
      [{| vert := (j, αj); edge := segjk |};
       {| vert := (k, αk); edge := segkx |} … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts j αj segjk k αk segkx hsl₁ hsl.
intros Hsort Hnp h αh Hαh (Hhj, Hjk).
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

  eapply Sorted_hd in Hsort; [ idtac | eassumption ].
  eapply Qlt_trans in Hhj; [ idtac | eassumption ].
  apply Qlt_irrefl in Hhj; contradiction.

 revert n pts hs₁ Hsort Hnp Hαh.
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
   eapply conj in Hjk; [ idtac | eexact Hhj ].
   eapply lt_bef_j_in_ch with (hsl₁ := [hs₂ … hsl₁]); eassumption.

   eapply lt_bef_j_aft_1st_ch with (hsl₁ := [hs₂ … hsl₁]); try eassumption.
   split; assumption.
Qed.

Lemma get_ns : ∀ hsl₁ hsj hsk hsl nsl₁ ns nsl g b,
  list_map_pairs newton_segment_of_pair (hsl₁ ++ [hsj; hsk … hsl]) =
     nsl₁ ++ [ns … nsl]
  → List.length hsl₁ = List.length nsl₁
    → g = (snd (vert hsj) - snd (vert hsk)) / (fst (vert hsk) - fst (vert hsj))
      → b = snd (vert hsj) + fst (vert hsj) * g
        → ns = mkns g b (vert hsj) (vert hsk) (edge hsj).
Proof.
intros hsl₁ hsj hsk hsl nsl₁ ns nsl g b.
intros Hhsl Hlen Hg Hb.
subst g b.
revert nsl₁ Hhsl Hlen.
induction hsl₁ as [| hs]; intros.
 destruct nsl₁; [ idtac | discriminate Hlen ].
 simpl in Hhsl.
 injection Hhsl; clear Hhsl; intros Hhsl H; subst ns.
 reflexivity.

 destruct nsl₁ as [| ns₃]; [ discriminate Hlen | idtac ].
 simpl in Hlen; apply eq_add_S in Hlen.
 destruct hsl₁ as [| hs₃].
  destruct nsl₁; [ idtac | discriminate Hlen ].
  simpl in Hhsl.
  injection Hhsl; clear Hhsl; intros Hhsl; intros; subst ns ns₃.
  reflexivity.

  simpl in Hhsl.
  injection Hhsl; clear Hhsl; intros Hhsl; intros; subst ns₃.
  eapply IHhsl₁; eassumption.
Qed.

Lemma lt_not_in_some_ns : ∀ n pts hsl₁ hsl nsl₁ ns nsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ hsl
    → list_map_pairs newton_segment_of_pair (hsl₁ ++ hsl) = nsl₁ ++ [ns … nsl]
      → List.length hsl₁ = List.length nsl₁
        → ∀ h αh, (h, αh) ∈ pts
          → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
            → β ns < αh + h * γ ns.
Proof.
intros n pts hsl₁ hsl nsl₁ ns nsl.
intros Hsort Hnp Hnsl Hlen h αh Hh Hnh.
destruct hsl as [| ((j, αj), segjk)].
 apply list_map_pairs_length in Hnsl.
 rewrite List.app_length in Hnsl.
 simpl in Hnsl.
 rewrite List.app_nil_r in Hnsl.
 rewrite Hlen in Hnsl.
 destruct (length nsl₁) as [| len]; [ discriminate Hnsl | simpl in Hnsl ].
 exfalso; symmetry in Hnsl; revert Hnsl.
 rewrite plus_comm; apply succ_plus_discr.

 destruct hsl as [| ((k, αk), segkx)].
  apply list_map_pairs_length in Hnsl.
  rewrite List.app_length in Hnsl.
  simpl in Hnsl.
  rewrite List.app_length in Hnsl; simpl in Hnsl.
  rewrite Hlen in Hnsl.
  exfalso; symmetry in Hnsl; revert Hnsl.
  rewrite plus_comm, <- plus_n_Sm; simpl.
  rewrite plus_comm; apply succ_plus_discr.

  eapply get_ns in Hnsl; [ idtac | assumption | reflexivity | reflexivity ].
  subst ns; simpl in Hnh |- *.
  destruct (Qlt_le_dec k h) as [Hlt| Hge].
   eapply lt_aft_k with (hsl₁ := hsl₁); simpl; eassumption.

   destruct (Qeq_dec h k) as [Heq| Hne].
    remember (hsl₁ ++ [{| vert := (j, αj); edge := segjk |}]) as x.
    eapply qeq_eq with (hsl₁ := x) in Heq; subst x; try eassumption.
     exfalso; revert Heq.
     eapply not_k with (hsl₁ := hsl₁); eassumption.

     rewrite <- List.app_assoc; simpl; eassumption.

    destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
     apply Qle_neq_lt in Hge; [ idtac | assumption ].
     eapply conj in Hge; [ idtac | eassumption ].
     eapply lt_bet_j_and_k with (hsl₁ := hsl₁); eassumption.

     destruct (Qeq_dec h j) as [Heq| Hne₂].
      eapply qeq_eq with (hsl₁ := hsl₁) in Heq; try eassumption.
      exfalso; revert Heq.
      eapply not_j with (hsl₁ := hsl₁); simpl; eassumption.

      apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
      eapply lt_bef_j with (hsl₁ := hsl₁); simpl; try eassumption.
      split; [ assumption | idtac ].
      apply next_points_sorted in Hnp; [ idtac | assumption ].
      apply Sorted_app in Hnp; destruct Hnp as (_, Hnp).
      apply Sorted_inv_2 in Hnp; destruct Hnp; assumption.
Qed.

Lemma lt_not_in_ns : ∀ n pts hsl₁ hsl nsl₁ nsl ns,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ hsl
    → list_map_pairs newton_segment_of_pair (hsl₁ ++ hsl) = nsl₁ ++ nsl
      → List.length hsl₁ = List.length nsl₁
        → ns ∈ nsl
          → ∀ h αh, (h, αh) ∈ pts
            → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
              → β ns < αh + h * γ ns.
Proof.
intros n pts hsl₁ hsl nsl₁ nsl ns Hsort Hnp Hnsl Hlen Hns.
intros h αh Hh Hnh.
revert n pts hsl₁ hsl nsl₁ ns Hsort Hnp Hnsl Hlen Hns Hh Hnh.
induction nsl as [| ns₃]; [ contradiction | intros ].
destruct Hns as [Hns| Hns].
 subst ns.
 eapply lt_not_in_some_ns with (hsl₁ := hsl₁) (nsl₁ := nsl₁); eassumption.

 destruct hsl as [| hs₂].
  apply list_map_pairs_length in Hnsl.
  rewrite List.app_length in Hnsl.
  rewrite List.app_nil_r in Hnsl.
  rewrite Hlen in Hnsl.
  destruct (length nsl₁) as [| len]; [ discriminate Hnsl | simpl in Hnsl ].
  exfalso; symmetry in Hnsl; revert Hnsl.
  rewrite plus_comm; apply succ_plus_discr.

  rewrite list_cons_app in Hnp, Hnsl.
  rewrite List.app_assoc in Hnp, Hnsl.
  symmetry in Hnsl.
  rewrite list_cons_app in Hnsl.
  rewrite List.app_assoc in Hnsl.
  symmetry in Hnsl.
  eapply IHnsl; try eassumption.
  do 2 rewrite List.app_length.
  rewrite plus_comm; simpl.
  rewrite plus_comm; simpl.
  apply eq_S; assumption.
Qed.

Lemma points_not_in_any_newton_segment₁ : ∀ pts hsl ns,
  Sorted fst_lt pts
  → hsl = lower_convex_hull_points pts
    → ns ∈ list_map_pairs newton_segment_of_pair hsl
      → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
        → β ns < αh + h * (γ ns).
Proof.
intros pts hsl ns Hsort Hhsl Hns h αh (Hαh, Hnαh).
symmetry in Hhsl.
unfold lower_convex_hull_points in Hhsl.
remember (length pts) as n; clear Heqn.
remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
rename Heqnsl into Hnsl.
symmetry in Hnsl.
eapply lt_not_in_ns with (hsl₁ := []) (nsl₁ := []); simpl; try eassumption.
reflexivity.
Qed.
