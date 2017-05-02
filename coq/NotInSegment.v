(* NotInSegment.v *)

(* points not in newton segment *)

Require Import Utf8 QArith Sorting NPeano.

Require Import Misc.
Require Import Slope_base.
Require Import SlopeMisc.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Newton.
Require Import NotInSegMisc.

(* is there a way to group together the cases c = Eq and c = Gt? *)
Theorem aft_end_in_rem : ∀ pt₁ pt₂ pts ms,
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
  destruct Hsort as (Hlt₁, _).
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

Theorem consec_end_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
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

Theorem min_slope_lt : ∀ pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃,
  Sorted fst_lt [pt₁; pt₂; pt₃ … pts]
  → minimise_slope pt₁ pt₃ pts = ms₁₃
    → minimise_slope pt₂ pt₃ pts = ms₂₃
      → slope_expr pt₁ pt₂ < slope ms₁₃
        → slope ms₁₃ < slope ms₂₃.
Proof.
intros pt₁ pt₂ pt₃ pts ms₁₃ ms₂₃ Hsort Hms₁₃ Hms₂₃ Heqc.
rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
rewrite slope_slope_expr; [ idtac | eassumption ].
rewrite slope_slope_expr; [ idtac | eassumption ].
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
 rewrite slope_slope_expr in Heqc₁; [ idtac | eassumption ].
 simpl in Hms₂₃.
 remember (minimise_slope pt₂ pt₄ pts) as ms₂₄.
 rename Heqms₂₄ into Hms₂₄; symmetry in Hms₂₄.
 remember (slope_expr pt₂ pt₃ ?= slope ms₂₄) as c₂.
 symmetry in Heqc₂.
 rewrite slope_slope_expr in Heqc₂; [ idtac | eassumption ].
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

Theorem consec_slope_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → minimise_slope (end_pt ms₁) pt₃ pts₃ = ms₂
      → rem_pts ms₁ = [pt₃ … pts₃]
        → slope ms₁ < slope ms₂.
Proof.
intros pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂ Hsort Hms₁ Hms₂ Hrem₁.
rewrite slope_slope_expr; [ idtac | eassumption ].
rewrite slope_slope_expr; [ idtac | eassumption ].
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
 rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
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
  eapply min_slope_lt in Hsort; try eassumption.
   rewrite slope_slope_expr in Hsort; [ idtac | eassumption ].
   rewrite slope_slope_expr in Hsort; [ idtac | eassumption ].
   assumption.

   rewrite slope_slope_expr; [ idtac | eassumption ].
   assumption.

  subst ms₁.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem j_aft_prev_end :
  ∀ pt₁ pt₂ pts ms pt₃ pts₃ ms₁ j αj k αk seg,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → rem_pts ms = [pt₃ … pts₃]
      → minimise_slope (end_pt ms) pt₃ pts₃ = ms₁
        → lower_convex_hull_points [end_pt ms₁ … rem_pts ms₁] =
             Some (mkns (j, αj) (k, αk) seg)
          → fst (end_pt ms) < j.
Proof.
intros pt₁ pt₂ pts ms pt₃ pts₃ ms₁ j αj k αk seg.
intros Hsort Hms Hrem Hms₁ Hnp.
unfold lower_convex_hull_points in Hnp.
remember (rem_pts ms₁) as pts₂.
destruct pts₂ as [| pt₄]; [ easy | ].
remember (minimise_slope (end_pt ms₁) pt₄ pts₂) as ms₂.
symmetry in Heqms₂.
injection Hnp; clear Hnp; intros Hseg Hend Hnp.
clear seg Hseg.
symmetry in Heqpts₂.
replace j with (fst (j, αj)) by easy.
rewrite <- Hnp.
rewrite <- Heqms₂.
rewrite minimised_slope_beg_pt.
eapply consec_end_lt; try eassumption.
Qed.

Theorem aft_j_in_rem :
  ∀ pt₁ pt₂ pts ms j αj k αk seg,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → lower_convex_hull_points [end_pt ms … rem_pts ms] =
       Some (mkns (j, αj) (k, αk) seg)
      → ∀ h αh, (h, αh) ∈ [pt₁; pt₂ … pts]
        → j < h
          → (h, αh) ∈ rem_pts ms.
Proof.
intros pt₁ pt₂ pts ms j αj k αk seg.
intros Hsort Hms Hnp h αh Hαh Hjh.
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃]; [ easy | ].
remember (minimise_slope (end_pt ms) pt₃ pts₁) as ms₁.
symmetry in Heqms₁.
rewrite <- Hrem.
injection Hnp; clear Hnp; intros Hseg Hend Hnp.
clear seg Hseg.
remember Hsort as Hsort₂; clear HeqHsort₂.
eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
rewrite minimised_slope_beg_pt in Hnp.
rewrite Hnp, Hrem in Hsort.
eapply aft_end_in_rem in Hsort₂; try eassumption.
rewrite Hnp; assumption.
Qed.

Theorem lt_aft_k : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
    → ∀ h αh, (h, αh) ∈ pts
      → k < h
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros pts j αj k αk seg Hsort Hnp h αh Hαh Hkh.
eapply points_after_k; try reflexivity; try eassumption.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros; subst.
eapply beg_lt_end_pt in Hsort; [ idtac | reflexivity ].
rewrite H0, H1 in Hsort.
assumption.
Qed.

Theorem h_not_k : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → h ≠ k.
Proof.
intros pts j αj k αk seg.
intros Hpts Hnp h αh Hαh Hnαh Hhk.
eapply sorted_qeq_eq with (k := k) (αk := αk) in Hαh.
 rewrite Hαh in Hnαh; simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (_, Hnαh).
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 negation Hnαh.

 assumption.

 eapply in_ch_in_pts; eassumption.

 subst h; reflexivity.
Qed.

Theorem next_ch_points_sorted₂ : ∀ pt₁ pt₂ pt₃ pts sg,
  Sorted fst_lt [pt₁ … pts]
  → lower_convex_hull_points [pt₁ … pts] = Some (mkns pt₂ pt₃ sg)
    → fst pt₁ < fst pt₃.
Proof.
intros pt₁ pt₂ pt₃ pts sg Hsort Hnp.
simpl in Hnp.
destruct pts as [| pt₄]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp He Hb.
eapply beg_lt_end_pt in Hsort; [ idtac | reflexivity ].
rewrite He, minimised_slope_beg_pt in Hsort.
assumption.
Qed.

(*
Theorem next_ch_points_sorted : ∀ n pt₁ pt₂ pt₃ pts h₁ hsl₁ hsl sg,
  Sorted fst_lt [pt₁ … pts]
  → next_ch_points n [pt₁ … pts] = [h₁ … hsl₁] ++ [mkns pt₂ pt₃ sg … hsl]
    → fst pt₁ < fst pt₂.
Proof.
intros n pt₁ pt₂ pt₃ pts h₁ hsl₁ hsl sg.
intros Hsort Hnp.
revert n pt₁ pt₂ pt₃ pts h₁ hsl sg Hsort Hnp.
induction hsl₁ as [| h₂]; intros.
 simpl in Hnp.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₄]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope pt₁ pt₄ pts) as ms₁.
 symmetry in Heqms₁.
 apply next_ch_points_hd in Hnp.
 rewrite <- Hnp.
 eapply Qlt_le_trans.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; eassumption.

  eapply minimise_slope_le; [ idtac | eassumption ].
  eapply Sorted_inv_1; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₄]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst h₁.
 remember (minimise_slope pt₁ pt₄ pts) as ms₂.
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
*)

Theorem lt_bet_j_and_k : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → j < h < k
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros pts j αj k αk seg Hsort Hnp.
intros h αh Hαh Hnαh Hjhk.
simpl in Hnαh.
apply Decidable.not_or in Hnαh.
destruct Hnαh as (_, Hnαh).
apply Decidable.not_or in Hnαh.
destruct Hnαh as (_, Hnαh).
eapply points_between_j_and_k; try eassumption; reflexivity.
Qed.

Theorem h_not_j : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → h ≠ j.
Proof.
intros pts j αj k αk seg.
intros Hpts Hnp h αh Hαh Hnαh Hne.
eapply sorted_qeq_eq with (k := j) (αk := αj) in Hαh; try eassumption.
 rewrite Hαh in Hnαh.
 simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 negation Hnαh.

 eapply in_ch_in_pts with (pt₂ := (k, αk)); eassumption.

 subst h; reflexivity.
Qed.

Theorem slope_expr_eq : ∀ pt₁ pt₂ pt₃ pts,
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
Theorem minimise_slope_expr_le : ∀ pt₁ pt₂ pt₃ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → end_pt ms = pt₃
      → fst pt₂ < fst pt₃
        → slope_expr pt₂ pt₃ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pts ms Hsort Hms Hend Hlt.
rewrite slope_slope_expr; [ idtac | eassumption ].
revert pt₁ pt₂ pt₃ ms Hsort Hms Hend Hlt.
induction pts as [| pt₄]; intros.
 subst pt₃ ms; apply Qlt_irrefl in Hlt; contradiction.

 simpl in Hms.
 remember (minimise_slope pt₁ pt₄ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
 destruct c.
  subst ms; simpl in Hend |- *.
  apply Qeq_alt in Heqc.
  symmetry in Hend.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  rewrite slope_slope_expr in Heqms₁; [ idtac | eassumption ].
  rewrite <- Heqc in Heqms₁ |- *.
  eapply slope_expr_eq in Heqms₁; try eassumption.
   rewrite Heqms₁; apply Qle_refl.

   rewrite Hend.
   eapply end_pt_in; eassumption.

  subst ms; simpl in Hend |- *.
  subst pt₃.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (H, _).
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
Theorem min_slope_le : ∀ pt₁ pt₂ pt₃ pt₄ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → pt₃ ∈ pts
      → end_pt ms = pt₄
        → fst pt₃ < fst pt₄
          → slope_expr pt₃ pt₄ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pt₄ pts ms Hsort Hms Hpt Hend Hlt.
rewrite slope_slope_expr; [ idtac | eassumption ].
revert pt₁ pt₂ pt₃ pt₄ ms Hsort Hms Hpt Hend Hlt.
induction pts as [| pt₅]; [ contradiction | intros ].
simpl in Hms.
remember (minimise_slope pt₁ pt₅ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
destruct c.
 subst ms; simpl in Hend |- *.
 destruct Hpt as [Hpt| Hpt].
  subst pt₅.
  rewrite <- slope_slope_expr; [ idtac | eassumption ].
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
  rewrite <- slope_slope_expr; [ idtac | eassumption ].
  eapply minimise_slope_expr_le; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem sl_lt_bef_j_in_ch : ∀ pts h αh i αi j αj k αk ptk seg ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (j, αj)
        → lower_convex_hull_points [end_pt ms … rem_pts ms] =
             Some(mkns ptk (k, αk) seg)
          → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros pts h αh i αi j αj k αk ptk seg ms.
intros Hsort (Hhj, Hjk) Hms Hend Hnp.
simpl in Hnp.
remember (rem_pts ms) as pts₁ eqn:Hpts₁ .
symmetry in Hpts₁.
destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp Hend₂ H; subst seg ptk.
eapply consec_slope_lt in Hpts₁; try eassumption; [ idtac | reflexivity ].
apply slope_lt_1223_1323; [ split; assumption | idtac ].
unfold slope in Hpts₁.
rewrite Hend₂, Hend, <- Hms in Hpts₁.
do 2 rewrite minimised_slope_beg_pt in Hpts₁.
assumption.
Qed.

Theorem sl_lt_bef_j_in_ch₂ : ∀ pts h αh i αi j αj k αk ept seg ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (j, αj)
        → lower_convex_hull_points [end_pt ms … rem_pts ms] =
            Some (mkns (k, αk) ept seg)
          → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros pts h αh i αi j αj k αk ept seg ms.
intros Hsort (Hhj, Hjk) Hms Hend Hnp.
simpl in Hnp.
remember (rem_pts ms) as pts₁.
rewrite Hend in Hnp.
destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
rewrite minimised_slope_beg_pt in Hnp.
injection Hnp; clear Hnp; intros; subst j αj.
apply Qlt_irrefl in Hjk; contradiction.
Qed.

Theorem lt_expr_bef_j_in_ch : ∀ pts h αh i αi j αj k αk segjk ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → lower_convex_hull_points [end_pt ms … rem_pts ms] =
         Some (mkns (j, αj) (k, αk) segjk)
        → slope_expr (h, αh) (j, αj) < slope_expr (j, αj) (k, αk).
Proof.
intros pts h αh i αi j αj k αk segjk ms.
intros Hsort Hhjk Hms Hnp.
apply slope_lt_1323_1223; [ assumption | idtac ].
remember Hnp as H; clear HeqH.
eapply next_ch_points_hd in H.
eapply sl_lt_bef_j_in_ch; eassumption.
Qed.

Theorem lt_bef_j_in_ch : ∀ pts h αh pt₂ j αj k αk segjk ms,
  Sorted fst_lt [(h, αh); pt₂ … pts]
  → h < j < k
    → minimise_slope (h, αh) pt₂ pts = ms
      → lower_convex_hull_points [end_pt ms … rem_pts ms] =
         Some (mkns (j, αj) (k, αk) segjk)
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros pts h αh (i, αi) j αj k αk segjk ms.
intros Hsort Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
eapply lt_expr_bef_j_in_ch; try eassumption.
Qed.

Theorem sl_lt_bef_j_any : ∀ pts pt₁ pt₂ h αh j αj k αk segkx ptk ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → end_pt ms = (j, αj)
          → lower_convex_hull_points [end_pt ms … rem_pts ms] =
             Some (mkns ptk (k, αk) segkx)
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros pts (g, αg) pt₂ h αh j αj k αk segkx ptk ms.
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

  destruct pt₂ as (i, αi).
  eapply sl_lt_bef_j_in_ch; try eassumption.
  split; [ idtac | assumption ].
  apply Sorted_inv_2 in Hsort.
  destruct Hsort.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  apply minimise_slope_le in Hms; [ idtac | assumption ].
  rewrite Hend in Hms; assumption.
Qed.

Theorem sl_lt_bef_j_any₂ : ∀ pts pt₁ pt₂ h αh j αj k αk segkx ptk ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → end_pt ms = (j, αj)
          → lower_convex_hull_points [end_pt ms … rem_pts ms] =
             Some (mkns (k, αk) ptk segkx)
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros pts (g, αg) pt₂ h αh j αj k αk segkx ptk ms.
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

  remember Hnp as HHnp; clear HeqHHnp.
  apply next_ch_points_hd in Hnp.
  rewrite Hend in Hnp.
  injection Hnp; clear Hnp; intros; subst j αj.
  apply Qlt_irrefl in Hjk; contradiction.
Qed.

Theorem sl_lt_1st_ns_any_hp :
  ∀ pt₁ pt₂ pt₃ pt₄ pt₅ pts pts₁ ms₁ ms₂ sg₄,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → rem_pts ms₁ = [pt₃ … pts₁]
      → minimise_slope (end_pt ms₁) pt₃ pts₁ = ms₂
        → lower_convex_hull_points [end_pt ms₂ … rem_pts ms₂] =
           Some (mkns pt₄ pt₅ sg₄)
          → slope_expr pt₁ (end_pt ms₁) < slope_expr (end_pt ms₁) pt₄.
Proof.
intros pt₁ pt₂ pt₃ pt₄ pt₅ pts pts₁ ms₁ ms₂ sg₄.
intros Hsort Hms₁ Hrem₁ Hms₂ Hnp.
apply next_ch_points_hd in Hnp.
rewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
symmetry in Hnp.
rewrite <- minimised_slope; [ idtac | eassumption | assumption ].
eapply consec_slope_lt; eassumption.
Qed.

Theorem sl_lt_any_ns : ∀ pt₁ pt₂ pt₃ pt₄ pts sg ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → lower_convex_hull_points [end_pt ms … rem_pts ms] =
       Some (mkns pt₃ pt₄ sg)
      → slope_expr pt₁ pt₃ < slope_expr pt₃ pt₄.
Proof.
intros pt₁ pt₂ pt₃ pt₄ pts sg ms Hsort Hms Hnp.
simpl in Hnp.
remember (rem_pts ms) as pts₁.
destruct pts₁ as [| pt₇]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp; intros Hend₁ Hend; subst sg.
remember (minimise_slope (end_pt ms) pt₇ pts₁) as ms₁.
symmetry in Heqms₁.
symmetry in Heqpts₁.
eapply consec_slope_lt in Hsort; try eassumption.
eapply minimised_slope in Hms; [ idtac | reflexivity ].
rewrite <- Heqms₁, minimised_slope_beg_pt in Hend.
rewrite Hms, Hend in Hsort.
eapply minimised_slope in Heqms₁; [ idtac | reflexivity ].
rewrite Heqms₁ in Hsort.
rewrite Hend, Hend₁ in Hsort.
assumption.
Qed.

Theorem sl_lt_bef_j : ∀ pt₁ pt₂ pts h αh j αj k αk ms segjk,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → fst pt₁ < h <= fst (end_pt ms)
          → lower_convex_hull_points [end_pt ms … rem_pts ms] =
             Some (mkns (j, αj) (k, αk) segjk)
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros (g, αg) pt₂ pts h αh j αj k αk ms segjk.
intros Hsort Hh (Hhj, Hjk) Hms (H₁h, Hhe) Hnp.
remember Hnp as H; clear HeqH.
eapply next_ch_points_hd in H.
eapply sl_lt_bef_j_any; try eassumption.
split; assumption.
Qed.

Theorem lt_bef_j_aft_1st_ch : ∀ pts pt₁ pt₂ h αh j αj k αk segjk ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → lower_convex_hull_points [end_pt ms … rem_pts ms] =
           Some (mkns (j, αj) (k, αk) segjk)
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros pts pt₁ pt₂ h αh j αj k αk segjk ms.
intros Hsort Hh Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
apply slope_lt_1323_1223; [ assumption | idtac ].
remember (end_pt ms) as pt₃ in |- *.
destruct pt₃ as (l, αl).
destruct (Qlt_le_dec l h) as [Hgt| Hle].
 remember Hnp as H; clear HeqH.
 eapply next_ch_points_hd in H.
 eapply sl_lt_bef_j_any; eassumption.

 eapply sl_lt_bef_j; try eassumption.
 rewrite <- Heqpt₃.
 split; [ idtac | assumption ].
 apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
 eapply Qlt_le_trans; [ eassumption | idtac ].
 replace h with (fst (h, αh)) by reflexivity.
 eapply Sorted_in; eassumption.
Qed.

(*
Theorem lt_bef_j₁ : ∀ n pts j αj k αk segjk hs₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = [hs₁; mkns (j, αj) (k, αk) segjk … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts j αj k αk segjk hs₁ hsl.
intros Hsort Hnp h αh Hαh (Hhj, Hjk).
destruct n; [ discriminate Hnp | simpl in Hnp ].
destruct pts as [| (l, αl)]; [ discriminate Hnp | idtac ].
destruct pts as [| (m, αm)]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
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

   rewrite Hend₁.
   split; [ idtac | apply Qlt_le_weak; assumption ].
   apply Sorted_inv in Hsort.
   destruct Hsort as (_, Hrel).
   apply HdRel_inv in Hrel; assumption.

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
*)

Theorem lt_bef_j : ∀ pts j αj segjk k αk,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) segjk)
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros pts j αj segjk k αk.
intros Hsort Hnp h αh Hαh (Hhj, Hjk).
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
simpl in Hnp.
rewrite minimised_slope_beg_pt in Hnp.
injection Hnp; clear Hnp; intros; subst pt₁.
rename H into Hnp.
rename H0 into Hseg.
destruct Hαh as [Hαh| Hαh].
 injection Hαh; clear Hαh; intros; subst h αh.
 apply Qlt_irrefl in Hhj; contradiction.

 eapply Sorted_hd in Hsort; [ idtac | eassumption ].
 eapply Qlt_trans in Hhj; [ idtac | eassumption ].
 apply Qlt_irrefl in Hhj; contradiction.
Qed.

Theorem lt_not_in_some_ns : ∀ pts ns,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
        → β ns < αh + h * γ ns.
Proof.
intros pts ns.
intros Hsort Hnp h αh Hh Hnh.
destruct ns as ((j, αj), (k, αk), segjk).
remember cons as f in Hnh; simpl in Hnh; subst f.
destruct (Qlt_le_dec k h) as [Hlt| Hge].
 eapply lt_aft_k; simpl; eassumption.

 destruct (Qeq_dec h k) as [Heq| Hne].
  eapply qeq_eq_fin in Heq; try eassumption.
  exfalso; revert Heq.
  eapply h_not_k; eassumption.

  destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
   apply Qle_neq_lt in Hge; [ idtac | assumption ].
   eapply conj in Hge; [ idtac | eassumption ].
   eapply lt_bet_j_and_k; eassumption.

   destruct (Qeq_dec h j) as [Heq| Hne₂].
    eapply qeq_eq_ini in Heq; try eassumption.
    exfalso; revert Heq.
    eapply h_not_j; simpl; eassumption.

    apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
    eapply lt_bef_j; simpl; try eassumption.
    split; [ assumption | idtac ].
    remember (mkns (j, αj) (k, αk) segjk) as ns.
    apply ini_lt_fin_pt with (ns := ns) in Hsort; [ | easy ].
    subst ns; assumption.
Qed.

Theorem lt_not_in_ns : ∀ pts ns,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
     → ∀ h αh, (h, αh) ∈ pts
       → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
         → β ns < αh + h * γ ns.
Proof.
intros pts ns Hsort Hnp.
intros h αh Hh Hnh.
eapply lt_not_in_some_ns; eassumption.
Qed.

Theorem points_not_in_any_newton_segment₁ : ∀ pts ns,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
  → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
  → β ns < αh + h * (γ ns).
Proof.
intros pts ns Hsort Hns h αh (Hαh, Hnαh).
eapply lt_not_in_ns; simpl; eassumption.
Qed.
