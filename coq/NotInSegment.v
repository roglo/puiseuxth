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

Lemma consec_slope_lt : ∀ pt₁ pt₂ pt₃ pts pts₃ ms₁ ms₂,
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

Lemma j_aft_prev_end :
  ∀ n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j αj k αk seg hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → rem_pts ms = [pt₃ … pts₃]
      → minimise_slope (end_pt ms) pt₃ pts₃ = ms₁
        → next_ch_points n [end_pt ms₁ … rem_pts ms₁] =
          hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
          → fst (end_pt ms) < j.
Proof.
intros n pt₁ pt₂ pts ms pt₃ pts₃ ms₁ hsl₁ j αj k αk seg hsl.
intros Hsort Hms Hrem Hms₁ Hnp.
revert pt₁ pt₂ pt₃ pts pts₃ ms ms₁ hsl₁ Hms Hrem Hms₁ Hnp Hsort.
induction n; intros; [ destruct hsl₁; discriminate Hnp | idtac ].
simpl in Hnp.
remember (rem_pts ms₁) as pts₂.
destruct pts₂ as [| pt₄]; [ destruct hsl₁; discriminate Hnp | idtac ].
remember (minimise_slope (end_pt ms₁) pt₄ pts₂) as ms₂.
symmetry in Heqms₂.
destruct hsl₁ as [| h₁].
 injection Hnp; clear Hnp; intros; subst seg.
 rename H into Hnp.
 rename H2 into Hend.
 replace j with (fst (j, αj)) by reflexivity.
 rewrite <- Hend.
 rewrite <- Heqms₂, minimised_slope_beg_pt.
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
  ∀ n pt₁ pt₂ pts ms hsl₁ j αj k αk seg hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → next_ch_points n [end_pt ms … rem_pts ms] =
       hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
      → ∀ h αh, (h, αh) ∈ [pt₁; pt₂ … pts]
        → j < h
          → (h, αh) ∈ rem_pts ms.
Proof.
intros n pt₁ pt₂ pts ms hsl₁ j αj k αk seg hsl.
intros Hsort Hms Hnp h αh Hαh Hjh.
destruct n; [ destruct hsl₁; discriminate Hnp | simpl in Hnp ].
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃]; [ destruct hsl₁; discriminate Hnp | idtac ].
remember (minimise_slope (end_pt ms) pt₃ pts₁) as ms₁.
symmetry in Heqms₁.
rewrite <- Hrem.
destruct hsl₁ as [| hs₁].
 injection Hnp; clear Hnp; intros.
 rename H into Hnp; rename H2 into Hend.
 subst seg.
 remember Hsort as Hsort₂; clear HeqHsort₂.
 eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
 rewrite <- Heqms₁, minimised_slope_beg_pt in Hend.
 rewrite Hend, Hrem in Hsort.
 eapply aft_end_in_rem in Hsort₂; try eassumption.
 rewrite Hend; assumption.

 eapply aft_end_in_rem; try eassumption.
 eapply Qlt_trans; [ idtac | eassumption ].
 injection Hnp; clear Hnp; intros.
 eapply j_aft_prev_end; eassumption.
Qed.

Lemma lt_aft_k : ∀ n pts hsl₁ hsl j αj k αk seg,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → k < h
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts hsl₁ hsl j αj k αk seg Hsort Hnp h αh Hαh Hkh.
revert n pts Hsort Hnp Hαh.
induction hsl₁ as [| hs₁]; intros.
 eapply points_after_k; try reflexivity; try eassumption.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros; subst.
 eapply beg_lt_end_pt in Hsort; [ idtac | reflexivity ].
 rewrite H1, H2 in Hsort.
 assumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros; subst.
 remember Hsort as Hsort₂; clear HeqHsort₂.
 eapply minimise_slope_sorted in Hsort; [ idtac | reflexivity ].
 eapply IHhsl₁; try eassumption.
 right.
 eapply aft_j_in_rem; try eassumption; [ reflexivity | idtac ].
 eapply Qlt_trans; [ idtac | eassumption ].
 remember (mkns (j, αj) (k, αk) seg) as ns.
 apply ini_lt_fin_pt with (ns := ns) (n := n) in Hsort.
  rewrite Heqns in Hsort; assumption.

  rewrite H; clear.
  induction hsl₁; [ left; reflexivity | right; assumption ].
Qed.

Lemma not_k : ∀ n pts hsl₁ hsl j αj k αk seg,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → h ≠ k.
Proof.
intros n pts hsl₁ hsl j αj k αk seg.
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
 right; left; reflexivity.

 subst h; reflexivity.
Qed.

Lemma next_ch_points_sorted₂ : ∀ n pt₁ pt₂ pt₃ pts hsl₁ hsl sg,
  Sorted fst_lt [pt₁ … pts]
  → next_ch_points n [pt₁ … pts] = hsl₁ ++ [mkns pt₂ pt₃ sg … hsl]
    → fst pt₁ < fst pt₃.
Proof.
intros n pt₁ pt₂ pt₃ pts hsl₁ hsl sg Hsort Hnp.
revert n pt₁ pt₂ pt₃ pts hsl sg Hsort Hnp.
induction hsl₁ as [| h₂]; intros.
 simpl in Hnp.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₄]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros.
 eapply beg_lt_end_pt in Hsort; [ idtac | reflexivity ].
 rewrite H0, minimised_slope_beg_pt in Hsort.
 assumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₄]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros.
 remember (minimise_slope pt₁ pt₄ pts) as ms₂.
 symmetry in Heqms₂.
 eapply IHhsl₁ in Hnp.
  eapply Qlt_trans; [ idtac | eassumption ].
  remember Heqms₂ as HH; clear HeqHH.
  apply beg_lt_end_pt in Heqms₂; [ idtac | assumption ].
  rewrite <- HH in Heqms₂ at 1.
  rewrite minimised_slope_beg_pt in Heqms₂.
  assumption.

  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma next_ch_points_sorted : ∀ n pt₁ pt₂ pt₃ pts h₁ hsl₁ hsl sg,
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

Lemma lt_bet_j_and_k : ∀ n pts hsl₁ hsl j αj k αk seg,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → j < h < k
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts hsl₁ hsl j αj k αk seg Hsort Hnp.
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

Lemma not_j : ∀ n pts hsl₁ j αj k αk seg hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) (k, αk) seg … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [(j, αj); (k, αk) … seg]
        → h ≠ j.
Proof.
intros n pts hsl₁ j αj k αk seg hsl.
intros Hpts Hnp h αh Hαh Hnαh Hne.
eapply sorted_qeq_eq with (k := j) (αk := αj) in Hαh; try eassumption.
 rewrite Hαh in Hnαh.
 simpl in Hnαh.
 apply Decidable.not_or in Hnαh.
 destruct Hnαh as (Hnαh, _).
 negation Hnαh.

 eapply in_ch_in_pts with (n := n) (pt₂ := (k, αk)).
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

Lemma sl_lt_bef_j_in_ch : ∀ n pts h αh i αi j αj k αk ptk seg hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (j, αj)
        → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [mkns ptk (k, αk) seg … hsl]
          → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
(* à nettoyer *)
intros n pts h αh i αi j αj k αk ptk seg hsl₁ hsl ms.
intros Hsort (Hhj, Hjk) Hms Hend Hnp.
revert n pts h αh i αi k αk j αj ptk seg hsl ms Hsort Hhj Hjk Hms Hnp Hend.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁ eqn:Hpts₁ .
 symmetry in Hpts₁.
 destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H Hend₂ I; subst seg ptk.
 eapply consec_slope_lt in Hpts₁; try eassumption; [ idtac | reflexivity ].
 apply slope_lt_1223_1323; [ split; assumption | idtac ].
 unfold slope in Hpts₁.
 rewrite Hend₂, Hend, <- Hms in Hpts₁.
 do 2 rewrite minimised_slope_beg_pt in Hpts₁.
 assumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁ eqn:Hpts₁ .
 symmetry in Hpts₁.
 destruct pts₁ as [| (l, αl)]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope (end_pt ms) (l, αl) pts₁) as ms₁ eqn:Hms₁ .
 symmetry in Hms₁.
 rewrite Hend in Hms₁.
 remember (end_pt ms₁) as x.
 destruct x as (m, αm).
 symmetry in Heqx.
 rewrite <- Heqx in Hnp.
 assert (j < m) as Hjm.
  remember Hms₁ as H; clear HeqH.
  apply beg_lt_end_pt in Hms₁.
   rewrite Heqx, <- H in Hms₁.
   rewrite minimised_slope_beg_pt in Hms₁.
   assumption.

   rewrite <- Hend, <- Hpts₁.
   eapply minimise_slope_sorted; eassumption.

  assert (m < k) as Hmk.
   Focus 2.
   eapply IHhsl₁ in Hnp.
    5: eassumption.

    5: eassumption.

    3: assumption.

    3: assumption.

    remember Hpts₁ as H; clear HeqH.
    eapply consec_slope_lt in H.
     3: eassumption.

     3: rewrite <- Hend in Hms₁; eassumption.

     unfold slope in H.
     rewrite Hend, Heqx in H.
     rewrite <- Hms, <- Hms₁ in H.
     do 2 rewrite minimised_slope_beg_pt in H.
     apply slope_lt_1223_1323; [ split; assumption | idtac ].
     eapply Qlt_trans; [ eassumption | idtac ].
     apply slope_lt_1323_1213; [ split; assumption | assumption ].

     assumption.

    rewrite <- Hend, <- Hpts₁.
    eapply minimise_slope_sorted; eassumption.

   apply next_ch_points_sorted₂ in Hnp.
    rewrite Heqx in Hnp; assumption.

    eapply minimise_slope_sorted; [ idtac | eassumption ].
    rewrite <- Hend, <- Hpts₁.
    eapply minimise_slope_sorted; eassumption.
Qed.

Lemma sl_lt_bef_j_in_ch₂ : ∀ n pts h αh i αi j αj k αk ept seg hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → end_pt ms = (j, αj)
        → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [mkns (k, αk) ept seg … hsl]
          → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts h αh i αi j αj k αk ept seg hsl₁ hsl ms.
intros Hsort (Hhj, Hjk) Hms Hend Hnp.
revert n pts h αh i αi k αk j αj ept seg hsl ms Hsort Hhj Hjk Hms Hnp Hend.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 rewrite Hend in Hnp.
 destruct pts₁ as [| pt₁]; [ discriminate Hnp | idtac ].
 rewrite minimised_slope_beg_pt in Hnp.
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

Lemma lt_expr_bef_j_in_ch : ∀ n pts h αh i αi j αj k αk segjk hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); (i, αi) … pts]
  → h < j < k
    → minimise_slope (h, αh) (i, αi) pts = ms
      → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++ [mkns (j, αj) (k, αk) segjk … hsl]
        → slope_expr (h, αh) (j, αj) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts h αh i αi j αj k αk segjk hsl₁ hsl ms.
intros Hsort Hhjk Hms Hnp.
apply slope_lt_1323_1223; [ assumption | idtac ].
revert Hms Hnp Hsort Hhjk.
revert n ms h αh i αi j αj k αk segjk hsl pts.
induction hsl₁ as [| hs₁]; intros.
 remember Hnp as H; clear HeqH.
 eapply next_ch_points_hd in H.
 eapply sl_lt_bef_j_in_ch; try eassumption.

 remember Hnp as HHnp; clear HeqHHnp.
 remember (end_pt ms) as pt₃ in |- *.
 destruct pt₃ as (l, αl).
 apply Qlt_trans with (y := slope_expr (l, αl) (k, αk)).
  symmetry in Heqpt₃.
  eapply sl_lt_bef_j_in_ch with (j := l); try eassumption.
  split.
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   apply minimise_slope_le in Hms; [ idtac | assumption ].
   rewrite Heqpt₃ in Hms.
   eapply Qlt_le_trans; eassumption.

   replace l with (fst (l, αl)) by reflexivity.
   replace k with (fst (k, αk)) by reflexivity.
   rewrite Heqpt₃ in HHnp.
   eapply next_ch_points_sorted₂; [ idtac | eassumption ].
   rewrite <- Heqpt₃.
   eapply minimise_slope_sorted; eassumption.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  remember (rem_pts ms) as pts₁.
  destruct pts₁ as [| (m, αm)]; [ destruct hsl₁; discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
  remember (minimise_slope (end_pt ms) (m, αm) pts₁) as ms₁.
  symmetry in Heqms₁.
  rewrite <- Heqpt₃ in Heqms₁.
  eapply IHhsl₁; try eassumption.
   rewrite Heqpt₃, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.

   split; [ idtac | destruct Hhjk; assumption ].
   rewrite <- Heqpt₃ in HHnp.
   apply next_ch_points_sorted in HHnp; [ assumption | idtac ].
   rewrite Heqpt₃, Heqpts₁.
   eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lt_bef_j_in_ch : ∀ n pts h αh pt₂ j αj k αk segjk hsl₁ hsl ms,
  Sorted fst_lt [(h, αh); pt₂ … pts]
  → h < j < k
    → minimise_slope (h, αh) pt₂ pts = ms
      → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++ [mkns (j, αj) (k, αk) segjk … hsl]
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts h αh (i, αi) j αj k αk segjk hsl₁ hsl ms.
intros Hsort Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
eapply lt_expr_bef_j_in_ch; try eassumption.
Qed.

Lemma sl_lt_bef_j_any : ∀ n pts pt₁ pt₂ h αh j αj k αk segkx ptk hsl₁ hsl ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → end_pt ms = (j, αj)
          → next_ch_points n [end_pt ms … rem_pts ms] =
              hsl₁ ++ [mkns ptk (k, αk) segkx … hsl]
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts (g, αg) pt₂ h αh j αj k αk segkx ptk hsl₁ hsl ms.
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

Lemma sl_lt_bef_j_any₂ : ∀ n pts pt₁ pt₂ h αh j αj k αk segkx ptk hsl₁ hsl ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → end_pt ms = (j, αj)
          → next_ch_points n [end_pt ms … rem_pts ms] =
              hsl₁ ++ [mkns (k, αk) ptk segkx … hsl]
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n pts (g, αg) pt₂ h αh j αj k αk segkx ptk hsl₁ hsl ms.
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
   eapply sl_lt_bef_j_in_ch₂; try eassumption.
   split; [ idtac | assumption ].
   apply Sorted_inv_2 in Hsort.
   destruct Hsort.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   apply minimise_slope_le in Hms; [ idtac | assumption ].
   rewrite Hend in Hms; assumption.
Qed.

Lemma sl_lt_1st_ns_any_hp :
  ∀ n pt₁ pt₂ pt₃ pt₄ pt₅ pts pts₁ ms₁ ms₂ sg₄ hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → rem_pts ms₁ = [pt₃ … pts₁]
      → minimise_slope (end_pt ms₁) pt₃ pts₁ = ms₂
        → next_ch_points n [end_pt ms₂ … rem_pts ms₂] =
          hsl₁ ++ [mkns pt₄ pt₅ sg₄ … hsl]
          → slope_expr pt₁ (end_pt ms₁) < slope_expr (end_pt ms₁) pt₄.
Proof.
intros n pt₁ pt₂ pt₃ pt₄ pt₅ pts pts₁ ms₁ ms₂ sg₄ hsl₁ hsl.
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
 destruct pts₂ as [| pt₆]; [ destruct hsl₁; discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope (end_pt ms₂) pt₆ pts₂) as ms₃.
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

Lemma sl_lt_any_ns : ∀ n pt₁ pt₂ pt₃ pt₄ pts sg ms hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → next_ch_points n [end_pt ms … rem_pts ms] =
        hsl₁ ++ [mkns pt₃ pt₄ sg … hsl]
      → slope_expr pt₁ pt₃ < slope_expr pt₃ pt₄.
Proof.
intros n pt₁ pt₂ pt₃ pt₄ pts sg ms hsl₁ hsl Hsort Hms Hnp.
revert n pt₁ pt₂ pts ms Hnp Hsort Hms.
induction hsl₁ as [| hs₁]; intros.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 destruct pts₁ as [| pt₇]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros H Hend₁ Hend; subst sg.
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

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms) as pts₁.
 destruct pts₁ as [| pt₇]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope (end_pt ms) pt₇ pts₁) as ms₁.
 symmetry in Heqms₁.
 remember Hnp as Hsl; clear HeqHsl.
 eapply IHhsl₁ in Hsl; [ idtac | idtac | eassumption ].
  eapply Qlt_trans; [ idtac | eassumption ].
  symmetry in Heqpts₁.
  remember Hsort as Hsl₂; clear HeqHsl₂.
  eapply consec_slope_lt in Hsl₂; try eassumption.
  unfold slope in Hsl₂.
  rewrite <- Hms in Hsl₂ at 1.
  rewrite minimised_slope_beg_pt in Hsl₂.
  rewrite <- Heqms₁ in Hsl₂ at 1.
  rewrite minimised_slope_beg_pt in Hsl₂.
  apply slope_lt_1223_1323.
   split.
    eapply Qlt_le_trans.
     apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
     unfold fst_lt in Hlt; simpl in Hlt; eassumption.

     eapply Sorted_inv_1 in Hsort.
     apply minimise_slope_le in Hms; assumption.

    remember Hms as Hms₂; clear HeqHms₂.
    apply minimise_slope_sorted in Hms; [ idtac | assumption ].
    rewrite Heqpts₁ in Hms.
    apply Sorted_inv_2 in Hms; destruct Hms as (Hlt, Hms).
    eapply Qlt_le_trans; [ eassumption | idtac ].
    remember Heqms₁ as Hms₁; clear HeqHms₁.
    remember Hms₁ as Hms₃; clear HeqHms₃.
    apply minimise_slope_le in Hms₁; [ idtac | eassumption ].
    eapply Qle_trans; [ eassumption | idtac ].
    apply next_ch_points_le in Hnp; [ assumption | idtac ].
    eapply minimise_slope_sorted; [ idtac | eassumption ].
    rewrite <- Heqpts₁.
    eapply minimise_slope_sorted; eassumption.

   eapply sl_lt_1st_ns_any_hp; try eassumption.

  rewrite Heqpts₁.
  eapply minimise_slope_sorted; eassumption.
Qed.

Lemma sl_lt_bef_j : ∀ n pt₁ pt₂ pts h αh j αj k αk ms segjk hsl₁ hsl,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → fst pt₁ < h <= fst (end_pt ms)
          → next_ch_points n [end_pt ms … rem_pts ms] =
            hsl₁ ++ [mkns (j, αj) (k, αk) segjk … hsl]
            → slope_expr (h, αh) (k, αk) < slope_expr (j, αj) (k, αk).
Proof.
intros n (g, αg) pt₂ pts h αh j αj k αk ms segjk hsl₁ hsl.
intros Hsort Hh (Hhj, Hjk) Hms (H₁h, Hhe) Hnp.
destruct hsl₁ as [| hs₁]; intros.
 remember Hnp as H; clear HeqH.
 eapply next_ch_points_hd in H.
 eapply sl_lt_bef_j_any; try eassumption.
 split; assumption.

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
   eapply sl_lt_bef_j_any₂; try eassumption.
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
   eapply sl_lt_any_ns; eassumption.
Qed.

Lemma lt_bef_j_aft_1st_ch : ∀ n pts pt₁ pt₂ h αh j αj k αk segjk hsl₁ hsl ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → (h, αh) ∈ [pt₂ … pts]
    → h < j < k
      → minimise_slope pt₁ pt₂ pts = ms
        → next_ch_points n [end_pt ms … rem_pts ms] =
          hsl₁ ++ [mkns (j, αj) (k, αk) segjk … hsl]
          → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts pt₁ pt₂ h αh j αj k αk segjk hsl₁ hsl ms.
intros Hsort Hh Hhjk Hms Hnp.
eapply ad_hoc_lt_lt₂; [ assumption | idtac ].
do 2 rewrite fold_slope_expr.
apply slope_lt_1323_1223; [ assumption | idtac ].
remember (end_pt ms) as pt₃ in |- *.
destruct pt₃ as (l, αl).
destruct (Qlt_le_dec l h) as [Hgt| Hle].
 revert n pt₁ pt₂ h αh j αj k αk segjk pts hsl ms l αl Hsort Hh Hhjk Hms Hnp
  Heqpt₃ Hgt.
 induction hsl₁ as [| hs₁]; intros.
  remember Hnp as H; clear HeqH.
  eapply next_ch_points_hd in H.
  eapply sl_lt_bef_j_any; try eassumption.

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

Lemma lt_bef_j₁ : ∀ n pts j αj k αk segjk hs₁ hsl,
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

Lemma lt_bef_j : ∀ n pts j αj segjk k αk hsl₁ hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ [mkns (j, αj) (k, αk) segjk … hsl]
    → ∀ h αh, (h, αh) ∈ pts
      → h < j < k
        → αj + j * ((αj - αk) / (k - j)) < αh + h * ((αj - αk) / (k - j)).
Proof.
intros n pts j αj segjk k αk hsl₁ hsl.
intros Hsort Hnp h αh Hαh (Hhj, Hjk).
destruct hsl₁ as [| hs₁].
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
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

Lemma lt_not_in_some_ns : ∀ n pts nsl₁ ns nsl,
  Sorted fst_lt pts
  → next_ch_points n pts = nsl₁ ++ [ns … nsl]
    → ∀ h αh, (h, αh) ∈ pts
      → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
        → β ns < αh + h * γ ns.
Proof.
intros n pts nsl₁ ns nsl.
intros Hsort Hnp h αh Hh Hnh.
destruct ns as ((j, αj), (k, αk), segjk).
remember cons as f in Hnh; simpl in Hnh; subst f.
destruct (Qlt_le_dec k h) as [Hlt| Hge].
 eapply lt_aft_k; simpl; eassumption.

 destruct (Qeq_dec h k) as [Heq| Hne].
  eapply qeq_eq_fin in Heq; try eassumption.
  exfalso; revert Heq.
  eapply not_k; eassumption.

  destruct (Qlt_le_dec j h) as [Hlt| Hge₂].
   apply Qle_neq_lt in Hge; [ idtac | assumption ].
   eapply conj in Hge; [ idtac | eassumption ].
   eapply lt_bet_j_and_k; eassumption.

   destruct (Qeq_dec h j) as [Heq| Hne₂].
    eapply qeq_eq_ini in Heq; try eassumption.
    exfalso; revert Heq.
    eapply not_j; simpl; eassumption.

    apply Qle_neq_lt in Hge₂; [ idtac | assumption ].
    eapply lt_bef_j; simpl; try eassumption.
    split; [ assumption | idtac ].
    remember (mkns (j, αj) (k, αk) segjk) as ns.
    apply ini_lt_fin_pt with (ns := ns) (n := n) in Hsort.
     subst ns; assumption.

     rewrite Hnp.
     apply List.in_or_app.
     right; left; reflexivity.
Qed.

Lemma lt_not_in_ns : ∀ n pts hsl₁ hsl ns,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl₁ ++ hsl
    → ns ∈ hsl
      → ∀ h αh, (h, αh) ∈ pts
        → (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
          → β ns < αh + h * γ ns.
Proof.
intros n pts hsl₁ hsl ns Hsort Hnp Hns.
intros h αh Hh Hnh.
revert n pts hsl₁ ns Hsort Hnp Hns Hh Hnh.
induction hsl as [| ns₁]; intros; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns.
 eapply lt_not_in_some_ns; eassumption.

 eapply IHhsl with (hsl₁ := hsl₁ ++ [ns₁]); try eassumption.
 rewrite <- List.app_assoc; eassumption.
Qed.

Lemma points_not_in_any_newton_segment₁ : ∀ pts ns,
  Sorted fst_lt pts
  → ns ∈ lower_convex_hull_points pts
  → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
  → β ns < αh + h * (γ ns).
Proof.
intros pts ns Hsort Hns h αh (Hαh, Hnαh).
eapply lt_not_in_ns with (hsl₁ := []); simpl; try eassumption.
reflexivity.
Qed.
