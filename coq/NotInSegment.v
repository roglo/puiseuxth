(* NotInSegment.v *)

(* points not in newton segment *)

From Stdlib Require Import Utf8 Arith Sorting.

Require Import A_QArith.
Require Import Misc.
Require Import Slope_base.
Require Import SlopeMisc.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Newton.
Require Import NotInSegMisc.

Theorem lt_aft_k : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
  → ∀ h αh, (h, αh) ∈ pts
  → (k < h)%nat
  → αj + Qnat j * ((αj - αk) / (Qnat k - Qnat j)) <
    αh + Qnat h * ((αj - αk) / (Qnat k - Qnat j)).
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
eapply sorted_qeq_eq with (k := k) (αk := αk) in Hαh. {
  rewrite Hαh in Hnαh; simpl in Hnαh.
  apply Decidable.not_or in Hnαh.
  destruct Hnαh as (_, Hnαh).
  apply Decidable.not_or in Hnαh.
  destruct Hnαh as (Hnαh, _).
  negation Hnαh.
} {
  assumption.
} {
  eapply in_ch_in_pts; eassumption.
} {
  subst h; reflexivity.
}
Qed.

Theorem lt_bet_j_and_k : ∀ pts j αj k αk seg,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
  → ∀ h αh, (h, αh) ∈ pts
  → (h, αh) ∉ [(j, αj); (k, αk) … seg]
  → (j < h < k)%nat
  → αj + Qnat j * ((αj - αk) / (Qnat k - Qnat j)) <
    αh + Qnat h * ((αj - αk) / (Qnat k - Qnat j)).
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
eapply sorted_qeq_eq with (k := j) (αk := αj) in Hαh; try eassumption. {
  rewrite Hαh in Hnαh.
  simpl in Hnαh.
  apply Decidable.not_or in Hnαh.
  destruct Hnαh as (Hnαh, _).
  negation Hnαh.
} {
  eapply in_ch_in_pts with (pt₂ := (k, αk)); eassumption.
}
Qed.

(* == *)

Theorem slope_expr_eq : ∀ pt₁ pt₂ pt₃ pts,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → pt₃ ∈ pts
  → slope_expr pt₁ pt₂ == slope_expr pt₁ pt₃
  → slope_expr pt₁ pt₂ == slope_expr pt₂ pt₃.
Proof.
intros pt₁ pt₂ pt₃ pts Hsort Hin H.
apply slope_eq; [ idtac | idtac | idtac | assumption ]. {
  intros HH.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
  unfold fst_lt in Hlt.
  destruct pt₁ as (i, αi).
  destruct pt₂ as (j, αj).
  rewrite HH in Hlt.
  apply Nat.lt_irrefl in Hlt; contradiction.
} {
  intros HH.
  clear H.
  induction pts as [| pt₄]; [ contradiction | idtac ].
  simpl in Hin.
  destruct Hin as [Hin| Hin]. {
    subst pt₄.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    unfold fst_lt in Hlt₂.
    destruct pt₁ as (i, αi).
    destruct pt₂ as (j, αj).
    rewrite HH in Hlt₂.
    apply Nat.lt_irrefl in Hlt₂; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  intros HH.
  clear H.
  induction pts as [| pt₄]; [ contradiction | idtac ].
  simpl in Hin.
  destruct Hin as [Hin| Hin]. {
    subst pt₄.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    unfold fst_lt in Hlt₂.
    destruct pt₁ as (i, αi).
    destruct pt₂ as (j, αj).
    destruct pt₃ as (k, αk).
    rewrite HH in Hlt₂.
    eapply Nat.lt_trans in Hlt₂; [ idtac | eassumption ].
    apply Nat.lt_irrefl in Hlt₂; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

(* réunion avec 'min_slope_le' ? *)
Theorem minimise_slope_expr_le : ∀ pt₁ pt₂ pt₃ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
  → fin_pt ms = pt₃
  → (fst pt₂ < fst pt₃)%nat
  → slope_expr pt₂ pt₃ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pts ms Hsort Hms Hend Hlt.
erewrite slope_slope_expr; [ idtac | eassumption ].
revert pt₁ pt₂ pt₃ ms Hsort Hms Hend Hlt.
induction pts as [| pt₄]; intros. {
  subst pt₃ ms; apply Nat.lt_irrefl in Hlt; contradiction.
}
simpl in Hms.
remember (minimise_slope pt₁ pt₄ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
destruct c. {
  subst ms; simpl in Hend |- *.
  apply -> Q.compare_eq_iff in Heqc.
  symmetry in Hend.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  erewrite slope_slope_expr in Heqms₁; [ idtac | eassumption ].
  assert (HH : slope_expr pt₁ (fin_pt ms₁) == slope_expr pt₁ pt₃). {
    now rewrite Heqms₁.
  }
  erewrite <- Heqc in HH |- *.
  eapply slope_expr_eq in HH; try eassumption; [ now rewrite HH | ].
  rewrite Hend.
  eapply end_pt_in; eassumption.
} {
  subst ms; simpl in Hend |- *.
  subst pt₃.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (H, _).
  apply Nat.lt_irrefl in Hlt; contradiction.
}
move Hms at top; subst ms₁.
apply -> Q.compare_gt_iff in Heqc.
clear IHpts.
revert pt₁ pt₂ pt₃ pt₄ ms Hsort Hend Hlt Heqms₁ Heqc.
induction pts as [| pt₅]; intros. {
  simpl in Heqms₁.
  subst ms; simpl.
  simpl in Hend, Heqc.
  subst pt₄.
  apply Q.lt_le_incl.
  apply slope_lt_1312_2313; [ idtac | assumption ].
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  split; assumption.
}
simpl in Heqms₁.
remember (minimise_slope pt₁ pt₅ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr pt₁ pt₄ ?= slope ms₂) as c₁.
symmetry in Heqc₁.
destruct c₁. {
  subst ms; simpl in Hend, Heqc |- *.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  subst ms; simpl in Hend, Heqc |- *.
  subst pt₄.
  apply Q.lt_le_incl.
  apply slope_lt_1312_2313; [ idtac | assumption ].
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  split; assumption.
} {
  subst ms; simpl in Hend |- *.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

(* réunion avec 'minimise_slope_expr_le' ? *)
Theorem min_slope_le : ∀ pt₁ pt₂ pt₃ pt₄ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
  → pt₃ ∈ pts
  → fin_pt ms = pt₄
  → (fst pt₃ < fst pt₄)%nat
  → slope_expr pt₃ pt₄ <= slope ms.
Proof.
intros pt₁ pt₂ pt₃ pt₄ pts ms Hsort Hms Hpt Hend Hlt.
erewrite slope_slope_expr; [ idtac | eassumption ].
revert pt₁ pt₂ pt₃ pt₄ ms Hsort Hms Hpt Hend Hlt.
induction pts as [| pt₅]; [ contradiction | intros ].
simpl in Hms.
remember (minimise_slope pt₁ pt₅ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
destruct c. {
  subst ms; simpl in Hend |- *.
  destruct Hpt as [Hpt| Hpt]. {
    subst pt₅.
    erewrite <- slope_slope_expr; [ idtac | eassumption ].
    eapply minimise_slope_expr_le; try eassumption.
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
  }
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  subst ms; simpl in Hend |- *; subst pt₄.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  eapply Nat.lt_trans in Hlt₂; [ idtac | eassumption ].
  exfalso; revert Hpt.
  eapply Sorted_not_in; [ idtac | idtac | eassumption | eassumption ]. {
    intros x H; apply Nat.lt_irrefl in H; contradiction.
  } {
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
  }
}
move Hms at top; subst ms₁.
destruct Hpt as [Hpt| Hpt]. {
  subst pt₅.
  erewrite <- slope_slope_expr; [ idtac | eassumption ].
  eapply minimise_slope_expr_le; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
eapply IHpts; try eassumption.
eapply Sorted_minus_2nd; [ idtac | eassumption ].
intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
Qed.

Theorem lt_bef_j : ∀ pts j αj segjk k αk,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) segjk)
  → ∀ h αh, (h, αh) ∈ pts
  → (h < j < k)%nat
  → αj + Qnat j * ((αj - αk) / (Qnat k - Qnat j)) <
    αh + Qnat h * ((αj - αk) / (Qnat k - Qnat j)).
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
destruct Hαh as [Hαh| Hαh]. {
  injection Hαh; clear Hαh; intros; subst h αh.
  apply Nat.lt_irrefl in Hhj; contradiction.
} {
  eapply Sorted_hd in Hsort; [ idtac | eassumption ].
  eapply Nat.lt_trans in Hhj; [ idtac | eassumption ].
  apply Nat.lt_irrefl in Hhj; contradiction.
}
Qed.

Theorem points_not_in_any_newton_segment₁ : ∀ pts ns,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
  → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
  → β ns < αh + Qnat h * γ ns.
Proof.
intros * Hsort Hnp h αh (Hh, Hnh).
destruct ns as ((j, αj), (k, αk), segjk).
remember cons as f in Hnh; simpl in Hnh; subst f.
destruct (lt_dec k h) as [Hlt| Hge]. {
  eapply lt_aft_k; simpl; eassumption.
}
destruct (Nat.eq_dec h k) as [Heq| Hne]. {
  exfalso; revert Heq.
  eapply h_not_k; eassumption.
}
destruct (le_lt_dec h j) as [Hge₂| Hlt]. 2: {
  apply Nat.nlt_ge in Hge.
  eapply lt_bet_j_and_k; try eassumption.
  split; [ easy | cbn ].
  now apply Nat.le_neq.
}
destruct (Nat.eq_dec h j) as [Heq| Hne₂]. {
  exfalso; revert Heq.
  eapply h_not_j; simpl; eassumption.
}
apply Nat_le_neq_lt in Hge₂; [ idtac | assumption ].
eapply lt_bef_j; simpl; try eassumption.
split; [ assumption | idtac ].
remember (mkns (j, αj) (k, αk) segjk) as ns.
apply ini_lt_fin_pt with (ns := ns) in Hsort; [ | easy ].
subst ns; assumption.
Qed.
