(* InSegment.v *)

(* points in newton segment *)

From Stdlib Require Import Utf8 Arith Sorting Field.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.
Require Import Slope_base.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Newton.

Theorem points_in_any_newton_segment₁ : ∀ ns pts,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
  → ∀ h αh, (h, αh) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
  → β ns == αh + Qnat h * γ ns.
Proof.
intros ns pts Hsort Hns h αh Hαh.
unfold lower_convex_hull_points in Hns.
destruct pts as [| pt₁]; [ easy | idtac ].
destruct pts as [| pt₂]; [ easy | idtac ].
injection Hns; clear Hns; intros Hns.
remember (minimise_slope pt₁ pt₂ pts) as ms eqn:Hms .
destruct Hαh as [Hαh| Hαh]. {
  now subst ns; unfold β, γ; rewrite Hαh.
}
destruct Hαh as [Hαh| Hαh]. {
  subst ns; simpl in Hαh; simpl.
  rewrite Hαh; simpl.
  unfold β, γ; simpl.
  field.
  apply Qgt_0_not_0, Q.lt_0_sub.
  remember (ini_pt ms) as pt₄.
  remember Heqpt₄ as H; clear HeqH.
  rewrite Hms in Heqpt₄.
  rewrite minimised_slope_beg_pt in Heqpt₄.
  subst pt₄ pt₁.
  remember (fst (fin_pt ms)) as x.
  remember Heqx as H; clear HeqH.
  rewrite Hαh in Heqx; simpl in Heqx.
  subst x h.
  apply Qnat_lt.
  eapply beg_lt_end_pt; [ eassumption | symmetry; eassumption ].
} {
  subst ns; simpl in Hαh.
  unfold β, γ; simpl.
  revert pt₁ pt₂ h αh ms Hms Hsort Hαh.
  induction pts as [| pt₃]; intros. {
    simpl in Hms.
    subst ms; contradiction.
  }
  simpl in Hms.
  remember (minimise_slope pt₁ pt₃ pts) as ms₁ eqn:Hms₁ .
  remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
  symmetry in Heqc.
  erewrite slope_slope_expr in Heqc; [ idtac | symmetry; eassumption ].
  destruct c. {
    subst ms.
    simpl in Hαh; simpl.
    apply -> Q.compare_eq_iff in Heqc.
    unfold slope_expr in Heqc.
    destruct Hαh as [Hαh| Hαh]. {
      subst pt₂.
      simpl in Heqc; simpl.
      do 2 rewrite Qdiv_minus_distr_r in Heqc.
      rewrite Qdiv_minus_distr_r.
      apply Qeq_opp_r in Heqc.
      do 2 rewrite Q.opp_sub_distr in Heqc.
      rewrite <- Heqc.
      progress unfold Qnat.
      field.
      apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
      apply Qgt_0_not_0, Q.lt_0_sub.
      progress unfold Q.lt.
      progress unfold Q.compare; cbn.
      apply Z.compare_lt_iff.
      do 2 rewrite q_Den_num_den.
      do 2 rewrite Z.mul_1_r.
      now apply Nat2Z.inj_lt.
    }
    replace pt₁ with (ini_pt ms₁) .
    eapply IHpts; try eassumption.
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
    rewrite Hms₁, minimised_slope_beg_pt; reflexivity.
  } {
    subst ms; contradiction.
  } {
    subst ms.
    eapply IHpts; try eassumption.
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
  }
}
Qed.
