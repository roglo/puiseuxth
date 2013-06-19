(* $Id: PolyConvexHull.v,v 1.2 2013-06-19 13:36:09 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Puiseux_base.
Require Import Newton.
Require Import InSegment.
Require Import NotInSegment.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Section puiseux_series.

Variable α : Type.
Variable fld : field (puiseux_series α).

Theorem points_in_any_newton_segment₁ : ∀ (pol : puis_ser_pol α) ns,
  ns ∈ newton_segments pol
  → ∀ h αh, (h, αh) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
    → β ns == αh + h * γ ns.
Proof.
intros pol ns Hns h αh Hαh.
eapply points_in_any_newton_segment; try eassumption; try reflexivity.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment₁ : ∀ (pol : puis_ser_pol α) pts ns,
  pts = points_of_ps_polynom pol
  → ns ∈ newton_segments pol
    → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < αh + h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h αh Hαhnαh.
eapply points_not_in_any_newton_segment.
 apply points_of_polyn_sorted in Hpts.
 eassumption.

 reflexivity.

 unfold newton_segments in Hns.
 rewrite <- Hpts in Hns.
 assumption.

 assumption.
Qed.

End puiseux_series.
