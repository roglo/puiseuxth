(* $Id: PolyConvexHull.v,v 2.1 2013-12-20 00:11:51 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import InSegment.
Require Import Newton.
Require Import NotInSegment.
Require Import Puiseux_base.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Section theorems.

Variable α : Type.
Variable f : field α.

Theorem points_in_any_newton_segment : ∀ (pol : puis_ser_pol α) ns,
  ns ∈ newton_segments f pol
  → ∀ h αh, (h, αh) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
    → β ns == αh + h * γ ns.
Proof.
intros pol ns Hns h αh Hαh.
eapply points_in_any_newton_segment₁; try eassumption; try reflexivity.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment : ∀ (pol : puis_ser_pol α) pts ns,
  pts = points_of_ps_polynom f pol
  → ns ∈ newton_segments f pol
    → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < αh + h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h αh Hαhnαh.
eapply points_not_in_any_newton_segment₁.
 apply points_of_polyn_sorted in Hpts.
 eassumption.

 reflexivity.

 unfold newton_segments in Hns.
 rewrite <- Hpts in Hns.
 assumption.

 assumption.
Qed.

End theorems.
