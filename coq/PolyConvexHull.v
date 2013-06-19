(* $Id: PolyConvexHull.v,v 1.1 2013-06-19 13:09:57 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Puiseux_base.
Require Import Newton.
Require Import InSegment.

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

End puiseux_series.
