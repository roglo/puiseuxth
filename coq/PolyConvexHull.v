(* PolyConvexHull.v *)

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
Variable r : ring α.

Theorem points_in_any_newton_segment : ∀ pol ns,
  ns ∈ newton_segments pol
  → ∀ h αh, (h, αh) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
    → β ns == αh + h * γ ns.
Proof.
intros pol ns Hns h αh Hαh.
eapply points_in_any_newton_segment₁; try eassumption; try reflexivity.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment : ∀ (pol : puis_ser_pol α) pts ns,
  pts = points_of_ps_polynom r pol
  → ns ∈ newton_segments pol
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

Lemma list_Q_pair_in_dec : ∀ a b (l : list (Q * Q)),
  {(a, b) ∈ l} + {(a, b) ∉ l}.
Proof.
intros a b l.
apply List.In_dec.
intros x y.
destruct x as ((xan, xad), (xbn, xbd)).
destruct y as ((yan, yad), (ybn, ybd)).
destruct (Z.eq_dec xan yan) as [Han| Han].
 subst xan.
 destruct (Pos.eq_dec xad yad) as [Had| Had].
  subst xad.
  destruct (Z.eq_dec xbn ybn) as [Hbn| Hbn].
   subst xbn.
   destruct (Pos.eq_dec xbd ybd) as [Hbd| Hbd].
    subst xbd.
    left; reflexivity.

    right; intros H.
    injection H; clear H; intros; subst.
    apply Hbd; reflexivity.

   right; intros H.
   injection H; clear H; intros; subst.
   apply Hbn; reflexivity.

  right; intros H.
  injection H; clear H; intros; subst.
  apply Had; reflexivity.

 right; intros H.
 injection H; clear H; intros; subst.
 apply Han; reflexivity.
Qed.

Theorem points_in_convex : ∀ (pol : puis_ser_pol α) pts ns,
  pts = points_of_ps_polynom r pol
  → ns ∈ newton_segments pol
    → ∀ h αh, (h, αh) ∈ pts
      → β ns <= αh + h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h αh Hαh.
remember [ini_pt ns; fin_pt ns … oth_pts ns] as spts.
pose proof (list_Q_pair_in_dec h αh spts) as H.
subst spts; destruct H as [H| H].
 eapply points_in_any_newton_segment in H; [ idtac | eassumption ].
 rewrite H; apply Qle_refl.

 apply Qlt_le_weak.
 eapply points_not_in_any_newton_segment; try eassumption.
 split; assumption.
Qed.

End theorems.
