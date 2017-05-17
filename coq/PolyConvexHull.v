(* PolyConvexHull.v *)

Require Import Utf8 QArith.

Require Import Misc.
Require Import Field.
Require Import InSegment.
Require Import ConvexHull.
Require Import Newton.
Require Import NotInSegment.
Require Import Puiseux_base.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Section theorems.

Variable α : Type.
Variable r : ring α.
Variable K : field r.

Theorem points_in_any_newton_segment : ∀ f L,
  newton_segments f = Some L
  → ∀ h αh, (h, αh) ∈ [ini_pt L; fin_pt L … oth_pts L]
    → β L == αh + h * γ L.
Proof.
intros f L HL h αh Hαh.
eapply points_in_any_newton_segment₁; try eassumption; try reflexivity.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment : ∀ (f : puis_ser_pol α) pts L,
  pts = points_of_ps_polynom f
  → newton_segments f = Some L
    → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt L; fin_pt L … oth_pts L]
      → β L < αh + h * (γ L).
Proof.
intros f pts L Hpts HL h αh Hαhnαh.
subst pts.
eapply points_not_in_any_newton_segment₁; try eassumption.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem list_Q_pair_in_dec : ∀ a b (l : list (Q * Q)),
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

Theorem points_in_convex : ∀ (f : puis_ser_pol α) pts L,
  pts = points_of_ps_polynom f
  → newton_segments f = Some L
    → ∀ h αh, (h, αh) ∈ pts
      → β L <= αh + h * (γ L).
Proof.
intros f pts L Hpts HL h αh Hαh.
remember [ini_pt L; fin_pt L … oth_pts L] as spts.
pose proof (list_Q_pair_in_dec h αh spts) as H.
subst spts; destruct H as [H| H].
 eapply points_in_any_newton_segment in H; [ idtac | eassumption ].
 rewrite H; apply Qle_refl.

 apply Qlt_le_weak.
 eapply points_not_in_any_newton_segment; try eassumption.
 split; assumption.
Qed.

End theorems.
