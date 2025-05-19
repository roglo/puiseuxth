(* PolyConvexHull.v *)

From Stdlib Require Import Utf8 ZArith.

Require Import QGArith.
Require Import Misc.
Require Import Field2.
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
    → β L = αh + QG_of_nat h * γ L.
Proof.
intros f L HL h αh Hαh.
eapply points_in_any_newton_segment₁; try eassumption; try reflexivity.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem points_not_in_any_newton_segment : ∀ (f : puis_ser_pol α) pts L,
  pts = points_of_ps_polynom f
  → newton_segments f = Some L
    → ∀ h αh, (h, αh) ∈ pts ∧ (h, αh) ∉ [ini_pt L; fin_pt L … oth_pts L]
      → β L < αh + QG_of_nat h * (γ L).
Proof.
intros f pts L Hpts HL h αh Hαhnαh.
subst pts.
eapply points_not_in_any_newton_segment₁; try eassumption.
eapply points_of_polyn_sorted; reflexivity.
Qed.

Theorem list_nat_QG_in_dec : ∀ a b (l : list (nat * QG)),
  {(a, b) ∈ l} + {(a, b) ∉ l}.
Proof.
intros a b l.
apply List.In_dec.
intros x y.
destruct x as (x, ((xbn, xbd), Hbx)).
destruct y as (y, ((ybn, ybd), Hby)).
cbn in Hbx, Hby.
destruct (Nat.eq_dec x y) as [Han| Han]. {
  subst x.
  destruct (Z.eq_dec xbn ybn) as [Hbn| Hbn]. {
    subst xbn.
    destruct (Pos.eq_dec xbd ybd) as [Hbd| Hbd]. {
      left; subst xbd.
      progress f_equal.
      now apply qeq_QG_eq.
    } {
      right; intros H; apply Hbd; clear Hbd.
      now injection H.
    }
  }
  right; intros H.
  now injection H; clear H; intros; subst.
}
right; intros H.
injection H; clear H; intros; subst.
apply Han; reflexivity.
Qed.

Theorem points_in_convex : ∀ (f : puis_ser_pol α) pts L,
  pts = points_of_ps_polynom f
  → newton_segments f = Some L
    → ∀ h αh, (h, αh) ∈ pts
      → β L ≤ αh + QG_of_nat h * (γ L).
Proof.
intros f pts L Hpts HL h αh Hαh.
remember [ini_pt L; fin_pt L … oth_pts L] as spts.
pose proof (list_nat_QG_in_dec h αh spts) as H.
subst spts; destruct H as [H| H]. {
  eapply points_in_any_newton_segment in H; [ idtac | eassumption ].
  rewrite H; apply QG_le_refl.
}
apply QG_lt_le_incl.
eapply points_not_in_any_newton_segment; try eassumption.
split; assumption.
Qed.

End theorems.
