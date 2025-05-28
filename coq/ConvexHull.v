(* ConvexHull.v *)

From Stdlib Require Import Utf8 QArith List.
Import ListNotations.

Require Import Slope_base.

Record newton_segment := mkns
  { ini_pt : (nat * Q);
    fin_pt : (nat * Q);
    oth_pts : list (nat * Q) }.

Definition slope ms := slope_expr (ini_pt ms) (fin_pt ms).

Fixpoint minimise_slope pt₁ pt₂ pts₂ :=
  match pts₂ with
  | [] =>
      {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := [] |}
  | pt₃ :: pts₃ =>
      let ms := minimise_slope pt₁ pt₃ pts₃ in
      match Qcompare (slope_expr pt₁ pt₂) (slope ms) with
      | Eq =>
          {| ini_pt := pt₁; fin_pt := fin_pt ms;
             oth_pts := pt₂ :: oth_pts ms |}
      | Lt =>
          {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := [] |}
      | Gt =>
          ms
      end
  end.

Definition lower_convex_hull_points pts :=
  match pts with
  | [] => None
  | [pt₁] => None
  | pt₁ :: pt₂ :: pts₂ =>
      let ms := minimise_slope pt₁ pt₂ pts₂ in
      Some
        {| ini_pt := ini_pt ms; fin_pt := fin_pt ms; oth_pts := oth_pts ms |}
  end.

Theorem minimised_slope_beg_pt : ∀ pt₁ pt₂ pts,
  ini_pt (minimise_slope pt₁ pt₂ pts) = pt₁.
Proof.
intros pt₁ pt₂ pts.
revert pt₁ pt₂.
induction pts as [| pt]; intros; [ reflexivity | simpl ].
remember (minimise_slope pt₁ pt pts) as ms.
remember (slope_expr pt₁ pt₂ ?= slope ms) as c.
symmetry in Heqc.
destruct c; simpl; [ reflexivity | reflexivity | idtac ].
subst ms; apply IHpts.
Qed.

Theorem slope_slope_expr : ∀ ms pt₁ pt₂ pts,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms = slope_expr pt₁ (fin_pt ms).
Proof.
intros ms pt₁ pt₂ pts Hms.
unfold slope.
rewrite <- Hms at 1.
rewrite minimised_slope_beg_pt.
reflexivity.
Qed.
