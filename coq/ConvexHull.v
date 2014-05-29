(* ConvexHull.v *)

Require Import Utf8 QArith.

Require Import Slope_base.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record newton_segment := mkns
  { ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) }.

Record min_sl :=
  { beg_pt : (Q * Q);
    end_pt : (Q * Q);
    seg : list (Q * Q);
    rem_pts : list (Q * Q) }.

Definition slope ms := slope_expr (beg_pt ms) (end_pt ms).

Fixpoint minimise_slope pt₁ pt₂ pts₂ :=
  match pts₂ with
  | [] =>
      {| beg_pt := pt₁; end_pt := pt₂; seg := []; rem_pts := [] |}
  | [pt₃ … pts₃] =>
      let ms := minimise_slope pt₁ pt₃ pts₃ in
      match Qcompare (slope_expr pt₁ pt₂) (slope ms) with
      | Eq =>
          {| beg_pt := pt₁; end_pt := end_pt ms; seg := [pt₂ … seg ms];
             rem_pts := rem_pts ms |}
      | Lt =>
          {| beg_pt := pt₁; end_pt := pt₂; seg := []; rem_pts := pts₂ |}
      | Gt =>
          ms
      end
  end.

Fixpoint next_ch_points n pts :=
  match n with
  | O => []
  | S n =>
      match pts with
      | [] => []
      | [pt₁] => []
      | [pt₁; pt₂ … pts₂] =>
          let ms := minimise_slope pt₁ pt₂ pts₂ in
          let hsl := next_ch_points n [end_pt ms … rem_pts ms] in
          [{| ini_pt := beg_pt ms; fin_pt := end_pt ms; oth_pts := seg ms |}
           … hsl]
      end
  end.

Definition lower_convex_hull_points pts :=
  next_ch_points (List.length pts) pts.

Theorem minimised_slope_beg_pt : ∀ pt₁ pt₂ pts,
  beg_pt (minimise_slope pt₁ pt₂ pts) = pt₁.
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
  → slope ms == slope_expr pt₁ (end_pt ms).
Proof.
intros ms pt₁ pt₂ pts Hms.
unfold slope.
rewrite <- Hms at 1.
rewrite minimised_slope_beg_pt.
reflexivity.
Qed.
