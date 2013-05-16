(* $Id: ConvexHull.v,v 1.46 2013-05-16 03:20:31 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Slope_base.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record min_sl :=
  { slope : Q;
    end_pt : (Q * Q);
    seg : list (Q * Q);
    rem_pts : list (Q * Q) }.

Record hull_seg := ahs
  { pt : (Q * Q);
    oth : list (Q * Q) }.

Fixpoint minimise_slope pt₁ pt₂ pts₂ :=
  let sl₁₂ := slope_expr pt₁ pt₂ in
  match pts₂ with
  | [] =>
      {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := [] |}
  | [pt₃ … pts₃] =>
      let ms := minimise_slope pt₁ pt₃ pts₃ in
      match Qcompare sl₁₂ (slope ms) with
      | Eq =>
          {| slope := slope ms; end_pt := end_pt ms; seg := [pt₂ … seg ms];
             rem_pts := rem_pts ms |}
      | Lt =>
          {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := pts₂ |}
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
      | [pt₁] => [{| pt := pt₁; oth := [] |}]
      | [pt₁; pt₂ … pts₂] =>
          let ms := minimise_slope pt₁ pt₂ pts₂ in
          let hsl := next_ch_points n [end_pt ms … rem_pts ms] in
          [{| pt := pt₁; oth := seg ms |} … hsl]
      end
  end.

Definition lower_convex_hull_points pts :=
  next_ch_points (List.length pts) pts.
