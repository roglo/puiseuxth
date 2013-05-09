(* $Id: ConvexHull.v,v 1.44 2013-05-09 17:56:48 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Streams.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.

Definition valuation α ps := snd (ps_1 α ps).
Definition valuation_coeff α ps := fst (ps_1 α ps).

Record min_sl α :=
  { slope : Q;
    end_pt : (Q * α);
    seg : list (Q * α);
    rem_pts : list (Q * α) }.
Arguments slope : default implicits.
Arguments end_pt : default implicits.
Arguments seg : default implicits.
Arguments rem_pts : default implicits.

Record hull_seg α := ahs
  { pt : (Q * α);
    oth : list (Q * α) }.
Arguments ahs : default implicits.
Arguments pt : default implicits.
Arguments oth : default implicits.

Definition slope_expr α pt₁ pt₂ :=
  let v₁ := valuation α (snd pt₁) in
  let v₂ := valuation α (snd pt₂) in
  Qdiv (Qminus v₂ v₁) (Qminus (fst pt₂) (fst pt₁)).

Fixpoint minimise_slope α pt₁ pt₂ pts₂ :=
  let sl₁₂ := slope_expr α pt₁ pt₂ in
  match pts₂ with
  | [] =>
      {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := [] |}
  | [pt₃ … pts₃] =>
      let ms := minimise_slope α pt₁ pt₃ pts₃ in
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

Fixpoint next_ch_points α n pts :=
  match n with
  | O => []
  | S n =>
      match pts with
      | [] => []
      | [pt₁] => [{| pt := pt₁; oth := [] |}]
      | [pt₁; pt₂ … pts₂] =>
          let ms := minimise_slope α pt₁ pt₂ pts₂ in
          let hsl := next_ch_points α n [end_pt ms … rem_pts ms] in
          [{| pt := pt₁; oth := seg ms |} … hsl]
      end
  end.

Definition lower_convex_hull_points α pts :=
  next_ch_points α (List.length pts) pts.
