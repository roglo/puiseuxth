(* $Id: ConvexHull.v,v 1.38 2013-04-24 09:22:06 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Streams.
Require Import Misc.

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.

Definition valuation α ps := snd (ps_1 α ps).
Definition valuation_coeff α ps := fst (ps_1 α ps).

Record min_sl α :=
  { slope : Q;
    end_pt : nat * α;
    seg : list (nat * α);
    rem_pts : list (nat * α) }.
Arguments slope : default implicits.
Arguments end_pt : default implicits.
Arguments seg : default implicits.
Arguments rem_pts : default implicits.

Definition slope_expr α pt₁ pt₂ :=
  let v₁ := valuation α (snd pt₁) in
  let v₂ := valuation α (snd pt₂) in
  Qdiv (Qminus v₂ v₁) (Qnat (fst pt₂ - fst pt₁)).

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
      | [pt₁] => [(pt₁, [])]
      | [pt₁; pt₂ … pts₂] =>
          let ms := minimise_slope α pt₁ pt₂ pts₂ in
          let chl := next_ch_points α n [end_pt ms … rem_pts ms] in
          [(pt₁, seg ms) … chl]
      end
  end.

Definition lower_convex_hull_points α pts :=
  next_ch_points α (List.length pts) pts.
