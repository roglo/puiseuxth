(* $Id: ConvexHull.v,v 1.29 2013-04-17 11:35:55 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Streams.

Notation "[ ]" := nil.
Notation "[ x , .. , y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.

Definition valuation α ps := snd (ps_1 α ps).
Definition valuation_coeff α ps := fst (ps_1 α ps).

Definition Qnat i := Z.of_nat i # 1.

Record ms α :=
  { slope : Q;
    end_pt : nat * α;
    seg : list (nat * α);
    rem_pts : list (nat * α) }.
Arguments slope : default implicits.
Arguments end_pt : default implicits.
Arguments seg : default implicits.
Arguments rem_pts : default implicits.

Fixpoint minimise_slope α pt₁ pt₂ pts₂ :=
  let v₁ := valuation α (snd pt₁) in
  let v₂ := valuation α (snd pt₂) in
  let sl₁₂ := (v₂ - v₁) / Qnat (fst pt₂ - fst pt₁) in
  match pts₂ with
  | [pt₃ … pts₃] =>
      let ms := minimise_slope α pt₁ pt₃ pts₃ in
      if Qle_bool (slope ms) sl₁₂ then
        let seg :=
          if Qeq_bool (slope ms) sl₁₂ then [pt₂ … seg ms]
          else seg ms
        in
        {| slope := slope ms; end_pt := end_pt ms; seg := seg;
           rem_pts := rem_pts ms |}
      else
        {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := pts₂ |}
  | [] =>
      {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := [] |}
  end.

Fixpoint next_ch_points α n pts :=
  match n with
  | O => []
  | S n =>
      match pts with
      | [pt₁, pt₂ … pts₂] =>
          let ms := minimise_slope α pt₁ pt₂ pts₂ in
          let chl := next_ch_points α n [end_pt ms … rem_pts ms] in
          [(pt₁, seg ms) … chl]
      | [pt₁] =>
          [(pt₁, [])]
      | [] =>
          []
      end
  end.

Definition lower_convex_hull_points α pts :=
  next_ch_points α (List.length pts) pts.
