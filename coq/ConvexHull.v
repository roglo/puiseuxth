(* $Id: ConvexHull.v,v 1.28 2013-04-17 10:03:00 deraugla Exp $ *)

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

Fixpoint minimise_slope α pt₁ pt₂ pts₂ :=
  let v₁ := valuation α (snd pt₁) in
  let v₂ := valuation α (snd pt₂) in
  let sl₁₂ := (v₂ - v₁) / Qnat (fst pt₂ - fst pt₁) in
  match pts₂ with
  | [pt₃ … pts₃] =>
      let ms := minimise_slope α pt₁ pt₃ pts₃ in
      if Qle_bool (snd (fst ms)) sl₁₂ then
        let pts :=
          if Qeq_bool (snd (fst ms)) sl₁₂ then [pt₂ … fst (snd ms)]
          else fst (snd ms)
        in
        (fst ms, (pts, snd (snd ms)))
      else
        ((pt₂, sl₁₂), ([], pts₂))
  | [] =>
      ((pt₂, sl₁₂), ([], []))
  end.

Fixpoint next_ch_points α n pts :=
  match n with
  | O => []
  | S n =>
      match pts with
      | [pt₁, pt₂ … pts₂] =>
          let msr := minimise_slope α pt₁ pt₂ pts₂ in
          let chl := next_ch_points α n [fst (fst msr) … snd (snd msr)] in
          [(pt₁, fst (snd msr)) … chl]
      | [pt₁] =>
          [(pt₁, [])]
      | [] =>
          []
      end
  end.

Definition lower_convex_hull_points α pts :=
  next_ch_points α (List.length pts) pts.
