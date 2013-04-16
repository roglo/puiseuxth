(* $Id: ConvexHull.v,v 1.26 2013-04-16 20:36:38 deraugla Exp $ *)

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

Fixpoint minimise_slope α dp₁ dp₂ dpl₂ :=
  let v₁ := valuation α (snd dp₁) in
  let v₂ := valuation α (snd dp₂) in
  let sl₁₂ := (v₂ - v₁) / Qnat (fst dp₂ - fst dp₁) in
  match dpl₂ with
  | [dp₃ … dpl₃] =>
      let (min, sr) := minimise_slope α dp₁ dp₃ dpl₃ in
      if Qle_bool (snd min) sl₁₂ then
        (min,
         (if Qeq_bool (snd min) sl₁₂ then [dp₂ … fst sr] else fst sr, snd sr))
      else
        ((dp₂, sl₁₂), ([], dpl₂))
  | [] =>
      ((dp₂, sl₁₂), ([], []))
  end.

Fixpoint next_ch_points α n dp₁ dpl₁ :=
  match n with
  | O => []
  | S n =>
      match dpl₁ with
      | [dp₂ … dpl₂] =>
          let (min, sr) := minimise_slope α dp₁ dp₂ dpl₂ in
          [(dp₁, fst sr) … next_ch_points α n (fst min) (snd sr)]
      | [] =>
          [(dp₁, [])]
      end
  end.

Definition lower_convex_hull_points α dpl :=
  match dpl with
  | [dp₁ … dpl₁] => next_ch_points α (List.length dpl) dp₁ dpl₁
  | [] => []
  end.
