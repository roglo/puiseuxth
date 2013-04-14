(* $Id: ConvexHull.v,v 1.20 2013-04-14 08:13:30 deraugla Exp $ *)

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

Fixpoint minimise_slope α dp₁ dp₂ dpl :=
  let v₁ := valuation α (snd dp₁) in
  let v₂ := valuation α (snd dp₂) in
  let sl₁₂ := (v₂ - v₁) / Qnat (fst dp₂ - fst dp₁) in
  match dpl with
  | [dp₃ … dpl₃] =>
      let min := minimise_slope α dp₁ dp₃ dpl₃ in
      if Qle_bool (snd min) sl₁₂ then min else (dp₂, sl₁₂)
  | [] =>
      (dp₂, sl₁₂)
  end.

Fixpoint next_points α dp₁ dpl₁ :=
  match dpl₁ with
  | [dp₂ … dpl₂] =>
      if lt_dec (fst dp₁) (fst dp₂) then
        let min := minimise_slope α dp₁ dp₂ dpl₂ in
        [dp₁ … next_points α (fst min) dpl₂]
      else
        next_points α dp₁ dpl₂
  | [] =>
      [dp₁]
  end.

Definition lower_convex_hull_points α dpl :=
  match dpl with
  | [dp₁ … dpl₁] => next_points α dp₁ dpl₁
  | [] => []
  end.

Definition points_in_segment α γ β dpl :=
  List.filter
    (λ dp,
       let i := fst dp in
       let αi := valuation α (snd dp) in
       Qeq_bool (αi + Qnat i * γ) β)
    dpl.
