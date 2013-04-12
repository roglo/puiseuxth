(* $Id: ConvexHull.v,v 1.17 2013-04-12 21:07:11 deraugla Exp $ *)

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

Fixpoint minimise_slope α d₁ p₁ d_min p_min sl_min dpl :=
  match dpl with
  | [(d₂, p₂) … dpl₂] =>
      let v₁ := valuation α p₁ in
      let v₂ := valuation α p₂ in
      let sl₁₂ := (v₂ - v₁) / Qnat (d₂ - d₁) in
      if Qle_bool sl₁₂ sl_min then
        minimise_slope α d₁ p₁ d₂ p₂ sl₁₂ dpl₂
      else
        minimise_slope α d₁ p₁ d_min p_min sl_min dpl₂
  | [] =>
      (d_min, p_min)
  end.

Fixpoint next_points α rev_list d₁ p₁ dpl₁ :=
  match dpl₁ with
  | [(d₂, p₂) … dpl₂] =>
      if lt_dec d₁ d₂ then
        let dp₃ :=
          let v₁ := valuation α p₁ in
          let v₂ := valuation α p₂ in
          let sl₁₂ := (v₂ - v₁) / Qnat (d₂ - d₁) in
          minimise_slope α d₁ p₁ d₂ p₂ sl₁₂ dpl₂
        in
        next_points α [dp₃ … rev_list] (fst dp₃) (snd dp₃) dpl₂
      else
        next_points α rev_list d₁ p₁ dpl₂
  | [] =>
      List.rev rev_list
  end.

Definition lower_convex_hull_points α dpl :=
  match dpl with
  | [(d₁, p₁) … dpl₁] => [(d₁, p₁) … next_points α [] d₁ p₁ dpl₁]
  | [] => []
  end.

Definition points_in_segment α γ β dpl :=
  List.filter
    (λ dp,
       let i := fst dp in
       let αi := valuation α (snd dp) in
       Qeq_bool (αi + Qnat i * γ) β)
    dpl.
