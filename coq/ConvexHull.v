(* $Id: ConvexHull.v,v 1.13 2013-04-11 08:59:05 deraugla Exp $ *)

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

Fixpoint minimise_slope α d₁ p₁ d_min p_min sl_min sk_min skip₁ dpl :=
  match dpl with
  | [(d₂, p₂) … dpl₂] =>
      let v₁ := valuation α p₁ in
      let v₂ := valuation α p₂ in
      let sl₁₂ := (v₂ - v₁) / Qnat (d₂ - d₁) in
      if Qle_bool sl₁₂ sl_min then
        minimise_slope α d₁ p₁ d₂ p₂ sl₁₂ skip₁ (S skip₁) dpl₂
      else
        minimise_slope α d₁ p₁ d_min p_min sl_min sk_min (S skip₁) dpl₂
  | [] =>
      ((d_min, p_min), sk_min)
  end.

Fixpoint next_points α rev_list nb_pts_to_skip d₁ p₁ dpl₁ :=
  match dpl₁ with
  | [(d₂, p₂) … dpl₂] =>
      match nb_pts_to_skip with
      | 0%nat =>
          let (dp₃, skip) :=
            let v₁ := valuation α p₁ in
            let v₂ := valuation α p₂ in
            let sl₁₂ := (v₂ - v₁) / Qnat (d₂ - d₁) in
            minimise_slope α d₁ p₁ d₂ p₂ sl₁₂ 0%nat 1%nat dpl₂
          in
          next_points α [dp₃ … rev_list] skip (fst dp₃) (snd dp₃) dpl₂
      | S n =>
          next_points α rev_list n d₁ p₁ dpl₂
      end
  | [] =>
      List.rev rev_list
  end.

Definition lower_convex_hull_segments α dpl :=
  match dpl with
  | [(d₁, p₁) … dpl₁] => [(d₁, p₁) … next_points α [] 0%nat d₁ p₁ dpl₁]
  | [] => []
  end.

Definition points_in_segment α γ β dpl :=
  List.filter
    (λ dp,
       let i := fst dp in
       let αi := valuation α (snd dp) in
       Qeq_bool (αi + Qnat i * γ) β)
    dpl.
