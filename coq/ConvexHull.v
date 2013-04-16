(* $Id: ConvexHull.v,v 1.25 2013-04-16 13:47:08 deraugla Exp $ *)

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
      let (min, seg) := minimise_slope α dp₁ dp₃ dpl₃ in
      if Qle_bool (snd min) sl₁₂ then
        (min, if Qeq_bool (snd min) sl₁₂ then [dp₂ … seg] else seg)
      else
        ((dp₂, sl₁₂), [])
  | [] =>
      ((dp₂, sl₁₂), [])
  end.

Fixpoint next_ch_points α dp₁ dpl₁ :=
  match dpl₁ with
  | [dp₂ … dpl₂] =>
      if lt_dec (fst dp₁) (fst dp₂) then
        let (min, seg) := minimise_slope α dp₁ dp₂ dpl₂ in
        [(dp₁, seg) … next_ch_points α (fst min) dpl₂]
      else
        next_ch_points α dp₁ dpl₂
  | [] =>
      [(dp₁, [])]
  end.

Definition lower_convex_hull_points α dpl :=
  match dpl with
  | [dp₁ … dpl₁] => next_ch_points α dp₁ dpl₁
  | [] => []
  end.

(**)

Fixpoint min_slope α pt₁ pt₂ pts :=
  let v₁ := valuation α (snd pt₁) in
  let v₂ := valuation α (snd pt₂) in
  let sl₁₂ := (v₂ - v₁) / Qnat (fst pt₂ - fst pt₁) in
  match pts with
  | [pt₃ … pts₃] =>
      let (pt, sl) := min_slope α pt₁ pt₃ pts₃ in
      if Qle_bool sl sl₁₂ then (pt, sl) else (pt₂, sl₁₂)
  | [] =>
      (pt₂, sl₁₂)
  end.

Fixpoint assoc_ch_points α pts :=
  match pts with
  | [pt₁ … pts₁] =>
      match pts₁ with
      | [pt₂ … pts₂] =>
          [(pt₁, fst (min_slope α pt₁ pt₂ pts₂)) … assoc_ch_points α pts₁]
      | [] =>
          []
      end
  | [] => []
  end.

Fixpoint filter_ch_points α (ach : list ((nat * α) * (nat * α))) :=
  match ach with
  | [(pt₁, pt₂) … ach₁] =>
      match filter_ch_points α ach₁ with
      | [(pt₃, seg, pt₄) … fcp] =>
          if eq_nat_dec (fst pt₂) (fst pt₄) then
            [(pt₁, [pt₃ … seg], pt₂) … fcp]
          else
            [(pt₁, [], pt₂) … fcp]
      | [] =>
          [(pt₁, [], pt₂)]
      end
  | [] =>
      []
  end.

Definition lower_convex_hull_points₁ α pts :=
  let ach := assoc_ch_points α pts in
  filter_ch_points (puiseux_series α) ach.
