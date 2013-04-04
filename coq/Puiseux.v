(* $Id: Puiseux.v,v 1.4 2013-04-04 15:45:09 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.

Record monomial α β := { coeff : α; power : β }.
Arguments coeff : default implicits.
Arguments power : default implicits.

Record polynomial α β := { monoms : list (monomial α β) }.
Arguments monoms : default implicits.

Definition valuation {α} (pol : polynomial α Q) :=
  match monoms pol with
  | [mx … _] => power mx
  | [] => 0
  end.
Arguments valuation : default implicits.

Definition valuation_coeff {α} k (pol : polynomial α Q) :=
  match monoms pol with
  | [mx … _] => coeff mx
  | [] => zero k
  end.
Arguments valuation_coeff : default implicits.

Definition gamma_beta_list {α} (pol : polynomial (polynomial α Q) nat) :=
  let fix loop rev_gbl xyl :=
    match xyl with
    | [(x₁, y₁) … [(x₂, y₂) … _] as xyl₁] =>
        let γ := (y₂ - y₁) / (x₁ - x₂) in
        let β := γ * x₁ + y₁ in
        loop [(γ, β) … rev_gbl] xyl₁
    | [_] | [] =>
        List.rev rev_gbl
    end
  in
  let xyl :=
    List.map (λ my, (Z.of_nat (power my) # 1, valuation (coeff my)))
      (monoms pol)
  in
  let ch := lower_convex_hull xyl in
  loop [] ch.

Record branch α β :=
  { initial_polynom : polynomial (polynomial α β) nat;
    cγl : list (α * β);
    step : nat;
    rem_steps : nat;
    pol : polynomial (polynomial α β) nat }.
Arguments initial_polynom : default implicits.
Arguments cγl : default implicits.
Arguments step : default implicits.
Arguments rem_steps : default implicits.
Arguments pol : default implicits.

Definition phony_monom {α β} : monomial (polynomial α β) nat :=
  {| coeff := {| monoms := [] |}; power := 0%nat |}.
Arguments phony_monom : default implicits.

Fixpoint puiseux_branch {α} (k : field α) (br : branch α Q)
    (sol_list : list (polynomial α Q * bool)) (γβ : Q * Q) :=
  let (γ, β) := γβ in
  let hl :=
    List.filter
      (λ m,
         let αi := valuation (coeff m) in
         let βi := αi + (Z.of_nat (power m) # 1) * γ in
         Qeq_bool β βi)
      (monoms (pol br))
  in
  let j := power (List.hd (phony_monom α Q) hl) in
  let ml :=
    List.map
      (λ m,
         {| coeff := valuation_coeff k (coeff m);
            power := (power m - j)%nat |})
      hl
  in
  let rl := roots k {| monoms := ml |} in
  ml.

Definition puiseux k nb_steps pol :=
  let gbl := gamma_beta_list pol in
  let rem_steps := (nb_steps - 1)%nat in
  List.fold_left
    (λ sol_list γβ₁,
       let br :=
         {| initial_polynom := pol; cγl := []; step := 1%nat;
            rem_steps := rem_steps; pol := pol |}
       in
       puiseux_branch k br sol_list γβ₁)
    gbl [].
