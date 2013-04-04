(* $Id: Puiseux.v,v 1.3 2013-04-04 12:05:28 deraugla Exp $ *)

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

Definition gamma_beta_list {α} (pol : polynomial (polynomial α Q) Z) :=
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
    List.map (λ my, (power my # 1, valuation (coeff my))) (monoms pol)
  in
  let ch := lower_convex_hull xyl in
  loop [] ch.

Definition puiseux k nb_steps vx vy pol :=
  let gbl := gamma_beta_list pol in
  let rem_steps := (nb_steps - 1)%nat in
  List.fold_left
    (λ sol_list γβ₁,
       let br :=
         {| initial_polynom := pol; cγl := []; step := 1%nat;
            rem_steps := rem_steps; vx := vx; vy := vy; pol := pol |}
       in
       puiseux_branch k br sol_list γβ₁)
    [] gbl.
