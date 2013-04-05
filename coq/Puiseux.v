(* $Id: Puiseux.v,v 1.9 2013-04-05 09:57:35 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Streams.
Require Import ConvexHull.

Record polynomial α := { monoms : list α }.
Arguments monoms : default implicits.

Definition degree {α} (pol : polynomial α) := pred (List.length (monoms pol)).
Arguments degree : default implicits.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    mul : α → α → α;
    div : α → α → α;
    k_eq : α → α → bool }.
Arguments zero : default implicits.
Arguments add : default implicits.
Arguments sub : default implicits.
Arguments mul : default implicits.
Arguments div : default implicits. 
Arguments k_eq : default implicits. 

Definition eval_poly {α} k pol (x : α) :=
  List.fold_right (λ accu coeff, add k accu (mul k coeff x)) (zero k)
    (monoms pol).

Record alg_cl_field α :=
  { ac_field : field α;
    ac_alg_cl : ∀ pol : polynomial α,
      degree pol ≥ 1 → ∃ x : α, eval_poly ac_field pol x = zero ac_field }.
Arguments ac_field : default implicits. 
Arguments ac_alg_cl : default implicits. 

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.
Arguments ps_1 : default implicits.
Arguments ps_n : default implicits.

Definition valuation {α} (ps : puiseux_series α) := snd (ps_1 ps).
Arguments valuation : default implicits.

Definition valuation_coeff {α} (ps : puiseux_series α) := fst (ps_1 ps).
Arguments valuation : default implicits.
Arguments valuation_coeff : default implicits.

Definition gamma_beta {α} k (pol : polynomial (puiseux_series α)) :=
  let fix points deg cl :=
    match cl with
    | [c₁ … cl₁] =>
        if k_eq k c₁ (zero k) then points (S deg) cl₁
        else
          let xy := (Z.of_nat deg # 1, valuation c₁) in
          [xy … points (S deg) cl₁]
    | [] =>
        []
    end
  in
  let xyl := points 0%nat (monoms pol) in
  match lower_convex_hull xyl with
  | [(x₁, y₁), (x₂, y₂) … _] =>
      let γ := (y₂ - y₁) / (x₁ - x₂) in
      let β := γ * x₁ + y₁ in
      Some (γ, β)
  | [_] | [] =>
      None
  end.
Arguments gamma_beta : default implicits.

(*
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

Definition puiseux_iteration k br r m γ β sol_list :=
  let pol :=
    let y :=
      {| monoms :=
           [{| coeff := {| monoms := [{| coeff := r; power := γ |}] |};
               power := 0 |},
            {| coeff := {| monoms := [{| coeff := one k; power := γ |}] |};
               power := 1 |} … [] ] |}
    in
    let pol := apply_poly_xy_pol k br.pol y in
    let pol := pol_div_x_power pol β in
    let pol := cancel_pol_constant_term_if_any k pol in
    xy_float_round_zero k pol
  in
  let finite := zero_is_root pol in
  let cγl := [(r, γ) … br.cγl] in
  if br.rem_steps = 0 || finite then
    let sol := make_solution cγl in
    Left [(sol, finite) … sol_list]
  else if br.rem_steps > 0 then Right (pol, cγl)
  else Left sol_list.

Fixpoint puiseux_branch {α} (k : alg_cl_field α) (br : branch α Q)
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
  List.fold_left
    (λ sol_list rm,
       let (r, m) := rm in
       if eq k r (zero k) then sol_list
       else
         match puiseux_iteration k br r m γ β sol_list with
         | Right (pol, cγl) => next_step k br sol_list col cγl
         | Left sol_list => sol_list
         end)
    rl sol_list.

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
*)
