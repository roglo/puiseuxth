(* $Id: Puiseux.v,v 1.21 2013-04-06 03:16:23 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Streams.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    mul : α → α → α;
    div : α → α → α;
    k_eq_dec : ∀ x y : α, {x = y} + {x ≠ y} }.
Arguments zero : default implicits.
Arguments add : default implicits.
Arguments sub : default implicits.
Arguments mul : default implicits.
Arguments div : default implicits. 
Arguments k_eq_dec : default implicits. 

(* polynomial of degree ≥ 1 *)
Record polynomial α := { al : list α; an : α }.
Arguments al : default implicits.
Arguments an : default implicits.

Definition degree {α} (pol : polynomial α) := List.length (al pol).
Arguments degree : default implicits.

Definition eval_poly {α} k pol (x : α) :=
  List.fold_right (λ accu coeff, add k accu (mul k coeff x)) (an pol)
    (al pol).
Arguments eval_poly : default implicits. 

Record alg_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol x, @eval_poly α ac_field pol x = zero ac_field }.
Arguments ac_field : default implicits. 
Arguments ac_prop : default implicits. 

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.
Arguments ps_1 : default implicits.
Arguments ps_n : default implicits.

Definition valuation {α} ps := snd (@ps_1 α ps).
Arguments valuation : default implicits.

Definition valuation_coeff {α} ps := fst (@ps_1 α ps).
Arguments valuation : default implicits.
Arguments valuation_coeff : default implicits.

Fixpoint points_of_pol α k deg cl cn :=
  match cl with
  | [c₁ … cl₁] =>
      if k_eq_dec k c₁ (zero k) then points_of_pol α k (S deg) cl₁ cn
      else
        let xy := (Z.of_nat deg # 1, @valuation α c₁) in
        [xy … points_of_pol α k (S deg) cl₁ cn]
  | [] =>
      [(Z.of_nat deg # 1, @valuation α cn)]
  end.

Definition gamma_beta {α} k pol :=
  let xyl := points_of_pol α k 0%nat (al pol) (an pol) in
  match lower_convex_hull xyl with
  | [(x₁, y₁), (x₂, y₂) … _] =>
      let γ := (y₂ - y₁) / (x₁ - x₂) in
      let β := γ * x₁ + y₁ in
      Some (γ, β)
  | [_] | [] =>
      None
  end.
Arguments gamma_beta : default implicits.

Lemma at_least_one_point : ∀ α k deg cl cn, points_of_pol α k deg cl cn ≠ [].
Proof.
intros α k deg cl cn.
revert deg.
induction cl as [| c]; intros; [ intros H; discriminate H | simpl ].
destruct (k_eq_dec k c (zero k)); [ apply IHcl | intros H; discriminate H ].
Qed.

Lemma at_least_two_points : ∀ α k deg cl cn,
  (∃ c, c ∈ cl ∧ c ≠ zero k)
  → List.length (points_of_pol α k deg cl cn) ≥ 2.
Proof.
intros α k deg cl cn Hcl.
revert deg.
induction cl as [| c]; intros.
 destruct Hcl as (c, (Hc, Hz)); contradiction.

 simpl.
 destruct (k_eq_dec k c (zero k)).
  destruct Hcl as (c₁, ([Hc₁| Hc₁], Hz)).
   subst c₁; contradiction.

   apply IHcl.
   exists c₁.
   split; assumption.

  simpl.
  apply le_n_S.
  remember (length (points_of_pol α k (S deg) cl cn)) as len.
  destruct len.
   remember (points_of_pol α k (S deg) cl cn) as l.
   destruct l; [ idtac | discriminate Heqlen ].
   exfalso; symmetry in Heql; revert Heql.
   apply at_least_one_point.

   apply le_n_S, le_0_n.
Qed.

Lemma rev_app_not_nil {α} : ∀ (x : α) l₁ l₂, List.rev l₁ ++ [x … l₂] ≠ [ ].
Proof.
intros x l₁ l₂.
revert x l₂.
induction l₁ as [| y]; intros x l₂.
 intros H; discriminate H.

 simpl; rewrite <- List.app_assoc; simpl.
 apply IHl₁.
Qed.

Lemma next_points_not_empty : ∀ xy xyl sk xy₁ xyl₁,
  next_points [xy … xyl] sk xy₁ xyl₁ ≠ [ ].
Proof.
intros.
revert xy xyl sk xy₁.
induction xyl₁ as [| xy₂]; intros.
 simpl.
 destruct xy₁.
 apply rev_app_not_nil.

 simpl.
 destruct xy₁ as (x₁, y₁).
 destruct xy₂ as (x₂, y₂).
 destruct sk.
  remember ((y₂ - y₁) / (x₂ - x₁)) as sl₁₂.
  remember (minimise_slope (x₁, y₁) (x₂, y₂) sl₁₂ 0 1 xyl₁) as xs.
  destruct xs as (xy₃, sk).
  apply IHxyl₁.

  apply IHxyl₁.
Qed.

Lemma convex_hull_not_empty : ∀ rl xy xy₁ xyl₁,
  next_points rl 0 xy [xy₁ … xyl₁] ≠ [].
Proof.
intros rl xy xy₁ xyl₁.
revert rl xy xy₁.
induction xyl₁ as [| xy₃]; intros.
 simpl.
 destruct xy.
 destruct xy₁ as (x₂, y₂).
 apply rev_app_not_nil.

 remember [xy₃ … xyl₁] as xyl.
 simpl.
 destruct xy as (x₁, y₁).
 destruct xy₁ as (x₂, y₂).
 remember ((y₂ - y₁) / (x₂ - x₁)) as sl₁₂.
 remember (minimise_slope (x₁, y₁) (x₂, y₂) sl₁₂ 0 1 xyl) as xys.
 destruct xys as (xy, skip).
 apply next_points_not_empty.
Qed.

Lemma gamma_beta_not_empty : ∀ α k (pol : polynomial (puiseux_series α)),
  an pol ≠ zero k
  → (∃ c, c ∈ al pol ∧ c ≠ zero k)
    → gamma_beta k pol ≠ None.
Proof.
intros α k pol an_nz ai_nz.
unfold gamma_beta.
destruct ai_nz as (c, (Hc, c_nz)).
remember (points_of_pol α k 0 (al pol) (an pol)) as pts.
remember (lower_convex_hull pts) as chp.
destruct chp.
 destruct pts; [ idtac | discriminate Heqchp ].
 symmetry in Heqpts.
 exfalso; revert Heqpts.
 apply at_least_one_point; assumption.

 destruct p as (x₁, y₁).
 destruct chp.
  destruct pts; [ discriminate Heqchp | idtac ].
  simpl in Heqchp.
  injection Heqchp; intros H₁ H₂.
  subst p; clear Heqchp.
  destruct pts.
   remember (length (points_of_pol α k 0 (al pol) (an pol))) as len.
   destruct len.
    rewrite <- Heqpts in Heqlen.
    discriminate Heqlen.

    destruct len.
     pose proof (at_least_two_points α k 0 (al pol) (an pol)) as H.
     rewrite <- Heqlen in H.
     unfold ge in H.
     assert (2 ≤ 1) as HH.
      apply H.
      exists c; split; assumption.

      apply le_not_lt in HH.
      exfalso; apply HH, lt_n_Sn.

     rewrite <- Heqpts in Heqlen; discriminate Heqlen.

   exfalso; symmetry in H₁; revert H₁.
   apply convex_hull_not_empty.

  destruct p.
  intros H; discriminate H.
Qed.

Record branch α :=
  { initial_polynom : polynomial (puiseux_series α);
    cγl : list (α * Q);
    step : nat;
    rem_steps : nat;
    pol : polynomial (puiseux_series α) }.
Arguments initial_polynom : default implicits.
Arguments cγl : default implicits.
Arguments step : default implicits.
Arguments rem_steps : default implicits.
Arguments pol : default implicits.

(*
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
