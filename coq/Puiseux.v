(* $Id: Puiseux.v,v 1.45 2013-04-09 09:17:14 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.
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
Arguments polynomial : default implicits.

Definition apply_poly {α} k pol (x : α) :=
  List.fold_right (λ accu coeff, add k (mul k accu x) coeff) (an pol)
    (al pol).
Arguments apply_poly : default implicits. 

Record alg_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol x, @apply_poly α ac_field pol x = zero ac_field }.
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

Fixpoint coeff_power_list_of_pol α pow cl (cn : puiseux_series α) :=
  match cl with
  | [c₁ … cl₁] => [(c₁, pow) … coeff_power_list_of_pol α (S pow) cl₁ cn]
  | [] => [(cn, pow)]
  end.

Definition filter_non_zero_coeffs α k (cpl : list (puiseux_series α * nat)) :=
  List.filter (λ cp, if k_eq_dec k (fst cp) (zero k) then false else true)
    cpl.

Definition valuation_points_gen α k pow cl cn :=
  let cpl := coeff_power_list_of_pol α pow cl cn in
  let scpl := filter_non_zero_coeffs α k cpl in
  List.map (λ cp, (Z.of_nat (snd cp) # 1, @valuation α (fst cp))) scpl.

Definition valuation_points α k pol :=
  valuation_points_gen α k 0%nat (al pol) (an pol).

Definition gamma_beta {α} k pol :=
  let xyl := valuation_points α k pol in
  match lower_convex_hull xyl with
  | [(x₁, y₁), (x₂, y₂) … _] =>
      let γ := (y₂ - y₁) / (x₁ - x₂) in
      let β := γ * x₁ + y₁ in
      Some (γ, β)
  | [_] | [] =>
      None
  end.
Arguments gamma_beta : default implicits.

Lemma cpl_not_empty : ∀ α pow cl cn, coeff_power_list_of_pol α pow cl cn ≠ [].
Proof.
intros; destruct cl; intros H; discriminate H.
Qed.

Lemma one_vp_gen : ∀ α k pow cl cn,
  cn ≠ zero k → valuation_points_gen α k pow cl cn ≠ [].
Proof.
intros α k pow cl cn Hcn.
unfold valuation_points_gen.
remember (coeff_power_list_of_pol α pow cl cn) as cpl.
revert pow cpl Heqcpl.
induction cl as [| c cl]; intros.
 subst cpl; simpl.
 destruct (k_eq_dec k cn (zero k)); [ contradiction | simpl ].
 intros H; discriminate H.

 subst cpl; simpl.
 destruct (k_eq_dec k c (zero k)).
  eapply IHcl; reflexivity.

  simpl.
  intros H; discriminate H.
Qed.

Lemma at_least_one_valuation_point : ∀ α k pol,
  an pol ≠ zero k → valuation_points α k pol ≠ [].
Proof.
intros; apply one_vp_gen; assumption.
Qed.

Lemma fold_valuation_points_gen : ∀ α k pow cl cn,
  List.map
   (λ cp, (Z.of_nat (snd cp) # 1, valuation (fst cp)))
   (filter_non_zero_coeffs α k (coeff_power_list_of_pol α pow cl cn)) =
  valuation_points_gen α k pow cl cn.
Proof. reflexivity. Qed.

Lemma two_vp_gen : ∀ α k pow cl cn,
  cn ≠ zero k
  → (∃ c, c ∈ cl ∧ c ≠ zero k)
    → List.length (valuation_points_gen α k pow cl cn) ≥ 2.
Proof.
intros α k pow cl cn Hcn Hcl.
revert pow.
induction cl as [| c]; intros.
 destruct Hcl as (c, (Hc, Hz)); contradiction.

 unfold valuation_points_gen; simpl.
 destruct (k_eq_dec k c (zero k)).
  destruct Hcl as (c₁, ([Hc₁| Hc₁], Hz)).
   subst c₁; contradiction.

   apply IHcl.
   exists c₁.
   split; assumption.

  simpl.
  apply le_n_S.
  rewrite fold_valuation_points_gen.
  remember (length (valuation_points_gen α k (S pow) cl cn)) as len.
  destruct len.
   remember (valuation_points_gen α k (S pow) cl cn) as l.
   destruct l; [ idtac | discriminate Heqlen ].
   exfalso; symmetry in Heql; revert Heql.
   apply one_vp_gen; assumption.

   apply le_n_S, le_0_n.
Qed.

Lemma at_least_two_valuation_points : ∀ α k pol,
  an pol ≠ zero k
  → (∃ c, c ∈ (al pol) ∧ c ≠ zero k)
    → List.length (valuation_points α k pol) ≥ 2.
Proof.
intros; apply two_vp_gen; assumption.
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

Lemma next_points_not_empty : ∀ xy xyl sk x₁ y₁ xyl₁,
  next_points [xy … xyl] sk x₁ y₁ xyl₁ ≠ [ ].
Proof.
intros.
revert xy xyl sk x₁ y₁.
induction xyl₁ as [| xy₂]; intros.
 simpl.
 apply rev_app_not_nil.

 simpl.
 destruct xy₂ as (x₂, y₂).
 destruct sk.
  remember ((y₂ - y₁) / (x₂ - x₁)) as sl₁₂.
  remember (minimise_slope x₁ y₁ x₂ y₂ sl₁₂ 0 1 xyl₁) as xs.
  destruct xs as (xy₃, sk).
  apply IHxyl₁.

  apply IHxyl₁.
Qed.

Lemma convex_hull_not_empty : ∀ rl x₁ y₁ xy₂ xyl₁,
  next_points rl 0 x₁ y₁ [xy₂ … xyl₁] ≠ [].
Proof.
intros rl x₁ y₁ xy₂ xyl₁.
revert rl x₁ y₁ xy₂.
induction xyl₁ as [| xy₃]; intros.
 simpl.
 destruct xy₂ as (x₂, y₂).
 apply rev_app_not_nil.

 remember [xy₃ … xyl₁] as xyl.
 simpl.
 destruct xy₂ as (x₂, y₂).
 remember ((y₂ - y₁) / (x₂ - x₁)) as sl₁₂.
 remember (minimise_slope x₁ y₁ x₂ y₂ sl₁₂ 0 1 xyl) as xys.
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
remember (valuation_points α k pol) as pts.
remember (lower_convex_hull pts) as chp.
destruct chp as [| (x₁, y₁)].
 destruct pts as [| (x₂, y₂)]; [ idtac | discriminate Heqchp ].
 symmetry in Heqpts.
 exfalso; revert Heqpts.
 apply at_least_one_valuation_point; assumption.

 destruct chp as [| (x₃, y₃)].
  destruct pts as [| (x₃, y₃)]; [ discriminate Heqchp | simpl in Heqchp ].
  injection Heqchp; intros H₁ H₂ H₃.
  subst x₃ y₃; clear Heqchp.
  destruct pts.
   remember (length (valuation_points α k pol)) as len.
   destruct len.
    rewrite <- Heqpts in Heqlen.
    discriminate Heqlen.

    destruct len.
     pose proof (at_least_two_valuation_points α k pol) as H.
     rewrite <- Heqlen in H.
     unfold ge in H.
     assert (2 ≤ 1) as HH.
      apply H; [ assumption | exists c; split; assumption ].

      apply le_not_lt in HH.
      exfalso; apply HH, lt_n_Sn.

     rewrite <- Heqpts in Heqlen; discriminate Heqlen.

   exfalso; symmetry in H₁; revert H₁.
   apply convex_hull_not_empty.

  intros H; discriminate H.
Qed.

Lemma LocallySorted_1st_two : ∀ A R (a b : A) l,
  LocallySorted R [a, b … l] → R a b.
Proof.
intros A R a b l H; inversion H; assumption.
Qed.

Lemma Qlt_minus : ∀ x y, x < y → x - y < 0.
Proof.
intros x y H.
apply Qnot_le_lt.
apply Qlt_not_le in H.
intros HH; apply H; clear H.
apply Qle_minus_iff.
assumption.
Qed.

Lemma pow_le_cpl : ∀ α pow cl cn cp,
  cp ∈ coeff_power_list_of_pol α pow cl cn
  → pow ≤ snd cp.
Proof.
intros α pos cl cn cp Hcp.
revert pos cp Hcp.
induction cl as [| c cl]; intros pos cp Hcp.
 simpl in Hcp.
 destruct Hcp; [ idtac | contradiction ].
 subst cp; apply le_n.

 simpl in Hcp.
 destruct Hcp as [Hcp| Hcp].
  subst cp; apply le_n.

  apply lt_le_weak.
  apply IHcl; assumption.
Qed.

Lemma cpl_sorted : ∀ α k pow cl cn,
  cn ≠ zero k
  → LocallySorted (λ xy₁ xy₂, lt (snd xy₁) (snd xy₂))
      (coeff_power_list_of_pol α pow cl cn).
Proof.
intros α k pow cl cn Hcn.
revert pow cn Hcn.
induction cl as [| c cl]; intros; [ constructor | simpl ].
remember (coeff_power_list_of_pol α (S pow) cl cn) as cpl.
destruct cpl as [| cp cpl]; [ constructor | idtac ].
constructor.
 rewrite Heqcpl; apply IHcl; assumption.

 simpl.
 apply pow_le_cpl with (cl := cl) (cn := cn).
 rewrite <- Heqcpl.
 left; reflexivity.
Qed.

Lemma LocallySorted_map_iff : ∀ α β f (g : α → β) l,
  LocallySorted (λ x y, f (g x) (g y)) l ↔ LocallySorted f (List.map g l).
Proof.
intros; split; intros H.
 induction l as [| x]; [ constructor | simpl ].
 destruct l as [| y]; [ constructor | simpl ].
 inversion H; constructor; [ apply IHl | idtac ]; assumption.

 induction l as [| x]; [ constructor | simpl ].
 destruct l as [| y]; [ constructor | simpl ].
 inversion H; constructor; [ apply IHl | idtac ]; assumption.
Qed.

Lemma min_slope_in_list : ∀ x₁ y₁ x_m y_m sl_m sk_m sk xyl xy skip,
  minimise_slope x₁ y₁ x_m y_m sl_m sk_m sk xyl = (xy, skip)
  → xy ∈ [(x_m, y_m) … xyl].
Proof.
intros; rename H into Hmin.
revert x₁ y₁ x_m y_m sl_m sk_m sk xy skip Hmin.
induction xyl as [| xy₂]; intros.
 simpl in Hmin.
 destruct xy; injection Hmin; clear Hmin; intros; subst x_m y_m sk_m.
 left; reflexivity.

 simpl in Hmin.
 destruct xy₂ as (x₂, y₂).
 destruct (Qle_bool ((y₂ - y₁) / (x₂ - x₁)) sl_m).
  apply IHxyl in Hmin.
  right; assumption.

  apply IHxyl in Hmin.
  destruct Hmin as [Hxy| Hxy].
   subst xy; left; reflexivity.

   right; right; assumption.
Qed.

Lemma xxx : ∀ rl n x₁ y₁ xyl₁ xy lch,
  next_points rl n x₁ y₁ xyl₁ = [xy … lch]
  → xy ∈ rl ∨ xy ∈ xyl₁.
Proof.
intros; rename H into Hnp.
induction rl as [| xy₂].
 right.
 induction xyl₁ as [| xy₂].
  simpl in Hnp.
bbb.

Lemma yyy : ∀ α k pol x₁ y₁ x₂ y₂ lch,
  lower_convex_hull (valuation_points α k pol) = [(x₁, y₁), (x₂, y₂) … lch]
  → x₁ < x₂.
Proof.
intros; rename H into Hlch.
unfold lower_convex_hull in Hlch.
remember (valuation_points α k pol) as xyl.
destruct xyl as [| (x₃, y₃)]; [ discriminate Hlch | idtac ].
injection Hlch; clear Hlch; intros; subst x₃ y₃; rename H into Hlch.
rename x₂ into x₃.
rename y₂ into y₃.
destruct xyl as [| (x₂, y₂)]; [ discriminate Hlch | idtac ].
simpl in Hlch.
remember ((y₂ - y₁) / (x₂ - x₁)) as yx.
remember (minimise_slope (x₁, y₁) (x₂, y₂) yx 0 1 xyl) as m.
subst yx.
destruct m as (xy, skip).
symmetry in Heqxyl.
symmetry in Heqm.
apply min_slope_in_list in Heqm.
simpl in Heqm.
destruct Heqm as [Hxy| Hxy].
 subst xy.
 apply xxx in Hlch.
bbb.

Lemma zzz : ∀ α k (pol : polynomial (puiseux_series α)) lch,
  an pol ≠ zero k
  → (∃ c, c ∈ al pol ∧ c ≠ zero k)
    → lch = lower_convex_hull (valuation_points α k pol)
      → ∃ γ x₁ y₁ x₂ y₂, (x₁, y₁) ∈ lch ∧ (x₂, y₂) ∈ lch ∧
         γ * x₁ + y₁ == γ * x₂ + y₂ ∧
         ∀ x y, (x, y) ∈ lch → γ * x₁ + y₁ <= γ * x + y.
Proof.
intros α k pol lch an_nz ai_nz Hlch.
apply gamma_beta_not_empty in ai_nz; [ idtac | assumption ].
remember (gamma_beta k pol) as gb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; reflexivity ].
destruct p as (γ, β).
exists γ.
unfold gamma_beta in Heqgb.
rewrite <- Hlch in Heqgb.
destruct lch; [ discriminate Heqgb | idtac ].
destruct p as (x₁, y₁).
destruct lch; [ discriminate Heqgb | idtac ].
destruct p as (x₂, y₂).
injection Heqgb; intros H₁ H₂; clear Heqgb.
exists x₁, y₁, x₂, y₂.
split; [ left; reflexivity | idtac ].
split; [ right; left; reflexivity | idtac ].
split.
 subst γ.
 field.
 apply Qlt_not_eq, Qlt_minus.
 eapply yyy; symmetry; eassumption.

 intros x y Hin.
 subst γ.
bbb.

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
*)
