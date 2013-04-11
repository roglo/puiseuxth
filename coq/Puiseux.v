(* $Id: Puiseux.v,v 1.83 2013-04-11 16:33:18 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Definition list_minus α eq_dec (l₁ l₂ : list α) :=
  List.fold_right (List.remove eq_dec) l₁ l₂.
Arguments list_minus : default implicits.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    mul : α → α → α;
    div : α → α → α;
    eq_k_dec : ∀ x y : α, {x = y} + {x ≠ y} }.
Arguments zero : default implicits.
Arguments add : default implicits.
Arguments sub : default implicits.
Arguments mul : default implicits.
Arguments div : default implicits. 
Arguments eq_k_dec : default implicits. 

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

Fixpoint power_ps_list_of_pol α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] => [(pow, ps₁) … power_ps_list_of_pol α (S pow) psl₁ psn]
  | [] => [(pow, psn)]
  end.

Definition filter_non_zero_ps α k (dpl : list (nat * puiseux_series α)) :=
  List.filter (λ dp, if eq_k_dec k (snd dp) (zero k) then false else true)
    dpl.

Definition power_puiseux_series_list_gen α k pow cl cn :=
  filter_non_zero_ps α k (power_ps_list_of_pol α pow cl cn).

Definition power_puiseux_series_list α k pol :=
  power_puiseux_series_list_gen α k 0%nat (al pol) (an pol).

Definition gamma_beta {α} k pol :=
  let gdpl := power_puiseux_series_list α k pol in
  match lower_convex_hull_points α gdpl with
  | [(j, p₁), (k, p₂) … _] =>
      let αj := valuation α p₁ in
      let αk := valuation α p₂ in
      let γ := (αj - αk) / Qnat (k - j)%nat in
      let β := αj + Qnat j * γ in
      let dpl := points_in_segment α γ β gdpl in
      Some (γ, β, (j, p₁), (k, p₂), dpl)
  | [_] | [] =>
      None
  end.
Arguments gamma_beta : default implicits.

Lemma cpl_not_empty : ∀ α pow cl cn, power_ps_list_of_pol α pow cl cn ≠ [].
Proof.
intros; destruct cl; intros H; discriminate H.
Qed.

Lemma one_vp_gen : ∀ α k pow cl cn,
  cn ≠ zero k → power_puiseux_series_list_gen α k pow cl cn ≠ [].
Proof.
intros α k pow cl cn Hcn.
unfold power_puiseux_series_list_gen.
remember (power_ps_list_of_pol α pow cl cn) as cpl.
revert pow cpl Heqcpl.
induction cl as [| c cl]; intros.
 subst cpl; simpl.
 destruct (eq_k_dec k cn (zero k)); [ contradiction | simpl ].
 intros H; discriminate H.

 subst cpl; simpl.
 destruct (eq_k_dec k c (zero k)).
  eapply IHcl; reflexivity.

  simpl.
  intros H; discriminate H.
Qed.

Lemma at_least_one_valuation_point : ∀ α k pol,
  an pol ≠ zero k → power_puiseux_series_list α k pol ≠ [].
Proof.
intros; apply one_vp_gen; assumption.
Qed.

Lemma fold_power_puiseux_series_list_gen : ∀ α k pow cl cn,
  filter_non_zero_ps α k (power_ps_list_of_pol α pow cl cn) =
  power_puiseux_series_list_gen α k pow cl cn.
Proof. reflexivity. Qed.

Lemma two_vp_gen : ∀ α k pow cl cn,
  cn ≠ zero k
  → (∃ c, c ∈ cl ∧ c ≠ zero k)
    → List.length (power_puiseux_series_list_gen α k pow cl cn) ≥ 2.
Proof.
intros α k pow cl cn Hcn Hcl.
revert pow.
induction cl as [| c]; intros.
 destruct Hcl as (c, (Hc, Hz)); contradiction.

 unfold power_puiseux_series_list_gen; simpl.
 destruct (eq_k_dec k c (zero k)).
  destruct Hcl as (c₁, ([Hc₁| Hc₁], Hz)).
   subst c₁; contradiction.

   apply IHcl.
   exists c₁.
   split; assumption.

  simpl.
  apply le_n_S.
  rewrite fold_power_puiseux_series_list_gen.
  remember (length (power_puiseux_series_list_gen α k (S pow) cl cn)) as len.
  destruct len.
   remember (power_puiseux_series_list_gen α k (S pow) cl cn) as l.
   destruct l; [ idtac | discriminate Heqlen ].
   exfalso; symmetry in Heql; revert Heql.
   apply one_vp_gen; assumption.

   apply le_n_S, le_0_n.
Qed.

Lemma at_least_two_power_puiseux_series_list : ∀ α k pol,
  an pol ≠ zero k
  → (∃ c, c ∈ (al pol) ∧ c ≠ zero k)
    → List.length (power_puiseux_series_list α k pol) ≥ 2.
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

Lemma next_points_not_empty : ∀ α dp dpl sk d₁ p₁ dpl₁,
  next_points α [dp … dpl] sk d₁ p₁ dpl₁ ≠ [ ].
Proof.
intros.
revert dp dpl sk d₁ p₁.
induction dpl₁ as [| dp₂]; intros.
 simpl.
 apply rev_app_not_nil.

 simpl.
 destruct dp₂ as (d₂, p₂).
 destruct sk.
  remember (valuation α p₂ - valuation α p₁) as v₂₁.
  remember (Qnat (d₂ - d₁)) as d₂₁.
  remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 dpl₁) as xs.
  subst v₂₁ d₂₁.
  destruct xs as (dp₃, sk).
  apply IHdpl₁.

  apply IHdpl₁.
Qed.

Lemma convex_hull_not_empty : ∀ α rl d₁ p₁ dp₂ dpl₁,
  next_points α rl 0 d₁ p₁ [dp₂ … dpl₁] ≠ [].
Proof.
intros α rl d₁ p₁ dp₂ dpl₁.
revert rl d₁ p₁ dp₂.
induction dpl₁ as [| dp₃]; intros.
 simpl.
 destruct dp₂ as (d₂, p₂).
 apply rev_app_not_nil.

 remember [dp₃ … dpl₁] as dpl.
 simpl.
 destruct dp₂ as (d₂, p₂).
 remember (valuation α p₂ - valuation α p₁) as v₂₁.
 remember (Qnat (d₂ - d₁)) as d₂₁.
 remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 dpl) as dps.
 subst v₂₁ d₂₁.
 destruct dps as (dp, skip).
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
remember (power_puiseux_series_list α k pol) as pts.
remember (lower_convex_hull_points α pts) as chp.
destruct chp as [| (d₁, p₁)].
 destruct pts as [| (d₂, p₂)]; [ idtac | discriminate Heqchp ].
 symmetry in Heqpts.
 exfalso; revert Heqpts.
 apply at_least_one_valuation_point; assumption.

 destruct chp as [| (mp₂₃, (d₃, p₃))].
  destruct pts as [| (d₃, p₃)]; [ discriminate Heqchp | simpl in Heqchp ].
  injection Heqchp; intros H₁ H₂ H₃.
  subst d₃ p₃; clear Heqchp.
  destruct pts.
   remember (length (power_puiseux_series_list α k pol)) as len.
   destruct len.
    rewrite <- Heqpts in Heqlen.
    discriminate Heqlen.

    destruct len.
     pose proof (at_least_two_power_puiseux_series_list α k pol) as H.
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

Lemma min_slope_in_list : ∀ α d₁ p₁ d_m p_m sl_m sk_m sk dpl dp skip,
  minimise_slope α d₁ p₁ d_m p_m sl_m sk_m sk dpl = (dp, skip)
  → dp ∈ [(d_m, p_m) … dpl].
Proof.
intros; rename H into Hmin.
revert d₁ p₁ d_m p_m sl_m sk_m sk dp skip Hmin.
induction dpl as [| dp₂]; intros.
 simpl in Hmin.
 destruct dp; injection Hmin; clear Hmin; intros; subst d_m p_m sk_m.
 left; reflexivity.

 simpl in Hmin.
 destruct dp₂ as (d₂, p₂).
 remember (valuation α p₂ - valuation α p₁) as v₂₁.
 remember (Qnat (d₂ - d₁)) as d₂₁.
 destruct (Qle_bool (v₂₁ / d₂₁) sl_m).
  apply IHdpl in Hmin.
  right; assumption.

  apply IHdpl in Hmin.
  destruct Hmin as [Hdp| Hdp].
   subst dp; left; reflexivity.

   right; right; assumption.
Qed.

Lemma vp_pow_lt : ∀ α k pow cl cn d₁ p₁ dpl,
  power_puiseux_series_list_gen α k (S pow) cl cn = dpl
  → (d₁, p₁) ∈ dpl
    → lt pow d₁.
Proof.
intros α k pow cl cn d₁ p₁ dpl Hvp Hdp.
revert k pow cn d₁ p₁ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k cn (zero k)) as [Heq| Hne].
  subst dpl; contradiction.

  simpl in Hvp.
  subst dpl; destruct Hdp as [Hdp| ]; [ idtac | contradiction ].
  injection Hdp; clear Hdp; intros; subst d₁ p₁.
  apply lt_n_Sn.

 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k c (zero k)) as [Heq| Hne].
  rewrite fold_power_puiseux_series_list_gen in Hvp.
  eapply IHcl in Hvp; [ idtac | eassumption ].
  eapply lt_trans; [ idtac | eassumption ].
  apply lt_n_Sn.

  simpl in Hvp.
  rewrite fold_power_puiseux_series_list_gen in Hvp.
  destruct dpl as [| (d₂, p₂)]; [ contradiction | idtac ].
  injection Hvp; clear Hvp; intros Hvp H₂ Hdpl; subst d₂ p₂.
  destruct Hdp as [Hdp| Hdp].
   injection Hdp; clear Hdp; intros; subst d₁ p₁.
   apply lt_n_Sn.

   eapply IHcl in Hvp; [ idtac | eassumption ].
   eapply lt_trans; [ idtac | eassumption ].
   apply lt_n_Sn.
Qed.

Lemma vp_lt : ∀ α k pow cl cn d₁ p₁ d₂ p₂ dpl,
  power_puiseux_series_list_gen α k pow cl cn = [(d₁, p₁) … dpl]
  → (d₂, p₂) ∈ dpl
    → lt d₁ d₂.
Proof.
intros α k pow cl cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
revert k pow cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k cn (zero k)) as [| Hne]; [ discriminate Hvp | idtac ].
 injection Hvp; intros; subst; contradiction.

 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k c (zero k)) as [Heq| Hne].
  eapply IHcl; eassumption.

  simpl in Hvp.
  injection Hvp; clear Hvp; intros; subst d₁ p₁.
  rewrite fold_power_puiseux_series_list_gen in H.
  eapply vp_pow_lt; eassumption.
Qed.

Lemma power_puiseux_series_list_lt : ∀ α k pol d₁ p₁ d₂ p₂ dpl,
  power_puiseux_series_list α k pol = [(d₁, p₁), (d₂, p₂) … dpl]
  → lt d₁ d₂.
Proof.
intros; rename H into Hvp.
unfold power_puiseux_series_list in Hvp.
eapply vp_lt; [ eassumption | left; reflexivity ].
Qed.

Lemma vp_2nd_lt : ∀ α k pow cl cn d₁ p₁ d₂ p₂ d₃ p₃ dpl,
  power_puiseux_series_list_gen α k pow cl cn = [(d₁, p₁), (d₂, p₂) … dpl]
  → (d₃, p₃) ∈ dpl
    → lt d₂ d₃.
Proof.
intros α k pow cl cn d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
revert k pow cn d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k cn (zero k)); discriminate Hvp.

 unfold power_puiseux_series_list_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec k c (zero k)) as [Heq| Hne].
  rewrite fold_power_puiseux_series_list_gen in Hvp.
  eapply IHcl; eassumption.

  simpl in Hvp.
  rewrite fold_power_puiseux_series_list_gen in Hvp.
  injection Hvp; clear Hvp; intros Hvp H₁ H₂; subst d₁ p₁.
  eapply vp_lt; eassumption.
Qed.

Lemma power_puiseux_series_list_2nd_lt : ∀ α k pol d₁ p₁ d₂ p₂ d₃ p₃ dpl,
  power_puiseux_series_list α k pol = [(d₁, p₁), (d₂, p₂) … dpl]
  → (d₃, p₃) ∈ dpl
    → lt d₂ d₃.
Proof.
intros α k pol d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
unfold power_puiseux_series_list in Hvp.
eapply vp_2nd_lt; eassumption.
Qed.

Lemma Qlt_minus : ∀ x y, x < y → 0 < y - x.
Proof.
intros x y H.
unfold Qlt in H |-*; simpl.
rewrite Z.mul_1_r, <- Zopp_mult_distr_l.
apply Zlt_left_lt.
assumption.
Qed.

Lemma QZ_minus : ∀ a b, a - b # 1 == (a # 1) - (b # 1).
Proof.
intros.
unfold Qminus, Qplus, Zminus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma eq_pts_dec {α} : ∀ (n m : nat * puiseux_series α), {n = m} + {n ≠ m}.
Proof.
intros (i, it) (j, jt).
Admitted.

Lemma zzz : ∀ α fld pol pts,
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → pts = power_puiseux_series_list α fld pol
      → ∃ γ β seg_pts,
        seg_pts = points_in_segment α γ β pts ∧
        (∀ i it, (i, it) ∈ seg_pts →
           valuation α it + Qnat i * γ == β) ∧
        (∀ i it, (i, it) ∈ list_minus eq_pts_dec pts seg_pts →
           valuation α it + Qnat i * γ <= β).
Proof.
intros α fld pol dpl pts an_nz ai_nz Hdpl Hpts.
apply gamma_beta_not_empty in ai_nz; [ idtac | assumption ].
remember (gamma_beta fld pol) as gb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; reflexivity ].
destruct p as (p, ldpl).
destruct p as (p, (k, kt)).
destruct p as (p, (j, jt)).
destruct p as (γ, β).
remember (points_in_segment α γ β pts) as seg_pts.
exists γ, β, seg_pts.
split.
 intros i it Hiit.
 revert Hiit; clear; intros.
 induction gdpl; [ contradiction | idtac ].
 simpl in Hiit.
 remember (Qeq_bool (valuation α (snd a) + Qnat (fst a) * γ) β) as b.
 symmetry in Heqb.
 destruct b.
  destruct Hiit as [Hiit| Hiit].
   subst a.
   simpl in Heqb.
   apply Qeq_bool_iff; assumption.

   apply IHgdpl; assumption.

  apply IHgdpl; assumption.

 intros i it Hiit.
zzz.

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
    let pol := apply_poly_dp_pol k br.pol y in
    let pol := pol_div_x_power pol β in
    let pol := cancel_pol_constant_term_if_any k pol in
    dp_float_round_zero k pol
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
