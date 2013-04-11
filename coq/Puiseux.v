(* $Id: Puiseux.v,v 1.78 2013-04-11 03:53:19 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

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
  let dpl := power_puiseux_series_list α k pol in
  match lower_convex_hull α dpl with
  | [(_, (d₁, p₁)), (mp, (d₂, p₂)) … _] =>
      let v₁ := valuation α p₁ in
      let v₂ := valuation α p₂ in
      let γ := (v₁ - v₂) / Qnat (d₂ - d₁)%nat in
      let β := v₁ + Qnat d₁ * γ in
      Some (γ, β, dpl)
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
  remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 [ ] dpl₁) as xs.
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
 remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 [ ] dpl) as dps.
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
remember (lower_convex_hull α pts) as chp.
destruct chp as [| (mp₁, (d₁, p₁))].
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

Lemma min_slope_in_list : ∀ α d₁ p₁ d_m p_m sl_m sk_m sk dpl dp skip mp mpr,
  minimise_slope α d₁ p₁ d_m p_m sl_m sk_m sk mp dpl = ((mpr, dp), skip)
  → dp ∈ [(d_m, p_m) … dpl].
Proof.
intros; rename H into Hmin.
revert d₁ p₁ d_m p_m sl_m sk_m sk dp skip mp mpr Hmin.
induction dpl as [| dp₂]; intros.
 simpl in Hmin.
 destruct dp; injection Hmin; clear Hmin; intros; subst d_m p_m sk_m.
 left; reflexivity.

 simpl in Hmin.
 destruct dp₂ as (d₂, p₂).
 remember (valuation α p₂ - valuation α p₁) as v₂₁.
 remember (Qnat (d₂ - d₁)) as d₂₁.
 destruct (Qeq_bool (v₂₁ / d₂₁) sl_m).
  apply IHdpl in Hmin.
  right; assumption.

  destruct (Qle_bool (v₂₁ / d₂₁) sl_m).
   apply IHdpl in Hmin.
   right; assumption.

   apply IHdpl in Hmin.
   destruct Hmin as [Hdp| Hdp].
    subst dp; left; reflexivity.

    right; right; assumption.
Qed.

Lemma next_points_in_list : ∀ α rl n d₁ p₁ dpl₁ dp mp lch,
  next_points α rl n d₁ p₁ dpl₁ = [(mp, dp) … lch]
  → (mp, dp) ∈ rl ∨ dp ∈ dpl₁.
Proof.
intros; rename H into Hnp.
revert rl n d₁ p₁ dp lch Hnp.
induction dpl₁ as [| (d₂, p₂)]; intros.
 left.
 simpl in Hnp.
 rewrite <- List.rev_involutive.
 apply List.in_rev.
 rewrite List.rev_involutive.
 rewrite Hnp; left; reflexivity.

 simpl in Hnp.
 destruct n.
  remember (valuation α p₂ - valuation α p₁) as v₂₁.
  remember (Qnat (d₂ - d₁)) as d₂₁.
  remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 [ ] dpl₁) as ms.
  subst v₂₁ d₂₁.
  destruct ms as ((mp₂₃, dp₃), skip).
  symmetry in Heqms.
  apply min_slope_in_list in Heqms.
  destruct Heqms as [Hdp| Hdp].
   subst dp₃.
   simpl in Hnp.
   apply IHdpl₁ in Hnp.
   destruct Hnp as [Hdp| Hdp].
    destruct Hdp as [Hdp| Hdp].
     injection Hdp; intros; subst mp dp.
     right; left; reflexivity.

     left; assumption.

    right; right; assumption.

   apply IHdpl₁ in Hnp.
   destruct Hnp as [Hdp₂| Hdp₂].
    destruct Hdp₂ as [Hdp₂| Hdp₂].
     injection Hdp₂; intros; subst mp dp.
     right; right; assumption.

     left; assumption.

    right; right; assumption.

  apply IHdpl₁ in Hnp.
  destruct Hnp as [Hdp| Hdp].
   left; assumption.

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

Lemma lower_convex_hull_lt : ∀ α k pol d₁ p₁ d₂ p₂ mp₀ mp₁₂ lch,
  lower_convex_hull α (power_puiseux_series_list α k pol) =
    [(mp₀, (d₁, p₁)), (mp₁₂, (d₂, p₂)) … lch]
  → (d₁ < d₂)%nat.
Proof.
intros; rename H into Hlch.
unfold lower_convex_hull in Hlch.
remember (power_puiseux_series_list α k pol) as dpl.
destruct dpl as [| (d₃, p₃)]; [ discriminate Hlch | idtac ].
injection Hlch; clear Hlch; intros; subst d₃ p₃; rename H into Hlch.
rename d₂ into d₃.
rename p₂ into p₃.
destruct dpl as [| (d₂, p₂)]; [ discriminate Hlch | idtac ].
simpl in Hlch.
remember (valuation α p₂ - valuation α p₁) as v₂₁.
remember (Qnat (d₂ - d₁)) as d₂₁.
remember (minimise_slope α d₁ p₁ d₂ p₂ (v₂₁ / d₂₁) 0 1 [ ] dpl) as m.
subst v₂₁ d₂₁.
destruct m as ((mp, dp), skip).
symmetry in Heqdpl.
symmetry in Heqm.
apply min_slope_in_list in Heqm.
simpl in Heqm.
destruct Heqm as [Hdp| Hdp].
 subst dp.
 simpl in Hlch.
 apply next_points_in_list in Hlch.
 destruct Hlch as [Hdp| Hdp].
  destruct Hdp; [ idtac | contradiction ].
  injection H; clear H; intros; subst d₃ p₃.
  eapply power_puiseux_series_list_lt; eassumption.

  eapply lt_trans with (m := d₂).
   eapply power_puiseux_series_list_lt; eassumption.

   eapply power_puiseux_series_list_2nd_lt; eassumption.

 apply lt_trans with (m := d₂).
  eapply power_puiseux_series_list_lt; eassumption.

  destruct dp as (d₄, p₄); simpl in Hlch.
  apply next_points_in_list in Hlch.
  destruct Hlch as [Hdp₃| Hdp₃].
   destruct Hdp₃; [ idtac | contradiction ].
   injection H; clear H; intros; subst d₄ p₄.
   eapply power_puiseux_series_list_2nd_lt; eassumption.

   eapply power_puiseux_series_list_2nd_lt; eassumption.
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

(*
Lemma www : ∀ α rl n l lt dpl mp₁₂ αi k kt lch αl γ αj j mp₂₃ m mt lch₁,
  next_points α rl n l lt dpl = [(mp₁₂, (k, kt)) … lch]
  → (∀ i it, (i, it) ∈ mp₁₂ → αi + Qnat i * γ == αj + Qnat j * γ)
    → αl + Qnat l * γ == αj + Qnat j * γ
      → next_points α [(mp₁₂, (l, lt)) … rl] n l lt dpl =
          [(mp₂₃, (m, mt)) … lch₁]
        → m = k ∧ mt = kt ∧ lch₁ = lch ∧ mp₂₃ = [(l, lt) … mp₁₂].
Proof.
www.
*)

(*
Lemma xxx : ∀ α i j k it jt kt αi αj αk γ mp₁₂ n dpl lch,
  αj = valuation α jt
  → αk = valuation α kt
    → γ = (αj - αk) / Qnat (k - j)
      → (i, it) ∈ mp₁₂
        → αi = valuation α it
          → next_points α [] n j jt dpl = [(mp₁₂, (k, kt)) … lch]
            → αi + Qnat i * γ == αj + Qnat j * γ.
Proof.
intros α i j k it jt kt αi αj αk γ mp₁₂ n dpl lch.
intros Hαj Hαk Hγ Hiit Hαi Hnp.
revert i Hiit.
revert j Hγ Hnp.
revert k it Hαi.
revert jt Hαj.
revert kt Hαk.
revert αi αj αk γ mp₁₂ n lch.
induction dpl as [| l jl]; intros; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct l as (d₂, p₂).
destruct n.
 remember (valuation α p₂ - valuation α jt) as v₂₁.
 remember (Qnat (d₂ - j)) as d₂₁.
 remember (minimise_slope α j jt d₂ p₂ (v₂₁ / d₂₁) 0 1 [ ] jl) as xs.
 subst v₂₁ d₂₁.
 destruct xs as (dp₃, sk).
xxx.
*)

Lemma yyy : ∀ α dpl mp₁ j jt mp₁₂ k kt lch αi αj αk γ i it,
  lower_convex_hull α dpl = [(mp₁, (j, jt)), (mp₁₂, (k, kt)) … lch]
  → αj = valuation α jt
    → αk = valuation α kt
      → γ = (αj - αk) / Qnat (k - j)
        → (i, it) ∈ mp₁₂
          → αi = valuation α it
            → αi + Qnat i * γ == αj + Qnat j * γ.
Proof.
intros α dpl mp₁ j jt mp₁₂ k kt lch αi αj αk γ i it.
intros Hlch Hαj Hαk Hγ Hiit Hαi.
destruct dpl as [| (l, jl)]; intros; [ discriminate Hlch | idtac ].
simpl in Hlch.
injection Hlch; intros Hnp; intros; subst jl l mp₁; clear Hlch.
destruct dpl; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct p as (l, lt).
remember (valuation α lt) as αl.
rewrite <- Hαj in Hnp.
remember ((αl - αj) / Qnat (l - j)) as sl.
remember (minimise_slope α j jt l lt sl 0 1 [ ] dpl) as xs.
subst sl.
destruct xs as (dp₃, skip).
destruct dpl.
 simpl in Hnp, Heqxs.
 injection Hnp; clear Hnp; intros; subst dp₃.
 injection Heqxs; clear Heqxs; intros; subst mp₁₂ skip l lt.
 contradiction.

 simpl in Hnp, Heqxs.
 destruct p as (m, mt).
 rewrite <- Hαj in Heqxs.
 remember (valuation α mt) as αm.
 destruct (Qeq_bool ((αm - αj) / Qnat (m - j)) ((αl - αj) / Qnat (l - j))).
  destruct skip.
   remember (snd (snd dp₃)) as nt.
   remember (valuation α nt) as αn.
   remember (fst (snd dp₃)) as n.
   remember
    (minimise_slope α n nt m mt ((αm - αn) / Qnat (m - n)) 0 1 [ ] dpl) as ds.
   destruct ds as (dp₄, skip).
yyy.

Lemma zzz : ∀ α fld (pol : polynomial (puiseux_series α)) lch,
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → lch = lower_convex_hull α (power_puiseux_series_list α fld pol)
      → ∃ γ mp₀ j jt mp₁₂ k kt,
           (mp₀, (j, jt)) ∈ lch ∧
           (mp₁₂, (k, kt)) ∈ lch ∧
           valuation α jt + Qnat j * γ == valuation α kt + Qnat k * γ ∧
           (∀ i it, (i, it) ∈ mp₁₂ →
              valuation α it + Qnat i * γ == valuation α jt + Qnat j * γ) ∧
           (∀ i it, (i, it) ∈ List.map (λ pmi, snd pmi) lch →
              valuation α jt + Qnat j * γ <= valuation α it + Qnat i * γ).
Proof.
intros α fld pol lch an_nz ai_nz Hlch.
apply gamma_beta_not_empty in ai_nz; [ idtac | assumption ].
remember (gamma_beta fld pol) as gb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; reflexivity ].
destruct p as ((γ, β), dpl).
exists γ.
unfold gamma_beta in Heqgb.
rewrite <- Hlch in Heqgb.
destruct lch; [ discriminate Heqgb | idtac ].
destruct p as (mp₁, (j, jt)).
destruct lch; [ discriminate Heqgb | idtac ].
destruct p as (mp₁₂, (k, kt)).
injection Heqgb; intros H₁ H₂ H₃; clear Heqgb.
exists mp₁, j, jt, mp₁₂, k, kt.
split; [ left; reflexivity | idtac ].
split; [ right; left; reflexivity | idtac ].
remember (valuation α jt) as αj.
remember (valuation α kt) as αk.
split.
 subst γ.
 unfold Qnat.
 rewrite Nat2Z.inj_sub.
  rewrite QZ_minus.
  field.
  intros H; symmetry in H; revert H.
  apply Qlt_not_eq, Qlt_minus.
  unfold Qlt; simpl.
  do 2 rewrite Z.mul_1_r.
  apply inj_lt.
  eapply lower_convex_hull_lt; symmetry; eassumption.

  apply lt_le_weak.
  eapply lower_convex_hull_lt; symmetry; eassumption.

 split.
  intros i it Hiit.
  remember (valuation α it) as αi.
  symmetry in Hlch.
  eapply yyy; eassumption.
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
