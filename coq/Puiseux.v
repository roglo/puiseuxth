(* $Id: Puiseux.v,v 1.145 2013-04-14 17:09:01 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).
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

Definition apply_poly {α} fld pol (x : α) :=
  List.fold_right (λ accu coeff, add fld (mul fld accu x) coeff) (an pol)
    (al pol).
Arguments apply_poly : default implicits. 

Record alg_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol x, @apply_poly α ac_field pol x = zero ac_field }.
Arguments ac_field : default implicits. 
Arguments ac_prop : default implicits. 

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] => [(pow, ps₁) … all_points_of_ps_polynom α (S pow) psl₁ psn]
  | [] => [(pow, psn)]
  end.

Definition filter_non_zero_ps α fld (dpl : list (nat * puiseux_series α)) :=
  List.filter (λ dp, if eq_k_dec fld (snd dp) (zero fld) then false else true)
    dpl.

Definition points_of_ps_polynom_gen α fld pow cl cn :=
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn).

Definition points_of_ps_polynom α fld pol :=
  points_of_ps_polynom_gen α fld 0%nat (al pol) (an pol).

Definition gamma_beta_gen α fld deg cl cn :=
  let gdpl := points_of_ps_polynom_gen α fld deg cl cn in
  match lower_convex_hull_points α gdpl with
  | [(j, jps), (k, kps) … _] =>
      let αj := valuation α jps in
      let αk := valuation α kps in
      let γ := (αj - αk) / Qnat (k - j)%nat in
      let β := αj + Qnat j * γ in
      let dpl := points_in_segment α γ β gdpl in
      Some (γ, β, (j, jps), (k, kps), dpl)
  | [_] | [] =>
      None
  end.

Definition gamma_beta {α} fld pol :=
  gamma_beta_gen α fld 0%nat (al pol) (an pol).
Arguments gamma_beta : default implicits.

Lemma one_vp_gen : ∀ α fld pow cl cn,
  cn ≠ zero fld → points_of_ps_polynom_gen α fld pow cl cn ≠ [].
Proof.
intros α fld pow cl cn Hcn.
unfold points_of_ps_polynom_gen.
remember (all_points_of_ps_polynom α pow cl cn) as cpl.
revert pow cpl Heqcpl.
induction cl as [| c cl]; intros.
 subst cpl; simpl.
 destruct (eq_k_dec fld cn (zero fld)); [ contradiction | simpl ].
 intros H; discriminate H.

 subst cpl; simpl.
 destruct (eq_k_dec fld c (zero fld)).
  eapply IHcl; reflexivity.

  simpl.
  intros H; discriminate H.
Qed.

Lemma at_least_one_valuation_point : ∀ α fld pol,
  an pol ≠ zero fld → points_of_ps_polynom α fld pol ≠ [].
Proof.
intros; apply one_vp_gen; assumption.
Qed.

Lemma fold_points_of_ps_polynom_gen : ∀ α fld pow cl cn,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn) =
  points_of_ps_polynom_gen α fld pow cl cn.
Proof. reflexivity. Qed.

Lemma two_vp_gen : ∀ α fld pow cl cn,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    → List.length (points_of_ps_polynom_gen α fld pow cl cn) ≥ 2.
Proof.
intros α fld pow cl cn Hcn Hcl.
revert pow.
induction cl as [| c]; intros.
 destruct Hcl as (c, (Hc, Hz)); contradiction.

 unfold points_of_ps_polynom_gen; simpl.
 destruct (eq_k_dec fld c (zero fld)).
  destruct Hcl as (c₁, ([Hc₁| Hc₁], Hz)).
   subst c₁; contradiction.

   apply IHcl.
   exists c₁.
   split; assumption.

  simpl.
  apply le_n_S.
  rewrite fold_points_of_ps_polynom_gen.
  remember (length (points_of_ps_polynom_gen α fld (S pow) cl cn)) as len.
  destruct len.
   remember (points_of_ps_polynom_gen α fld (S pow) cl cn) as l.
   destruct l; [ idtac | discriminate Heqlen ].
   exfalso; symmetry in Heql; revert Heql.
   apply one_vp_gen; assumption.

   apply le_n_S, le_0_n.
Qed.

Lemma at_least_two_points_of_ps_polynom : ∀ α fld pol,
  an pol ≠ zero fld
  → (∃ c, c ∈ (al pol) ∧ c ≠ zero fld)
    → List.length (points_of_ps_polynom α fld pol) ≥ 2.
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

Lemma next_points_not_empty : ∀ α dp dpl,
  next_points α dp dpl ≠ [ ].
Proof.
intros.
induction dpl as [| dp₂ dpl₂]; [ intros H; discriminate H | simpl ].
destruct (lt_dec (fst dp) (fst dp₂)); [ intros H; discriminate H | idtac ].
assumption.
Qed.

Lemma vp_pow_lt : ∀ α fld pow cl cn d₁ p₁ dpl,
  points_of_ps_polynom_gen α fld (S pow) cl cn = dpl
  → (d₁, p₁) ∈ dpl
    → lt pow d₁.
Proof.
intros α fld pow cl cn d₁ p₁ dpl Hvp Hdp.
revert fld pow cn d₁ p₁ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld cn (zero fld)) as [Heq| Hne].
  subst dpl; contradiction.

  simpl in Hvp.
  subst dpl; destruct Hdp as [Hdp| ]; [ idtac | contradiction ].
  injection Hdp; clear Hdp; intros; subst d₁ p₁.
  apply lt_n_Sn.

 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
  rewrite fold_points_of_ps_polynom_gen in Hvp.
  eapply IHcl in Hvp; [ idtac | eassumption ].
  eapply lt_trans; [ idtac | eassumption ].
  apply lt_n_Sn.

  simpl in Hvp.
  rewrite fold_points_of_ps_polynom_gen in Hvp.
  destruct dpl as [| (d₂, p₂)]; [ contradiction | idtac ].
  injection Hvp; clear Hvp; intros Hvp H₂ Hdpl; subst d₂ p₂.
  destruct Hdp as [Hdp| Hdp].
   injection Hdp; clear Hdp; intros; subst d₁ p₁.
   apply lt_n_Sn.

   eapply IHcl in Hvp; [ idtac | eassumption ].
   eapply lt_trans; [ idtac | eassumption ].
   apply lt_n_Sn.
Qed.

Lemma vp_lt : ∀ α fld pow cl cn d₁ p₁ d₂ p₂ dpl,
  points_of_ps_polynom_gen α fld pow cl cn = [(d₁, p₁) … dpl]
  → (d₂, p₂) ∈ dpl
    → lt d₁ d₂.
Proof.
intros α fld pow cl cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
revert fld pow cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld cn (zero fld)) as [| Hne]; [ discriminate Hvp | idtac ].
 injection Hvp; intros; subst; contradiction.

 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
  eapply IHcl; eassumption.

  simpl in Hvp.
  injection Hvp; clear Hvp; intros; subst d₁ p₁.
  rewrite fold_points_of_ps_polynom_gen in H.
  eapply vp_pow_lt; eassumption.
Qed.

Lemma points_of_ps_polynom_lt : ∀ α fld pol d₁ p₁ d₂ p₂ dpl,
  points_of_ps_polynom α fld pol = [(d₁, p₁), (d₂, p₂) … dpl]
  → (d₁ < d₂)%nat.
Proof.
intros; rename H into Hvp.
unfold points_of_ps_polynom in Hvp.
eapply vp_lt; [ eassumption | left; reflexivity ].
Qed.

Lemma gb_gen_not_empty : ∀ α fld deg cl cn,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    → gamma_beta_gen α fld deg cl cn ≠ None.
Proof.
intros α fld deg cl cn Hcn Hcl.
unfold gamma_beta_gen.
remember (points_of_ps_polynom_gen α fld deg cl cn) as pts.
remember (lower_convex_hull_points α pts) as chp.
destruct chp as [| (j, jps)].
 destruct pts as [| (j, jps)].
  symmetry in Heqpts.
  exfalso; revert Heqpts.
  apply one_vp_gen; assumption.

  symmetry in Heqchp.
  exfalso; revert Heqchp.
  apply next_points_not_empty.

 destruct chp as [| (k, kps)]; [ idtac | intros H; discriminate H ].
 destruct pts; [ discriminate Heqchp | idtac ].
 symmetry in Heqchp; simpl in Heqchp.
 destruct pts.
  eapply two_vp_gen with (pow := deg) in Hcl; [ idtac | eassumption ].
  rewrite <- Heqpts in Hcl.
  apply le_not_lt in Hcl.
  exfalso; apply Hcl, lt_n_Sn.

  simpl in Heqchp.
  destruct (lt_dec (fst p) (fst p0)).
   injection Heqchp; clear Heqchp; intros; subst p.
   exfalso; revert H; apply next_points_not_empty.

   exfalso; apply n; clear n.
   destruct p, p0; simpl.
   symmetry in Heqpts.
   eapply vp_lt; [ eassumption | left; reflexivity ].
Qed.

Lemma gamma_beta_not_empty : ∀ α fld (pol : polynomial (puiseux_series α)),
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → gamma_beta fld pol ≠ None.
Proof.
intros α fld pol an_nz ai_nz.
unfold gamma_beta.
apply gb_gen_not_empty; assumption.
Qed.

(*
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
*)

(*
Lemma vp_2nd_lt : ∀ α fld pow cl cn d₁ p₁ d₂ p₂ d₃ p₃ dpl,
  points_of_ps_polynom_gen α fld pow cl cn = [(d₁, p₁), (d₂, p₂) … dpl]
  → (d₃, p₃) ∈ dpl
    → lt d₂ d₃.
Proof.
intros α fld pow cl cn d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
revert fld pow cn d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld cn (zero fld)); discriminate Hvp.

 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
  rewrite fold_points_of_ps_polynom_gen in Hvp.
  eapply IHcl; eassumption.

  simpl in Hvp.
  rewrite fold_points_of_ps_polynom_gen in Hvp.
  injection Hvp; clear Hvp; intros Hvp H₁ H₂; subst d₁ p₁.
  eapply vp_lt; eassumption.
Qed.

Lemma points_of_ps_polynom_2nd_lt : ∀ α fld pol d₁ p₁ d₂ p₂ d₃ p₃ dpl,
  points_of_ps_polynom α fld pol = [(d₁, p₁), (d₂, p₂) … dpl]
  → (d₃, p₃) ∈ dpl
    → lt d₂ d₃.
Proof.
intros α fld pol d₁ p₁ d₂ p₂ d₃ p₃ dpl Hvp Hdp.
unfold points_of_ps_polynom in Hvp.
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
*)

Lemma QZ_plus : ∀ a b, a + b # 1 == (a # 1) + (b # 1).
Proof.
intros.
unfold Qplus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma QZ_minus : ∀ a b, a - b # 1 == (a # 1) - (b # 1).
Proof.
intros.
unfold Qminus, Qplus, Zminus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma points_in_newton_segment : ∀ α fld pol pts,
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → pts = points_of_ps_polynom α fld pol
      → ∃ γ β, ∀ i ips,
          (i, ips) ∈ points_in_segment α γ β pts
          → valuation α ips + Qnat i * γ == β.
Proof.
intros α fld pol pts an_nz ai_nz Hpts.
apply gamma_beta_not_empty in ai_nz; [ idtac | assumption ].
remember (gamma_beta fld pol) as gb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; reflexivity ].
destruct p as ((((γ, β), (j, jps)), (k, kps)), dpl).
exists γ, β.
intros i ips Hiit.
clear Hpts.
induction pts as [| pt]; intros; [ contradiction | idtac ].
simpl in Hiit.
remember (Qeq_bool (valuation α (snd pt) + Qnat (fst pt) * γ) β) as b.
symmetry in Heqb.
destruct b.
 destruct Hiit as [Hiit| Hiit].
  subst pt.
  simpl in Heqb.
  apply Qeq_bool_iff; assumption.

  apply IHpts; assumption.

 apply IHpts; assumption.
Qed.

(*
Lemma uuu : ∀ α fld deg cl cn pts rl n j jps k kps lch,
  cn ≠ zero fld
  → jps ≠ zero fld
    → pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α deg cl cn)
      → next_points α rl n j jps pts = [(k, kps) … lch]
        → (j < k)%nat.
Proof.
intros α fld deg cl cn pts rl n j jps k kps lch Hcn Hjps Hpts Hnp.
revert fld deg cn pts rl n j jps k kps lch Hcn Hjps Hpts Hnp.
induction cl as [| ps]; intros.
 subst pts; simpl in Hnp.
 destruct (eq_k_dec fld cn (zero fld)) as [| Hne]; [ contradiction | idtac ].
 simpl in Hnp.
 destruct n.
bbb.

Lemma vvv : ∀ α fld deg cl cn pts j jps k kps lch,
  pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α deg cl cn)
  → lower_convex_hull_points α pts = [(j, jps), (k, kps) … lch]
    → (j < k)%nat.
Proof.
intros α fld deg cl cn pts j jps k kps lch Hpts Hch.
revert fld deg cn pts j jps k kps lch Hpts Hch.
induction cl as [| ps]; intros.
 simpl in Hpts.
 subst pts.
 destruct (eq_k_dec fld cn (zero fld)); discriminate Hch.

 simpl in Hpts.
 destruct (eq_k_dec fld ps (zero fld)) as [Heq| Hne].
  eapply IHcl; eassumption.

  remember
   (filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)) as pts₁.
  subst pts.
  simpl in Hch.
  injection Hch; clear Hch; intros; subst deg ps.
  eapply uuu; eassumption.
bbb.

Lemma www : ∀ α fld deg cl cn pts j jps k kps lch,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → lower_convex_hull_points α pts = [(j, jps), (k, kps) … lch]
    → (j < k)%nat.
Proof.
intros α fld deg cl cn pts j jps k kps lch Hpts Hch.
revert fld deg cn pts j jps k kps lch Hpts Hch.
induction cl as [| ps]; intros.
 unfold points_of_ps_polynom_gen in Hpts.
 simpl in Hpts.
 destruct (eq_k_dec fld cn (zero fld)) as [Heq| Hne].
  subst pts; discriminate Hch.

  subst pts; discriminate Hch.

 unfold points_of_ps_polynom_gen in Hpts.
 simpl in Hpts.
 destruct (eq_k_dec fld ps (zero fld)) as [Heq| Hne].
  eapply vvv; eassumption.
bbb.

Lemma xxx : ∀ α fld pol pts j jps k kps lch,
  pts = points_of_ps_polynom α fld pol
  → lower_convex_hull_points α pts = [(j, jps), (k, kps) … lch]
    → (j < k)%nat.
Proof.
intros α fld pol pts j jps k kps lch Hpts Hch.
unfold points_of_ps_polynom in Hpts.
eapply www; eassumption.
bbb.

intros α fld pol pts j jps k kps lch Hpts Hch.
destruct pts as [| (l, lps)]; [ discriminate Hch | idtac ].
destruct pts as [| (m, mps)]; [ discriminate Hch | idtac ].
simpl in Hch.
remember ((valuation α mps - valuation α lps) / Qnat (m - l)) as sl.
remember (minimise_slope α l lps m mps sl 0 1 pts) as ms.
destruct ms as ((n, nps), sk).
simpl in Hch.
injection Hch; clear Hch; intros; subst l lps.
revert fld pol m mps j jps k kps lch sl n nps sk H Hpts Heqsl Heqms.
induction pts as [| (p, pps)]; intros.
 simpl in H.
 injection H; clear H; intros; subst lch n nps.
 simpl in Heqms.
 injection Heqms; clear Heqms; intros; subst m mps sk.
 symmetry in Hpts.
 eapply points_of_ps_polynom_lt; eassumption.
bbb.

Lemma yyy : ∀ α fld pol j jps k kps lch,
  lower_convex_hull_points α (points_of_ps_polynom α fld pol) =
    [(j, jps), (k, kps) … lch]
  → j ≠ k.
Proof.
intros; rename H into Hgb.
unfold gamma_beta in Hgb.
remember (points_of_ps_polynom α fld pol) as pts.
remember (lower_convex_hull_points α pts) as lch.
symmetry in Heqlch.
destruct lch as [| (l, lps)]; [ discriminate Hgb | idtac ].
destruct lch as [| (m, mps)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros H₁ H₂ H₃ H₄ H₆ Hβ Hγ.
subst l lps m mps seg_pts.
symmetry in Hγ, Hβ.
yyy.
*)

Lemma rev_app_le_val : ∀ α β γ i ips rl l lch,
  (∀ m mps, (m, mps) ∈ lch → β <= valuation α mps + Qnat m * γ)
  → List.rev rl ++ [(i, ips) … l] = lch
    →  β <= valuation α ips + Qnat i * γ.
Proof.
intros α β γ i ips rl l lch Hle Hrl.
revert i ips l lch Hle Hrl.
induction rl as [| (m, mps)]; intros.
 simpl in Hrl.
 apply Hle.
 rewrite <- Hrl.
 left; reflexivity.

 simpl in Hrl.
 rewrite <- List.app_assoc in Hrl.
 simpl in Hrl.
 remember (List.rev rl ++ [(i, ips), (m, mps) … l]) as lch₁.
 symmetry in Heqlch₁.
 eapply IHrl; [ idtac | eassumption ].
 intros n nps Hn.
 apply Hle.
 subst lch lch₁.
 apply List.in_app_iff in Hn.
 apply List.in_app_iff.
 destruct Hn as [Hn| Hn].
  left; assumption.

  right.
  destruct Hn as [Hn| Hn].
   injection Hn; clear Hn; intros; subst n nps.
   right; left; reflexivity.

   destruct Hn as [Hn| Hn].
    injection Hn; clear Hn; intros; subst n nps.
    left; reflexivity.

    right; right; assumption.
Qed.

Lemma min_sl_in : ∀ α iips jjps kkps sl pts,
  (iips, sl) = minimise_slope α jjps kkps pts
  → iips ∈ pts ∨ iips = kkps.
Proof.
intros α iips jjps kkps sl pts Hips.
revert iips jjps kkps sl Hips.
induction pts as [| llps]; intros.
 simpl in Hips.
 injection Hips; clear Hips; intros; subst iips sl.
 right; reflexivity.

 simpl in Hips.
 remember (minimise_slope α jjps llps pts) as x.
 destruct x as (mmps, sl₁).
 simpl in Hips.
 remember
  (Qle_bool sl₁
     ((valuation α (snd kkps) - valuation α (snd jjps)) /
      Qnat (fst kkps - fst jjps))) as b.
 destruct b.
  injection Hips; clear Hips; intros; subst mmps sl₁.
  apply IHpts in Heqx.
  destruct Heqx as [Heqx| Heqx].
   left; right; assumption.

   left; left; subst iips; reflexivity.

  injection Hips; clear Hips; intros; subst kkps sl.
  right; reflexivity.
Qed.

Lemma np_in : ∀ α iips pts lch,
  next_points α iips pts = lch
  → ∀ jjps, jjps ∈ lch → jjps = iips ∨ jjps ∈ pts.
Proof.
intros α iips pts lch Hnp jjps Hjps.
revert iips lch Hnp jjps Hjps.
induction pts as [| kkps]; intros.
 subst lch; simpl in Hjps.
 destruct Hjps; [ idtac | contradiction ].
 left; symmetry; assumption.

 simpl in Hnp.
 destruct (lt_dec (fst iips) (fst kkps)) as [Hlt| Hge].
  remember (minimise_slope α iips kkps pts) as ms.
  destruct ms as (llps, sl).
  simpl in Hnp.
  remember (next_points α llps pts) as lch₁.
  subst lch.
  destruct Hjps; [ left; symmetry; assumption | idtac ].
  symmetry in Heqlch₁.
  eapply IHpts in Heqlch₁; [ idtac | eassumption ].
  destruct Heqlch₁ as [HH| ]; [ idtac | right; right; assumption ].
  subst llps.
  apply min_sl_in in Heqms.
  destruct Heqms as [HH| HH].
   right; right; assumption.

   right; left; subst jjps; reflexivity.

  eapply IHpts in Hnp; [ idtac | eassumption ].
  destruct Hnp as [Hnp| Hnp].
   left; assumption.

   right; right; assumption.
Qed.

(*
Lemma vvv :
  pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α deg cl cn)
  → next_points α rl l lps pts = lch
    → β = valuation α jps + Qnat j * γ
      → β = valuation α kps + Qnat k * γ
        → (∀ m mps, (m, mps) ∈ rl → β <= valuation α mps + Qnat m * γ)
          → (∀ m mps, (m, mps) ∈ lch → β <= valuation α mps + Qnat m * γ).
Proof.
bbb.

Lemma www : ∀ α fld deg cl cn pts β γ j jps k kps l lps rl lch,
  pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α deg cl cn)
  → next_points α rl l lps pts = [(k, kps) … lch]
    → (∀ m mps, (m, mps) ∈ lch → β <= valuation α mps + Qnat m * γ)
      → β = valuation α jps + Qnat j * γ
        → β = valuation α kps + Qnat k * γ
          → ∀ i ips, (i, ips) ∈ pts
            → β <= valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts β γ j jps k kps l lps rl lch.
intros Hpts Hnp Hrng Hβj Hβk i ips Hips.
revert fld deg cn pts i ips l lps rl lch Hnp Hrng Hpts Hips.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (eq_k_dec fld cn (zero fld)) as [Heq| Hne].
  subst pts; contradiction.

  subst pts.
  destruct Hips; [ idtac | contradiction ].
  injection H; clear H; intros; subst deg cn.
  simpl in Hnp.
  destruct (lt_dec l i) as [Hlt| Hge].
   eapply rev_app_le_val; [ idtac | eassumption ].
   intros m mps Hin.
   destruct Hin as [Hin| Hin].
    injection Hin; clear Hin; intros; subst m mps.
    rewrite <- Hβk; apply Qle_refl.

    apply Hrng; assumption.
bbb.

Lemma xxx₂ : ∀ α fld deg cl cn γ β j jps k kps l lps i ips pts lch rl,
  β = valuation α jps + Qnat j * γ
  → β = valuation α kps + Qnat k * γ
    → pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α deg cl cn)
      → (i, ips) ∈ pts
        → (i, ips) ∉ points_in_segment α γ β pts
          → next_points α rl l lps pts = [(k, kps) … lch]
            → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn γ β j jps k kps l lps i ips pts lch rl.
intros Hβj Hβk Hpts Hips Hipsn Hnp.
revert Hpts Hips Hipsn Hnp.
revert fld deg cn l lps i ips pts lch rl.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (eq_k_dec fld cn (zero fld)) as [Heq| Hne].
  subst pts; contradiction.

  subst pts.
  destruct Hips as [Hips| ]; [ idtac | contradiction ].
  injection Hips; clear Hips; intros; subst deg cn.
  simpl in Hipsn.
  remember (Qeq_bool (valuation α ips + Qnat i * γ) β) as b.
  destruct b.
   simpl in Hipsn.
   apply Decidable.not_or in Hipsn.
   destruct Hipsn as (H); exfalso; apply H; reflexivity.

   symmetry in Heqb.
   apply Qeq_bool_neq in Heqb.
   apply Qnot_le_lt.
   intros H; apply Heqb; clear Heqb.
   apply Qle_antisym; [ assumption | idtac ].
   Focus 2.
   simpl in Hpts.
   destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
    eapply IHcl; eassumption.

    remember
     (filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)) as pts₁.
    subst pts.
    rename pts₁ into pts.
    rename Heqpts₁ into Heqpts.
    destruct Hips as [Hips| Hips].
     injection Hips; clear Hips; intros; subst deg c.
     simpl in Hipsn.
     remember (Qeq_bool (valuation α ips + Qnat i * γ) β) as b.
     destruct b.
      simpl in Hipsn.
      apply Decidable.not_or in Hipsn.
      destruct Hipsn as (H).
      exfalso; apply H; reflexivity.

      Focus 2.
      simpl in Hipsn.
      remember (Qeq_bool (valuation α c + Qnat deg * γ) β) as b.
      simpl in Hnp.
      remember
       (minimise_slope α l lps (deg, c)
          ((valuation α c - valuation α lps) / Qnat (deg - l)) pts) as sl.
      destruct sl as (m, mps).
      destruct b.
       simpl in Hipsn.
       apply Decidable.not_or in Hipsn.
       destruct Hipsn as (H, Hipsn).
       destruct (lt_dec l deg); eapply IHcl; eassumption.

       destruct (lt_dec l deg); eapply IHcl; eassumption.

     symmetry in Heqb.
     apply Qeq_bool_neq in Heqb.
     simpl in Hnp.
     remember
      (minimise_slope α l lps (i, ips)
         ((valuation α ips - valuation α lps) / Qnat (i - l)) pts) as sl.
     destruct sl as (m, mps).
     destruct (lt_dec l i) as [Hle| Hgt].
      apply Qnot_le_lt.
      intros H; apply Heqb.
      apply Qle_antisym; [ assumption | idtac ].
bbb.

Lemma yyy₄ : ∀ α fld deg cl cn i ips j jps k kps pts lch γ β,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → β = valuation α jps + Qnat j * γ
    → β = valuation α kps + Qnat k * γ
      → (i, ips) ∈ pts
        → (i, ips) ∉ points_in_segment α γ β pts
          → lower_convex_hull_points α pts = [(j, jps), (k, kps) … lch]
            → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn i ips j jps k kps pts lch γ β.
intros Hpts Hβj Hβk Hipts Hipis Hch.
unfold points_of_ps_polynom_gen in Hpts.
revert Hpts Hipts Hipis Hch.
revert fld deg cn i ips pts lch.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (eq_k_dec fld cn (zero fld)); subst pts; discriminate Hch.

 simpl in Hpts.
 destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
  eapply IHcl; eassumption.

  remember
   (filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)) as pts₁.
  subst pts.
  rename pts₁ into pts.
  rename Heqpts₁ into Heqpts.
  destruct Hipts as [Hips| Hips].
   injection Hips; clear Hips; intros; subst deg c.
   simpl in Hch.
   injection Hch; clear Hch; intros; subst i ips.
   simpl in Hipis.
   rewrite <- Hβj in Hipis.
   remember (Qeq_bool β β) as b.
   destruct b.
    exfalso; apply Hipis; left; reflexivity.

    symmetry in Heqb.
    apply Qeq_bool_neq in Heqb; exfalso; apply Heqb; reflexivity.

   simpl in Hch.
   injection Hch; clear Hch; intros; subst deg c.
   simpl in Hipis.
   rewrite <- Hβj in Hipis.
   remember (Qeq_bool β β) as b.
   destruct b.
    simpl in Hipis.
    apply Decidable.not_or in Hipis.
    destruct Hipis as (Hjps, Hipis).
    destruct Hipis as (Hjps, Hipis).
    eapply xxx₂; eassumption.

    symmetry in Heqb.
    apply Qeq_bool_neq in Heqb; exfalso; apply Heqb; reflexivity.
bbb.
*)

(*
Lemma yyy : ∀ α fld deg cl cn pts,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    → pts = points_of_ps_polynom_gen α fld deg cl cn
      → ∃ γ β,
        (∀ i ips, (i, ips) ∈ pts ∧ (i, ips) ∉ points_in_segment α γ β pts
           → β < valuation α ips + Qnat i * γ).
Proof.
intros α fld deg cl cn pts Hcn Hcl Hpts.
bbb.
*)

Lemma minus_Sn_n : ∀ n, (S n - n = 1)%nat.
Proof.
intros n.
rewrite <- minus_Sn_m; [ rewrite minus_diag; reflexivity | apply le_n ].
Qed.

Lemma np_beta_le : ∀ α pts γ β j jps k kps lch,
  γ = (valuation α jps - valuation α kps) / Qnat (k - j)
  → β = valuation α jps + Qnat j * γ
    → ∀ i ips,
        next_points α (i, ips) pts = [(j, jps), (k, kps) … lch]
        → β <= valuation α ips + Qnat i * γ.
Proof.
intros α pts γ β j jps k kps lch Hγ Hβ i ips Hnp.
revert lch i ips Hnp.
induction pts as [| (l, lps)]; intros.
 discriminate Hnp.

 simpl in Hnp.
 destruct (lt_dec i l) as [Hlt| Hge].
  injection Hnp; clear Hnp; intros; subst i ips.
  subst β; apply Qle_refl.

  eapply IHpts; eassumption.
Qed.

Lemma not_seg_le : ∀ α fld deg cl cn pts i ips j jps k kps lch β γ,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → next_points α (i, ips) pts = [(j, jps), (k, kps) … lch]
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → (i, ips) ∉ points_in_segment α γ β pts
          → β <= valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts i ips j jps k kps lch β γ Hpts Hnp Hγ Hβ Hips.
unfold points_of_ps_polynom_gen in Hpts.
revert deg cn pts i ips lch Hpts Hnp Hips.
induction cl as [| c]; intros.
 simpl in Hpts; subst pts.
 destruct (eq_k_dec fld cn (zero fld)) as [Heq| Hne].
  simpl in Hnp; discriminate Hnp.

  simpl in Hnp.
  destruct (lt_dec i deg) as [Hlt| Hge].
   injection Hnp; clear Hnp; intros; subst i ips deg cn lch.
   subst β; apply Qle_refl.

   discriminate Hnp.

 simpl in Hpts.
 destruct (eq_k_dec fld c (zero fld)) as [Heq| Hne].
  eapply IHcl; eassumption.

  remember
   (filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)) as pts₁.
  subst pts.
  simpl in Hnp.
  destruct (lt_dec i deg) as [Hlt| Hge].
   injection Hnp; clear Hnp; intros; subst i ips.
   subst β; apply Qle_refl.

   simpl in Hips.
   remember (Qeq_bool (valuation α c + Qnat deg * γ) β) as b.
   destruct b.
    eapply IHcl; try eassumption.
    intros H; apply Hips; clear Hips.
    right; assumption.

    eapply IHcl; try eassumption.
Qed.

(*
Lemma xxx : ∀ α fld deg cl cn pts c j jps k kps lch i ips β γ,
  pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)
  → next_points α (deg, c) pts = [(j, jps), (k, kps) … lch]
    → β == valuation α c + Qnat deg * γ
      → (i, ips) ∈ pts
        → (i, ips) ∉ points_in_segment α γ β pts
          → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts c j jps k kps lch i ips β γ.
intros Hpts Hnp Hβ Hips Hnips.

revert deg cn pts c j jps k kps lch i ips β γ Hpts Hnp Hips Hnips.
induction cl as [| c₁]; intros.
 simpl in Hpts; subst pts.
 destruct (eq_k_dec fld cn (zero fld)); [ discriminate Hnp | idtac ].
 simpl in Hnp.
 destruct (lt_dec deg (S deg)).
  injection Hnp; clear Hnp; intros; subst j jps k kps lch.
  destruct Hips; [ idtac | contradiction ].
  injection H; clear H; intros; subst i ips.
  simpl in Hnips.
  remember (Qeq_bool (valuation α cn + Qnat (S deg) * γ) β) as b.
  destruct b.
   exfalso; apply Hnips; left; reflexivity.

   Focus 2.
   exfalso; apply n0.
   apply lt_n_Sn.
bbb.
*)

(*
Lemma yyy : ∀ α fld deg cl cn pts j jps k kps lch β γ,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → lower_convex_hull_points α pts = [(j, jps), (k, kps) … lch]
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → ∀ i ips,
            (i, ips) ∈ pts
            → (i, ips) ∉ points_in_segment α γ β pts
              → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts j jps k kps lch β γ Hpts Hch Hγ Hβ.
intros i ips Hips Hnips.
unfold points_of_ps_polynom_gen in Hpts.
revert deg cn pts lch Hpts Hch i ips Hips Hnips.
induction cl as [| c]; intros.
 simpl in Hpts.
 subst pts.
 destruct (eq_k_dec fld cn (zero fld)); [ contradiction | discriminate Hch ].

 simpl in Hpts.
 destruct (eq_k_dec fld c (zero fld)) as [Hlt| Hge].
  eapply IHcl; eassumption.

  remember
   (filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)) as pts₁.
  subst pts.
  simpl in Hch.
  destruct Hips as [Hips| Hips].
   injection Hips; clear Hips; intros; subst deg c.
   simpl in Hnips.
   remember (Qeq_bool (valuation α ips + Qnat i * γ) β) as b.
   destruct b.
    exfalso; apply Hnips; left; reflexivity.

    apply Qnot_le_lt.
    symmetry in Heqb.
    apply Qeq_bool_neq in Heqb.
    intros H; apply Heqb.
    apply Qeq_sym.
    apply Qle_antisym; [ idtac | eassumption ].
    eapply not_seg_le; eassumption.

   simpl in Hnips.
   remember (Qeq_bool (valuation α c + Qnat deg * γ) β) as b.
   destruct b.
    simpl in Hnips.
    apply Decidable.not_or in Hnips.
    destruct Hnips as (Hdeg, Hnips).
    exfalso; apply Hnips.

bbb.
*)

Lemma zzz₁ : ∀ α fld deg cl cn pts,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    →  pts = points_of_ps_polynom_gen α fld deg cl cn
      → ∃ γ β,
        (∀ i ips, (i, ips) ∈ pts ∧ (i, ips) ∉ points_in_segment α γ β pts
           → β < valuation α ips + Qnat i * γ).
Proof.
intros α fld deg cl cn pts an_nz ai_nz Hpts.
eapply gb_gen_not_empty in ai_nz; [ idtac | eassumption ].
remember (gamma_beta_gen α fld deg cl cn) as gb.
symmetry in Heqgb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; eassumption ].
destruct p as ((((γ, β), (j, jps)), (k, kps)), seg_pts).
exists γ, β.
intros i ips Hiit.
destruct Hiit as (Hin, Hout).
unfold gamma_beta_gen in Heqgb.
remember
 (lower_convex_hull_points α (points_of_ps_polynom_gen α fld deg cl cn)) as lch.
destruct lch as [| (l, lt)]; [ discriminate Heqgb | idtac ].
destruct lch as [| (m, mt)]; [ discriminate Heqgb | idtac ].
injection Heqgb; clear Heqgb; intros; subst l lt m mt.
rewrite H5 in H.
rewrite H5 in H4.
rewrite H4 in H.
symmetry in H4; rename H4 into Hβ.
symmetry in H5; rename H5 into Hγ.
rewrite <- Hpts in H.
rewrite H in Hout.
rewrite <- Hpts in Heqlch.
symmetry in Heqlch.
subst seg_pts.
eapply yyy; eassumption.
bbb.

Lemma zzz : ∀ α fld pol pts,
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → pts = points_of_ps_polynom α fld pol
      → ∃ γ β,
        (∀ i ips, (i, ips) ∈ pts ∧ (i, ips) ∉ points_in_segment α γ β pts
           → β < valuation α ips + Qnat i * γ).
Proof.
intros α fld pol pts an_nz ai_nz Hpts.
bbb.
apply gamma_beta_not_empty in ai_nz; [ idtac | assumption ].
remember (gamma_beta fld pol) as gb.
destruct gb; [ clear ai_nz | exfalso; apply ai_nz; reflexivity ].
destruct p as ((((γ, β), (j, jps)), (k, kps)), seg_pts).
exists γ, β.
intros i ips Hiit.
destruct Hiit as (Hin, Hout).
symmetry in Heqgb.
unfold gamma_beta in Heqgb.
remember (lower_convex_hull_points α (points_of_ps_polynom α fld pol)) as lch.
destruct lch as [| (l, lt)]; [ discriminate Heqgb | idtac ].
destruct lch as [| (m, mt)]; [ discriminate Heqgb | idtac ].
injection Heqgb; clear Heqgb; intros; subst l lt m mt.
rewrite H5 in H.
rewrite H5 in H4.
rewrite H4 in H.
symmetry in H4; rename H4 into Hβ.
symmetry in H5; rename H5 into Hγ.
rewrite <- Hpts in H.
rewrite H in Hout.
rewrite <- Hpts in Heqlch.
symmetry in Heqlch.
subst seg_pts.
bbb.
eapply yyy; try eassumption.
 rewrite Hβ; reflexivity.

 rewrite Hβ, Hγ.
 unfold Qnat.
 rewrite Nat2Z.inj_sub.
  rewrite QZ_minus.
  field.
  intros H.
  unfold Qminus in H.
  unfold Qplus in H.
  simpl in H.
  do 2 rewrite Z.mul_1_r in H.
  unfold Qeq in H.
  simpl in H.
  rewrite Z.mul_1_r in H.

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
    let pol := cancel_pol_constant_term_if_any fld pol in
    dp_float_round_zero fld pol
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
       if eq k r (zero fld) then sol_list
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
