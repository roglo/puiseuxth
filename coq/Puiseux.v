(* $Id: Puiseux.v,v 1.326 2013-04-26 01:07:27 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.
Require Import Misc.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat (at level 70, y at next level).

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    mul : α → α → α;
    div : α → α → α;
    is_zero_dec : ∀ x : α, {x = zero} + {x ≠ zero} }.
Arguments zero : default implicits.
Arguments add : default implicits.
Arguments sub : default implicits.
Arguments mul : default implicits.
Arguments div : default implicits. 
Arguments is_zero_dec : default implicits. 

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
  List.filter (λ dp, if is_zero_dec fld (snd dp) then false else true)
    dpl.

Definition points_of_ps_polynom_gen α fld pow cl cn :=
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn).

Definition points_of_ps_polynom α fld pol :=
  points_of_ps_polynom_gen α fld 0%nat (al pol) (an pol).

Definition gamma_beta_gen α fld deg cl cn :=
  let gdpl := points_of_ps_polynom_gen α fld deg cl cn in
  match lower_convex_hull_points α gdpl with
  | [((j, jps), seg); ((k, kps), _) … _] =>
      let αj := valuation α jps in
      let αk := valuation α kps in
      let γ := (αj - αk) / Qnat (k - j)%nat in
      let β := αj + Qnat j * γ in
      Some (γ, β, (j, jps), (k, kps), seg)
  | [_] | [] =>
      None
  end.

Definition gamma_beta {α} fld pol :=
  gamma_beta_gen α fld 0%nat (al pol) (an pol).
Arguments gamma_beta : default implicits.

Section puiseux_field.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma one_vp_gen : ∀ pow cl cn,
  cn ≠ zero fld → points_of_ps_polynom_gen α fld pow cl cn ≠ [].
Proof.
intros pow cl cn Hcn.
unfold points_of_ps_polynom_gen.
remember (all_points_of_ps_polynom α pow cl cn) as cpl.
revert pow cpl Heqcpl.
induction cl as [| c cl]; intros.
 subst cpl; simpl.
 destruct (is_zero_dec fld cn); [ contradiction | simpl ].
 intros H; discriminate H.

 subst cpl; simpl.
 destruct (is_zero_dec fld c).
  eapply IHcl; reflexivity.

  simpl.
  intros H; discriminate H.
Qed.

Lemma at_least_one_valuation_point : ∀ pol,
  an pol ≠ zero fld → points_of_ps_polynom α fld pol ≠ [].
Proof.
intros; apply one_vp_gen; assumption.
Qed.

Lemma fold_points_of_ps_polynom_gen : ∀ pow cl cn,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn) =
  points_of_ps_polynom_gen α fld pow cl cn.
Proof. reflexivity. Qed.

Lemma two_vp_gen : ∀ pow cl cn,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    → List.length (points_of_ps_polynom_gen α fld pow cl cn) ≥ 2.
Proof.
intros pow cl cn Hcn Hcl.
revert pow.
induction cl as [| c]; intros.
 destruct Hcl as (c, (Hc, Hz)); contradiction.

 unfold points_of_ps_polynom_gen; simpl.
 destruct (is_zero_dec fld c).
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

Lemma at_least_two_points_of_ps_polynom : ∀ pol,
  an pol ≠ zero fld
  → (∃ c, c ∈ (al pol) ∧ c ≠ zero fld)
    → List.length (points_of_ps_polynom α fld pol) ≥ 2.
Proof.
intros; apply two_vp_gen; assumption.
Qed.

Lemma lower_convex_points_empty_iff : ∀ dpl,
  lower_convex_hull_points α dpl = [ ] ↔ dpl = [].
Proof.
intros dpl.
unfold lower_convex_hull_points.
split; intros H; [ idtac | subst dpl; reflexivity ].
destruct dpl as [| dp₁ dpl₁]; [ reflexivity | simpl in H ].
destruct dpl₁; discriminate H.
Qed.

Lemma vp_pow_lt : ∀ pow cl cn d₁ p₁ dpl,
  points_of_ps_polynom_gen α fld (S pow) cl cn = dpl
  → (d₁, p₁) ∈ dpl
    → (pow < d₁)%nat.
Proof.
intros pow cl cn d₁ p₁ dpl Hvp Hdp.
revert pow cn d₁ p₁ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (is_zero_dec fld cn) as [Heq| Hne].
  subst dpl; contradiction.

  simpl in Hvp.
  subst dpl; destruct Hdp as [Hdp| ]; [ idtac | contradiction ].
  injection Hdp; clear Hdp; intros; subst d₁ p₁.
  apply lt_n_Sn.

 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (is_zero_dec fld c) as [Heq| Hne].
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

Lemma vp_lt : ∀ pow cl cn d₁ p₁ d₂ p₂ dpl,
  points_of_ps_polynom_gen α fld pow cl cn = [(d₁, p₁) … dpl]
  → (d₂, p₂) ∈ dpl
    → (d₁ < d₂)%nat.
Proof.
intros pow cl cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
revert pow cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (is_zero_dec fld cn) as [| Hne]; [ discriminate Hvp | idtac ].
 injection Hvp; intros; subst; contradiction.

 unfold points_of_ps_polynom_gen in Hvp; simpl in Hvp.
 destruct (is_zero_dec fld c) as [Heq| Hne].
  eapply IHcl; eassumption.

  simpl in Hvp.
  injection Hvp; clear Hvp; intros; subst d₁ p₁.
  rewrite fold_points_of_ps_polynom_gen in H.
  eapply vp_pow_lt; eassumption.
Qed.

Lemma points_of_ps_polynom_lt : ∀ pol d₁ p₁ d₂ p₂ dpl,
  points_of_ps_polynom α fld pol = [(d₁, p₁); (d₂, p₂) … dpl]
  → (d₁ < d₂)%nat.
Proof.
intros; rename H into Hvp.
unfold points_of_ps_polynom in Hvp.
eapply vp_lt; [ eassumption | left; reflexivity ].
Qed.

Lemma gb_gen_not_empty : ∀ deg cl cn,
  cn ≠ zero fld
  → (∃ c, c ∈ cl ∧ c ≠ zero fld)
    → gamma_beta_gen α fld deg cl cn ≠ None.
Proof.
intros deg cl cn Hcn Hcl.
unfold gamma_beta_gen.
remember (points_of_ps_polynom_gen α fld deg cl cn) as pts.
remember (lower_convex_hull_points α pts) as chp.
destruct chp as [| (j, jps)].
 destruct pts as [| (j, jps)].
  symmetry in Heqpts.
  exfalso; revert Heqpts.
  apply one_vp_gen; assumption.

  destruct pts; discriminate Heqchp.

 destruct j.
 destruct chp as [| ((k, kps), seg)]; [ idtac | intros H; discriminate H ].
 destruct pts; [ discriminate Heqchp | idtac ].
 symmetry in Heqchp; simpl in Heqchp.
 destruct pts.
  eapply two_vp_gen with (pow := deg) in Hcl; [ idtac | eassumption ].
  rewrite <- Heqpts in Hcl.
  apply le_not_lt in Hcl.
  exfalso; apply Hcl, lt_n_Sn.

  unfold lower_convex_hull_points in Heqchp.
  simpl in Heqchp.
  remember (minimise_slope α p0 p1 pts) as ms.
  injection Heqchp; clear Heqchp; intros; subst p0 jps.
  destruct (rem_pts ms); [ discriminate H | idtac ].
  discriminate H.
Qed.

Lemma gamma_beta_not_empty : ∀ (pol : polynomial (puiseux_series α)),
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → gamma_beta fld pol ≠ None.
Proof.
intros pol an_nz ai_nz.
unfold gamma_beta.
apply gb_gen_not_empty; assumption.
Qed.

Definition fst_lt {α} (x y : nat * α) :=
  (fst x < fst y)%nat.
Definition fst_fst_lt {α β} (x y : (nat * α) * β) :=
  (fst (fst x) < fst (fst y))%nat.

Lemma LocallySorted_inv_1 {A} : ∀ (f : A → A → Prop) x l,
  LocallySorted f [x … l]
  → LocallySorted f l.
Proof.
intros f x l H.
inversion H; [ constructor | assumption ].
Qed.

Lemma LocallySorted_inv_2 {A} : ∀ (f : A → A → Prop) x y l,
  LocallySorted f [x; y … l]
  → f x y ∧ LocallySorted f [y … l].
Proof.
intros f x y l H.
inversion H; subst a b l0.
split; assumption.
Qed.

Lemma LocallySorted_hd {A} : ∀ (pt₁ pt₂ : nat * A) pts,
  LocallySorted fst_lt [pt₁ … pts]
  → pt₂ ∈ pts
    → (fst pt₁ < fst pt₂)%nat.
Proof.
intros pt₁ pt₂ pts Hsort Hpt.
revert pt₁ pt₂ Hsort Hpt.
induction pts as [| pt]; intros; [ contradiction | idtac ].
apply LocallySorted_inv_2 in Hsort.
destruct Hsort as (Hlt, Hsort).
destruct Hpt as [Hpt| Hpt]; [ subst pt; assumption | idtac ].
eapply lt_trans; [ eassumption | idtac ].
apply IHpts; assumption.
Qed.

Lemma points_of_polyn_sorted : ∀ deg cl cn pts,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → LocallySorted fst_lt pts.
Proof.
intros deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (is_zero_dec fld cn); subst pts; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 rewrite fold_points_of_ps_polynom_gen in Hpts.
 destruct (is_zero_dec fld c) as [Heq| Hne].
  eapply IHcl; eassumption.

  remember (points_of_ps_polynom_gen α fld (S deg) cl cn) as pts₁.
  subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
  clear IHcl.
  clear Hne.
  revert c deg cn pts Hpts.
  induction cl as [| c₂]; intros.
   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   destruct (is_zero_dec fld cn) as [Heq| Hne].
    subst pts; constructor.

    subst pts.
    constructor; [ constructor | apply lt_n_Sn ].

   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   rewrite fold_points_of_ps_polynom_gen in Hpts.
   destruct (is_zero_dec fld c₂) as [Heq| Hne].
    eapply IHcl with (c := c) in Hpts.
    destruct pts as [| pt]; [ constructor | idtac ].
    apply LocallySorted_inv_2 in Hpts.
    destruct Hpts as (Hlt, Hpts).
    constructor; [ assumption | idtac ].
    eapply lt_trans; [ apply lt_n_Sn | eassumption ].

    subst pts.
    constructor; [ eapply IHcl; reflexivity | apply lt_n_Sn ].
Qed.

Lemma minimise_slope_le : ∀ pt₁ pt₂ pts₂ ms,
  LocallySorted fst_lt [pt₂ … pts₂]
  → minimise_slope α pt₁ pt₂ pts₂ = ms
    → fst pt₂ ≤ fst (end_pt ms).
Proof.
intros pt₁ pt₂ pts₂ ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts₂ as [| pt]; intros.
 subst ms; apply le_n.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt pts₂) as ms₁.
 remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
 destruct c; subst ms; simpl; [ idtac | reflexivity | idtac ].
  apply lt_le_weak.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply lt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.

  apply lt_le_weak.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply lt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.
Qed.

Lemma min_sl_in : ∀ pt₁ pt₂ pts₂ ms,
  minimise_slope α pt₁ pt₂ pts₂ = ms
  → end_pt ms ∈ [pt₂ … pts₂].
Proof.
intros pt₁ pt₂ pts₂ ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts₂ as [| pt]; intros.
 subst ms; left; reflexivity.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt pts₂) as ms₁.
 remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqms₁.
 destruct c; subst ms; simpl; [ idtac | left; reflexivity | idtac ].
  apply IHpts₂ in Heqms₁.
  destruct Heqms₁; [ subst pt; right; left; reflexivity | idtac ].
  right; right; assumption.

  apply IHpts₂ in Heqms₁.
  destruct Heqms₁; [ subst pt; right; left; reflexivity | idtac ].
  right; right; assumption.
Qed.

Lemma in_rem_pts : ∀ pt pt₁ pt₂ pts₂,
  pt ∈ rem_pts (minimise_slope α pt₁ pt₂ pts₂)
  → pt ∈ [pt₂ … pts₂].
Proof.
intros pt pt₁ pt₂ pts₂ Hpt.
revert pt₁ pt₂ pt Hpt.
induction pts₂ as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hpt.
remember (minimise_slope α pt₁ pt₃ pts₂) as ms.
remember (slope_expr α pt₁ pt₂ ?= slope ms) as c.
destruct c; simpl in Hpt; [ idtac | right; assumption | idtac ].
 subst ms.
 apply IHpts₂ in Hpt.
 right; assumption.

 subst ms.
 apply IHpts₂ in Hpt.
 right; assumption.
Qed.

Lemma np_in : ∀ n pts lch,
  next_ch_points α n pts = lch
  → ∀ pt, pt ∈ List.map (λ ms, fst ms) lch
    → pt ∈ pts.
Proof.
intros n pts lch Hnp pt Hpt.
subst lch.
revert pts pt Hpt.
induction n; intros; [ contradiction | simpl in Hpt ].
destruct pts as [| pt₁]; [ contradiction | idtac ].
destruct pts as [| pt₂]; [ assumption | idtac ].
simpl in Hpt.
destruct Hpt; [ subst pt₁; left; reflexivity | idtac ].
remember (minimise_slope α pt₁ pt₂ pts) as ms.
symmetry in Heqms.
remember Heqms as Hms; clear HeqHms.
apply min_sl_in in Heqms.
apply IHn in H.
destruct H as [H| H].
 subst pt.
 right; assumption.

 subst ms;
 right; eapply in_rem_pts; eassumption.
Qed.

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pts₁ sg lch,
  next_ch_points α n [pt₁ … pts₁] = [(pt₂, sg) … lch]
  → fst pt₁ ≤ fst pt₂.
Proof.
intros n pt₁ pt₂ pts₁ sg lch Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts₁; injection Hnp; intros; subst pt₁; reflexivity.
Qed.

Lemma minimise_slope_sorted : ∀ pt₁ pt₂ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → LocallySorted fst_lt [end_pt ms … rem_pts ms].
Proof.
intros pt₁ pt₂ pts ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros; [ subst ms; constructor | idtac ].
simpl in Hms.
remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqms₁.
apply LocallySorted_inv_2 in Hsort.
destruct Hsort as (Hlt₁, Hsort).
destruct c; subst ms; simpl; [ idtac | assumption | idtac ].
 eapply IHpts; [ idtac | eassumption ].
 apply LocallySorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 constructor; [ assumption | eapply lt_trans; eassumption ].

 eapply IHpts; [ idtac | eassumption ].
 apply LocallySorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 constructor; [ assumption | eapply lt_trans; eassumption ].
Qed.

Lemma next_points_sorted : ∀ n pts lch,
  LocallySorted fst_lt pts
  → next_ch_points α n pts = lch
    → LocallySorted fst_fst_lt lch.
Proof.
intros n pts lch Hsort Hnp.
revert pts lch Hsort Hnp.
induction n; intros; [ subst lch; constructor | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ subst lch; constructor | idtac ].
destruct pts as [| pt₂]; [ subst lch; constructor | idtac ].
remember (minimise_slope α pt₁ pt₂ pts) as ms₂.
remember (next_ch_points α n [end_pt ms₂ … rem_pts ms₂]) as lch₁.
subst lch.
symmetry in Heqlch₁.
remember Heqlch₁ as Hch; clear HeqHch.
apply IHn in Heqlch₁.
 destruct lch₁ as [| (pt₃, sg)]; [ constructor | idtac ].
 constructor; [ assumption | idtac ].
 unfold fst_fst_lt; simpl.
 symmetry in Heqms₂.
 remember Heqms₂ as Hms; clear HeqHms.
 apply minimise_slope_le in Heqms₂.
  eapply lt_le_trans.
   apply LocallySorted_inv_2 in Hsort; destruct Hsort; eassumption.

   eapply le_trans; [ eassumption | idtac ].
   eapply next_ch_points_le; eassumption.

  apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.

 symmetry in Heqms₂.
 eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lower_convex_hull_points_sorted : ∀ pts lch,
  LocallySorted fst_lt pts
  → lower_convex_hull_points α pts = lch
    → LocallySorted fst_fst_lt lch.
Proof.
intros pts lch Hsort Hch.
eapply next_points_sorted; eassumption.
Qed.

Lemma next_ch_points_hd : ∀ n pt₁ pt₂ pts₁ seg lch,
  next_ch_points α n [pt₁ … pts₁] = [(pt₂, seg) … lch]
  → pt₁ = pt₂.
Proof.
intros n pt₁ pt₂ pts₂ seg₂ lch Hnp.
revert pt₁ pt₂ pts₂ seg₂ lch Hnp.
induction n; intros; [ discriminate Hnp | simpl in Hnp ].
destruct pts₂; injection Hnp; intros; subst pt₂; reflexivity.
Qed.

Lemma minimised_slope : ∀ j jps k kps pt pts ms,
  minimise_slope α (j, jps) pt pts = ms
  → (k, kps) = end_pt ms
    → slope ms == slope_expr α (j, jps) (k, kps).
Proof.
intros j jps k kps pt pts ms Hms Hkps.
revert j jps k kps pt ms Hms Hkps.
induction pts as [| pt₁]; intros.
 subst ms; simpl in Hkps |- *; subst pt; reflexivity.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 symmetry in Heqms₁.
 destruct c; subst ms; simpl in Hkps |- *.
  eapply IHpts; eassumption.

  destruct pt as (l, lps).
  injection Hkps; clear Hkps; intros; subst l lps; reflexivity.

  eapply IHpts; eassumption.
Qed.

Lemma min_sl_pt_in_newt_segm : ∀ j jps k kps β γ pt pts ms segkx lch n,
  LocallySorted fst_lt [(j, jps); pt … pts]
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → minimise_slope α (j, jps) pt pts = ms
        → next_ch_points α n [end_pt ms … rem_pts ms] =
            [(k, kps, segkx) … lch]
          → ∀ i ips, (i, ips) ∈ seg ms
            → valuation α ips + Qnat i * γ == β.
Proof.
intros j jps k kps β γ pt pts ms segkx lch n.
intros Hsort Hβ Hγ Hms Hnp i ips Hips.
revert pt ms lch n i ips Hsort Hips Hms Hnp.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 subst ms; simpl in Hnp, Hips.
 contradiction.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 destruct c; subst ms; simpl in Hnp, Hips; [ idtac | contradiction | idtac ].
  symmetry in Heqms₁.
  symmetry in Heqc.
  apply Qeq_alt in Heqc.
  remember Hnp as Hnp₁; clear HeqHnp₁.
  apply next_ch_points_hd in Hnp.
  symmetry in Hnp.
  remember Heqms₁ as Hms; clear HeqHms.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  rewrite <- Heqc in Heqms₁.
  destruct Hips as [Hips| Hips].
   subst pt.
   subst β.
   unfold slope_expr in Heqms₁; simpl in Heqms₁.
   remember (valuation α kps) as v₃.
   subst γ.
   do 2 rewrite Qdiv_minus_distr_r in Heqms₁.
   rewrite Qdiv_minus_distr_r.
   apply Qeq_opp_r in Heqms₁.
   do 2 rewrite Qopp_minus in Heqms₁.
   rewrite <- Heqms₁.
   unfold Qnat.
   rewrite Nat2Z.inj_sub.
    rewrite QZ_minus.
    field.
    unfold Qminus, Qplus; simpl.
    do 2 rewrite Z.mul_1_r.
    unfold Qeq; simpl.
    rewrite Z.mul_1_r, Z.add_opp_r.
    intros H.
    apply Zminus_eq, Nat2Z.inj in H.
    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
    subst i.
    apply lt_irrefl in Hlt; contradiction.

    apply lt_le_weak.
    apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.

   eapply IHpts; try eassumption.
   apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
   apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
   constructor; [ assumption | eapply lt_trans; eassumption ].

  symmetry in Heqms₁.
  eapply IHpts; try eassumption.
  apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
  constructor; [ assumption | eapply lt_trans; eassumption ].
Qed.

Lemma in_newt_segm : ∀ j jps k kps γ β pts segjk segkx lch,
  LocallySorted fst_lt pts
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → lower_convex_hull_points α pts =
          [((j, jps), segjk); ((k, kps), segkx) … lch]
        → ∀ i ips, (i, ips) ∈ segjk
          → valuation α ips + Qnat i * γ == β.
Proof.
intros j jps k kps γ β pts segjk segkx lch.
intros Hsort Hβ Hγ Hch i ips Hips.
unfold lower_convex_hull_points in Hch.
remember (length pts) as n; clear Heqn.
rename Hch into Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros; subst pt₁.
rename H0 into Hjk.
remember (minimise_slope α (j, jps) pt₂ pts) as ms.
subst segjk.
symmetry in Heqms.
eapply min_sl_pt_in_newt_segm; eassumption.
Qed.

Lemma points_in_newton_segment : ∀ pol γ β j jps k kps seg,
  gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
  → ∀ h hps, (h, hps) ∈ [(j, jps); (k, kps) … seg]
    → valuation α hps + Qnat h * γ == β.
Proof.
intros pol γ β j jps k kps seg Hgb i ips Hips.
unfold gamma_beta in Hgb.
unfold gamma_beta_gen in Hgb.
remember (points_of_ps_polynom_gen α fld 0 (al pol) (an pol)) as pts.
rename Heqpts into Hpts.
remember (lower_convex_hull_points α pts) as lch.
destruct lch as [| ((l, lps), seg₁)]; [ discriminate Hgb | idtac ].
destruct lch as [| ((m, mps), seg₂)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros; subst l lps m mps seg₁.
rename H4 into Hβ.
rename H5 into Hγ.
rewrite Hγ in Hβ.
symmetry in Hβ, Hγ.
destruct Hips as [Hips| Hips].
 injection Hips; clear Hips; intros; subst i ips.
 rewrite Hβ; reflexivity.

 destruct Hips as [Hips| Hips].
  injection Hips; clear Hips; intros; subst i ips.
  rewrite Hβ, Hγ.
  unfold Qnat.
  apply points_of_polyn_sorted in Hpts.
  symmetry in Heqlch.
  eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
  apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
  unfold fst_fst_lt in Hlt₁; simpl in Hlt₁.
  rewrite Nat2Z.inj_sub; [ idtac | apply lt_le_weak; assumption ].
  rewrite QZ_minus.
  field.
  unfold Qminus, Qplus; simpl.
  do 2 rewrite Z.mul_1_r.
  unfold Qeq; simpl.
  rewrite Z.mul_1_r, Z.add_opp_r.
  intros H.
  apply Zminus_eq, Nat2Z.inj in H.
  subst k; apply lt_irrefl in Hlt₁; contradiction.

  apply points_of_polyn_sorted in Hpts.
  symmetry in Heqlch.
  eapply in_newt_segm in Heqlch; eassumption.
Qed.

Lemma rev_app_le_val : ∀ β γ i ips rl l lch,
  (∀ m mps, (m, mps) ∈ lch → β <= valuation α mps + Qnat m * γ)
  → List.rev rl ++ [(i, ips) … l] = lch
    →  β <= valuation α ips + Qnat i * γ.
Proof.
intros β γ i ips rl l lch Hle Hrl.
revert i ips l lch Hle Hrl.
induction rl as [| (m, mps)]; intros.
 simpl in Hrl.
 apply Hle.
 rewrite <- Hrl.
 left; reflexivity.

 simpl in Hrl.
 rewrite <- List.app_assoc in Hrl.
 simpl in Hrl.
 remember (List.rev rl ++ [(i, ips); (m, mps) … l]) as lch₁.
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

Lemma ad_hoc_lt_lt : ∀ i j k x y z,
  (i < j ∧ i < k)%nat
  → (y - x) / Qnat (k - i) < (z - x) / Qnat (j - i)
    → x + Qnat i * ((x - y) / Qnat (k - i)) <
      z + Qnat j * ((x - y) / Qnat (k - i)).
Proof.
intros i j k x y z (Hij, Hjk) H.
rewrite Qnat_minus_distr in H; [ idtac | apply lt_le_weak; assumption ].
rewrite Qnat_minus_distr in H; [ idtac | apply lt_le_weak; assumption ].
apply Qlt_shift_mult_r in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
rewrite Qmult_comm, Qmult_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Qlt_minus, Qnat_lt; assumption ].
rewrite Qmult_comm in H.
do 2 rewrite Qmult_minus_distr_l in H.
do 4 rewrite Qmult_minus_distr_r in H.
do 2 rewrite Qminus_minus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qminus_lt_lt_plus_r in H.
do 2 rewrite <- Qplus_assoc in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
rewrite <- Qplus_minus_swap in H.
apply Qlt_minus_plus_lt_r in H.
do 2 rewrite Qplus_assoc in H.
do 2 rewrite Qmult_div_assoc.
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qnat_lt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Qnat_lt_0_lt; assumption | idtac ].
rewrite Qnat_minus_distr; [ idtac | apply lt_le_weak; assumption ].
rewrite Qplus_comm, Qmult_comm; apply Qnot_le_lt.
rewrite Qplus_comm, Qmult_comm; apply Qlt_not_le.
do 2 rewrite Qmult_minus_distr_l.
do 2 rewrite Qmult_minus_distr_r.
do 2 rewrite Qplus_minus_assoc.
apply Qlt_plus_minus_lt_r; rewrite <- Qplus_minus_swap.
apply Qlt_plus_minus_lt_r; rewrite Qplus_minus_swap.
do 2 rewrite <- Qplus_assoc; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; rewrite <- Qplus_minus_swap.
apply Qplus_lt_lt_minus_r; do 2 rewrite Qplus_assoc.
rewrite Qplus_comm, Qplus_assoc, Qplus_assoc; apply Qnot_le_lt.
rewrite <- Qplus_assoc, <- Qplus_assoc, Qplus_comm, Qplus_assoc.
rewrite Qplus_plus_swap; apply Qlt_not_le.
assumption.
Qed.

Definition pt_of_ch α
    (item : (nat * puiseux_series α) * list (nat * puiseux_series α)) :=
  fst item.

Lemma minimised_slope_le : ∀ j jps h hps pts ms,
  minimise_slope α (j, jps) (h, hps) pts = ms
  → slope ms <= slope_expr α (j, jps) (h, hps).
Proof.
intros j jps h hps pts ms Hms.
revert ms Hms.
induction pts as [| pt]; intros.
 simpl in Hms.
 subst ms; simpl.
 apply Qle_refl.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt pts) as ms₁.
 remember (slope_expr α (j, jps) (h, hps) ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl.
  symmetry in Heqc; apply Qeq_alt in Heqc.
  rewrite Heqc; apply Qle_refl.

  simpl.
  apply Qle_refl.

  symmetry in Heqc; apply Qgt_alt in Heqc.
  apply Qlt_le_weak; eassumption.
Qed.

Lemma minimise_slope_pts_le : ∀ j jps pt pts ms,
  minimise_slope α (j, jps) pt pts = ms
  → ∀ h hps,
     (h, hps) ∈ pts
     → slope ms <= slope_expr α (j, jps) (h, hps).
Proof.
intros j jps pt pts ms Hms h hps Hhps.
revert pt ms Hms h hps Hhps.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 simpl in Hms.
 remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl.
  eapply minimised_slope_le; eassumption.

  simpl.
  eapply minimised_slope_le in Heqms₁.
  symmetry in Heqc; apply Qlt_alt in Heqc.
  apply Qlt_le_weak.
  eapply Qlt_le_trans; eassumption.

  eapply minimised_slope_le in Heqms₁.
  assumption.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 symmetry in Heqc.
 destruct c; subst ms.
  simpl.
  eapply IHpts; eassumption.

  simpl.
  apply Qlt_alt in Heqc.
  apply Qlt_le_weak.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply IHpts; eassumption.

  eapply IHpts; eassumption.
Qed.

Lemma min_slope_lt_betw_j_and_k_not_in_seg : ∀ j jps k kps pt pts ms,
  LocallySorted fst_lt pts
  → minimise_slope α (j, jps) pt pts = ms
    → end_pt ms = (k, kps)
      → ∀ h hps, (h, hps) ∈ [pt … pts] ∧ (h, hps) ∉ [(k, kps) … seg ms]
        → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms Hsort Hms Hep h hps (Hhps, Hnhps).
revert pt ms h Hms Hep Hhps Hnhps.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 subst ms.
 simpl in Hep, Hnhps |- *.
 subst pt.
 contradiction.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 symmetry in Heqc.
 destruct c; subst ms.
  simpl in Hep, Hnhps |- *.
  eapply IHpts; try eassumption.
   eapply LocallySorted_inv_1; eassumption.

   destruct Hhps as [Hhps| Hhps].
    subst pt.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, H).
    apply Decidable.not_or in H.
    destruct H as (H); exfalso; apply H; reflexivity.

    assumption.

   intros H; apply Hnhps; clear Hnhps.
   destruct H as [H| H].
    left; assumption.

    right; right; assumption.

  simpl in Hep, Hnhps |- *.
  subst pt.
  apply Qlt_alt in Heqc.
  apply Decidable.not_or in Hnhps.
  destruct Hnhps as (H, _).
  destruct Hhps as [Hhps| Hhps]; [ contradiction | idtac ].
  destruct Hhps as [Hhps| Hhps].
   subst pt₁.
   apply minimised_slope_le in Heqms₁.
   eapply Qlt_le_trans; eassumption.

   eapply Qlt_le_trans; [ eassumption | idtac ].
   eapply minimise_slope_pts_le; eassumption.

  destruct Hhps as [Hhps| Hhps].
   subst pt.
   apply Qgt_alt in Heqc.
   assumption.

   eapply IHpts; try eassumption.
   eapply LocallySorted_inv_1; eassumption.
Qed.

Lemma min_slope_lt_after_k : ∀ j jps k kps pt pts ms,
  LocallySorted fst_lt pts
  → minimise_slope α (j, jps) pt pts = ms
    → end_pt ms = (k, kps)
      → ∀ h hps, (h, hps) ∈ pts
        → (k < h)%nat
          → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms Hsort Hms Hep h hps Hhps Hkh.
revert pt ms Hms Hep h Hhps Hkh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 remember Hms as H; clear HeqH.
 apply min_sl_in in Hms.
 rewrite Hep in Hms.
 destruct Hms as [Hms| Hms].
  subst pt.
  simpl in H.
  remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α (j, jps) (k, kps) ?= slope ms₁) as c.
  destruct c; subst ms.
   simpl in Hep |- *.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁.
   apply le_not_lt in Heqms₁; contradiction.

   simpl in Hep |- *; clear Hep.
   symmetry in Heqc; apply Qlt_alt in Heqc.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   eapply minimised_slope_le; eassumption.

   symmetry in Heqc; apply Qgt_alt in Heqc.
   apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
   rewrite Hep in Heqms₁; simpl in Heqms₁.
   apply le_not_lt in Heqms₁.
   contradiction.

  destruct Hms as [Hms| Hms].
   injection Hms; clear Hms; intros; subst h hps.
   apply lt_irrefl in Hkh; contradiction.

   eapply LocallySorted_hd in Hsort; [ idtac | eassumption ].
   simpl in Hsort.
   eapply lt_trans in Hsort; [ idtac | eassumption ].
   apply lt_irrefl in Hsort; contradiction.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl in Hep |- *.
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.

  simpl in Hep |- *.
  subst pt.
  symmetry in Heqc; apply Qlt_alt in Heqc.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimise_slope_pts_le; eassumption.

  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.
Qed.

Lemma pt_aft_k : ∀ n pts j jps k kps seg seg₂ lch γ β,
  LocallySorted fst_lt pts
  → (j < k)%nat
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → next_ch_points α n pts = [(j, jps, seg); (k, kps, seg₂) … lch]
          → ∀ h hps, (k < h)%nat
            → (h, hps) ∈ pts
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx lch γ β.
intros Hsort Hjk Hγ Hβ Hnp h hps Hkh Hhps.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hhps as [Hhps| Hhps].
 injection Hhps; clear Hhps; intros; subst h hps.
(**)
 eapply lt_trans in Hkh; [ idtac | eassumption ].
 apply lt_irrefl in Hkh; contradiction.

 destruct Hhps as [Hhps| Hhps]; [ exfalso | idtac ].
  subst pt₁.
  symmetry in Heqms₁.
  apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
  rewrite Hep₁ in Heqms₁.
  apply le_not_lt in Heqms₁.
  contradiction.

  symmetry in Heqms₁.
  symmetry in Hep₁.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in H; [ idtac | eassumption ].
  symmetry in Hep₁.
  eapply min_slope_lt_after_k in Heqms₁; try eassumption.
   rewrite H in Heqms₁.
   subst β γ.
   apply ad_hoc_lt_lt; [ idtac | assumption ].
   split; [ idtac | assumption ].
   destruct pt₁ as (l, lps).
   apply lt_trans with (m := l).
    apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.

    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
    eapply LocallySorted_hd in Hsort; [ idtac | eassumption ].
    assumption.

   apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   destruct pts as [| pt₂]; [ constructor | idtac ].
   apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.
Qed.

Lemma points_after_k : ∀ pol pts γ β j jps k kps seg,
  pts = points_of_ps_polynom α fld pol
  → gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
    → ∀ h hps, (h, hps) ∈ pts
      → (k < h)%nat
        → β < valuation α hps + Qnat h * γ.
Proof.
intros pol pts γ β j jps k kps segjk Hpts Hgb h hps Hhps Hki.
unfold gamma_beta in Hgb.
unfold gamma_beta_gen in Hgb.
unfold points_of_ps_polynom in Hpts.
rewrite <- Hpts in Hgb.
remember (lower_convex_hull_points α pts) as lch.
destruct lch as [| ((l, lps), seglx)]; [ discriminate Hgb | idtac ].
destruct lch as [| ((m, mps), segmx)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros; subst l lps m mps seglx.
symmetry in H4; rename H4 into Hβ.
symmetry in H5; rename H5 into Hγ.
rewrite <- Hγ in Hβ.
symmetry in Heqlch.
apply points_of_polyn_sorted in Hpts.
remember Hpts as Hpts₂; clear HeqHpts₂.
eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt, Hpts).
unfold fst_fst_lt in Hlt; simpl in Hlt.

eapply pt_aft_k; eassumption.
Qed.

Lemma not_seg_min_sl_lt : ∀ j jps k kps pt pts ms h hps,
  LocallySorted fst_lt [(j, jps); pt; (h, hps) … pts]
  → minimise_slope α (j, jps) pt [(h, hps) … pts] = ms
    → j < h <  k
      → (h, hps) ∉ seg ms
        → end_pt ms = (k, kps)
          → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms h hps Hsort Hms (Hjh, Hhk) Hseg Hep.
revert ms Hms Hseg Hep.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 remember (slope_expr α (j, jps) pt ?= slope_expr α (j, jps) (h, hps)) as c.
 symmetry in Heqc.
 destruct c; subst ms; simpl.
  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h hps.
  apply lt_irrefl in Hhk; contradiction.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc.
  assumption.

  simpl in Hseg, Hep.
  injection Hep; clear Hep; intros; subst h hps.
  apply lt_irrefl in Hhk; contradiction.

 remember [pt₁ … pts] as pts₁.
 simpl in Hms.
 remember (minimise_slope α (j, jps) (h, hps) pts₁) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c₁.
 symmetry in Heqc₁.
 destruct c₁; subst ms; simpl.
  simpl in Hseg, Hep.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hne, Hseg).
  subst pts₁.
  simpl in Heqms₁.
  remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl.
   simpl in Heqc₁, Hseg, Hep.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hne₂, Hseg).
   exfalso; apply Hne₂; reflexivity.

   simpl in Heqc₁, Hseg, Hep.
   injection Hep; clear Hep; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   apply Qgt_alt in Heqc; assumption.

  simpl in Hseg, Hep.
  subst pt.
  apply Qlt_alt in Heqc₁.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  eapply minimised_slope_le; eassumption.
bbb.
  eapply IHpts; try eassumption.
   subst pts₁.
   apply LocallySorted_inv_2 in Hsort.
   destruct Hsort as (Hlt₁, Hsort).
   apply LocallySorted_inv_2 in Hsort.
   destruct Hsort as (Hlt₂, Hsort).
   apply LocallySorted_inv_2 in Hsort.
   destruct Hsort as (Hlt₃, Hsort).
   constructor; [ idtac | assumption ].
   constructor; [ idtac | assumption ].
   destruct pts as [| pt₂]; [ constructor | idtac ].
   constructor.
    eapply LocallySorted_inv_1; eassumption.

    eapply LocallySorted_inv_2 in Hsort.
    destruct Hsort as (Hlt₄, Hsort).
    eapply lt_trans; eassumption.

   subst pts₁.
   simpl in Heqms₁.
   remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
   symmetry in Heqc.
   remember [(h, hps) … pts] as pts₁.
   destruct c; subst ms₁; simpl.
    simpl in Heqc₁, Hseg, Hep.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (Hne₂, Hseg).
    exfalso; apply Hne₂; reflexivity.

    simpl in Heqc₁, Hseg, Hep.
    injection Hep; clear Hep; intros; subst h hps.
    apply lt_irrefl in Hhk; contradiction.

bbb.

(*
Lemma not_seg_min_sl_lt : ∀ j jps k kps pt pts ms,
  LocallySorted fst_lt pts
  → minimise_slope α (j, jps) pt pts = ms
    → pt ∉ seg ms
      → end_pt ms = (k, kps)
        → ∀ h hps, (h, hps) ∈ pts
          → (h, hps) ∉ seg ms
            → slope ms < slope_expr α (j, jps) (h, hps).
Proof.
intros j jps k kps pt pts ms Hsort Hms Hpt Hep h hps Hhps Hseg.
revert h pt ms Hms Hep Hseg Hhps Hpt.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 remember Hms as H; clear HeqH.
 apply min_sl_in in Hms.
 rewrite Hep in Hms.
 destruct Hms as [Hms| Hms].
  subst pt.
  simpl in H.
  remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α (j, jps) (k, kps) ?= slope ms₁) as c.
  symmetry in Heqc.
  destruct c; subst ms.
   simpl in Hep, Hseg |- *.
   apply Decidable.not_or in Hseg.
   destruct Hseg as (Hkh, Hseg).
   eapply min_slope_lt_betw_j_and_k_not_in_seg in Heqms₁; try eassumption.
    eapply LocallySorted_inv_1; eassumption.

    split; [ left; reflexivity | intros H; destruct H; contradiction ].

   simpl in Hep, Hseg |- *.
   apply Qlt_alt in Heqc.
   clear Hep Hseg.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   eapply minimised_slope_le; eassumption.

   apply Qgt_alt in Heqc.
   symmetry in Hep.
   eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
   rewrite Heqms₁ in Heqc.
   apply Qlt_irrefl in Heqc; contradiction.

  simpl in H.
  remember (minimise_slope α (j, jps) (h, hps) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
  symmetry in Heqc.
  destruct c; subst ms.
   simpl in Hep, Hseg, Hpt |- *.
   apply Decidable.not_or in Hpt.
   destruct Hpt as (H); exfalso; apply H; reflexivity.

   simpl in Hep, Hseg, Hpt |- *.
   subst pt.
   apply Qlt_alt in Heqc.
   destruct Hms as [Hms| Hms].
    injection Hms; clear Hms; intros; subst h hps.
    apply minimised_slope_le in Heqms₁.
    eapply Qle_lt_trans in Heqms₁; [ idtac | eassumption ].
    apply Qlt_irrefl in Heqms₁; contradiction.

    apply minimised_slope_le in Heqms₁.
    eapply Qlt_le_trans; eassumption.

   apply Qgt_alt in Heqc.
   destruct Hms as [Hms| Hms].
    injection Hms; clear Hms; intros; subst h hps.
-- blocked --
bbb.
*)

Lemma pt_betw_j_and_k : ∀ n pts j jps k kps segjk segkx lch γ β,
  LocallySorted fst_lt pts
  → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
    → β = valuation α jps + Qnat j * γ
      → next_ch_points α n pts = [(j, jps, segjk); (k, kps, segkx) … lch]
        → ∀ h hps, (j < h < k)%nat
          → (h, hps) ∈ pts
            → (h, hps) ∉ segjk
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx lch γ β.
intros Hsort Hγ Hβ Hnp h hps (Hjh, Hhk) Hhps Hseg.
destruct n; [ discriminate Hnp | idtac ].
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros; subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename H into Hep₁.
rewrite Hep₁ in Hnp.
destruct Hhps as [Hhps| Hhps].
 injection Hhps; clear Hhps; intros; subst h hps.
 apply lt_irrefl in Hjh; contradiction.

 destruct Hhps as [Hhps| Hhps].
  subst pt₁.
  symmetry in Heqms₁.
  destruct pts as [| pt₁].
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   injection Hep₁; clear Hep₁; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   simpl in Heqms₁.
   remember (minimise_slope α (j, jps) pt₁ pts) as ms₂.
   symmetry in Heqms₂.
   remember (slope_expr α (j, jps) (h, hps) ?= slope ms₂) as c.
   destruct c; subst ms₁.
    simpl in Hep₁, Hseg, Hnp.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (H); exfalso; apply H; reflexivity.

    simpl in Hep₁, Hseg, Hnp.
    injection Hep₁; clear Hep₁; intros; subst h hps.
    apply lt_irrefl in Hhk; contradiction.

    symmetry in Hep₁.
    remember Heqms₂ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Heqc; apply Qgt_alt in Heqc.
    rewrite H in Heqc.
    subst β γ.
    apply ad_hoc_lt_lt; [ idtac | assumption ].
    split; [ assumption | idtac ].
    eapply lt_trans; eassumption.

  symmetry in Heqms₁.
  revert pt₁ ms₁ Hsort Heqms₁ Hep₁ Hseg Hnp.
  induction pts as [| pt₂]; intros.
   simpl in Heqms₁.
   subst ms₁.
   simpl in Hep₁, Hseg, Hnp.
   contradiction.

   destruct Hhps as [Hhps| Hhps].
    subst pt₂.
    symmetry in Hep₁.
    remember Heqms₁ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Hep₁.
    eapply not_seg_min_sl_lt in Heqms₁; try eassumption.
     rewrite H in Heqms₁.
     subst β γ.
     apply ad_hoc_lt_lt; [ idtac | assumption ].
     split; [ assumption | idtac ].
     eapply lt_trans; eassumption.

     split; assumption.

    simpl in Heqms₁.
    remember (minimise_slope α (j, jps) pt₂ pts) as ms₂.
    symmetry in Heqms₂.
    remember (slope_expr α (j, jps) pt₁ ?= slope ms₂) as c.
    symmetry in Heqc.
    destruct c; subst ms₁.
     simpl in Hep₁, Hseg, Hnp.
     apply Decidable.not_or in Hseg.
     destruct Hseg as (Hlt₁, Hseg).
     eapply IHpts; try eassumption.
     constructor.
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort; assumption.

      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort; eapply lt_trans; eassumption.

     simpl in Hep₁, Hseg, Hnp.
     subst pt₁.
     apply LocallySorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₂, Hsort).
     apply LocallySorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₃, Hsort).
     eapply LocallySorted_hd in Hsort; [ idtac | eassumption ].
     unfold fst_lt in Hlt₃.
     simpl in Hlt₃, Hsort.
     clear Hlt₂.
     eapply lt_trans in Hlt₃; [ idtac | eassumption ].
     eapply lt_trans in Hlt₃; [ idtac | eassumption ].
     apply lt_irrefl in Hlt₃; contradiction.

     eapply IHpts; try eassumption.
     constructor.
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort; assumption.

      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort as (Hlt₂, Hsort).
      apply LocallySorted_inv_2 in Hsort.
      destruct Hsort; eapply lt_trans; eassumption.
Qed.

Lemma points_between_j_and_k : ∀ pol pts γ β j jps k kps seg,
  pts = points_of_ps_polynom α fld pol
  → gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
    → ∀ h hps, (h, hps) ∈ pts
      → (j < h < k)%nat
        → (h, hps) ∉ seg
          → β < valuation α hps + Qnat h * γ.
Proof.
intros pol pts γ β j jps k kps segjk Hpts Hgb h hps Hhps (Hjh, Hhk) Hseg.
unfold gamma_beta in Hgb.
unfold gamma_beta_gen in Hgb.
unfold points_of_ps_polynom in Hpts.
rewrite <- Hpts in Hgb.
remember (lower_convex_hull_points α pts) as lch.
destruct lch as [| ((l, lps), seglx)]; [ discriminate Hgb | idtac ].
destruct lch as [| ((m, mps), segmx)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros; subst l lps m mps seglx.
symmetry in H4; rename H4 into Hβ.
symmetry in H5; rename H5 into Hγ.
rewrite <- Hγ in Hβ.
symmetry in Heqlch.
apply points_of_polyn_sorted in Hpts.
remember Hpts as Hpts₂; clear HeqHpts₂.
eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt, Hpts).
unfold fst_fst_lt in Hlt; simpl in Hlt.

eapply pt_betw_j_and_k; try eassumption.
split; assumption.
Qed.

(*
unfold lower_convex_hull_points in Heqlch.
remember (length pts) as n; clear Heqn.
rename Heqlch into Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros; subst pt₁.
remember (minimise_slope α (j, jps) pt₂ pts) as ms₁.
symmetry in Heqms₁.
subst segjk.
remember H as Hnp; clear HeqHnp.
apply next_ch_points_hd in H.
rename pt₂ into pt.
rename ms₁ into ms.
apply LocallySorted_inv_2 in Hpts₂.
destruct Hpts₂ as (Hlt₁, Hsort).
unfold fst_lt in Hlt₁; simpl in Hlt₁.
bbb.
revert ms pt Heqms₁ H Hseg Hnp Hhps Hlt₁ Hsort.
induction pts as [| pt₁]; intros.
 simpl in Heqms₁.
 subst ms.
 simpl in H, Hseg, Hnp.
 clear Hseg.
 subst pt.
 clear Hsort.
 simpl in Hhps.
 destruct Hhps as [H| Hhps].
  injection H; clear H; intros; subst h hps.
  apply lt_irrefl in Hjh; contradiction.

  simpl in Hlt₁.
  destruct Hhps as [H| Hhps].
   injection H; clear H; intros; subst h hps.
   apply lt_irrefl in Hhk; contradiction.

   contradiction.

 simpl in Heqms₁.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 symmetry in Heqms₁.
 remember (slope_expr α (j, jps) pt ?= slope ms₁) as c.
 destruct c; subst ms.
  simpl in H, Hseg, Hnp, IHpts.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hpt, Hseg).
  symmetry in Heqc; apply Qeq_alt in Heqc.
  symmetry in Heqms₁0.
  eapply IHpts; try eassumption.
   simpl in Hhps.
   destruct Hhps as [HH| Hhps].
    left; assumption.

    destruct Hhps as [HH| Hhps].
     contradiction.

     destruct Hhps as [HH| Hhps].
      right; left; assumption.

      right; right; assumption.

   eapply lt_trans; [ eassumption | idtac ].
   apply LocallySorted_inv_2 in Hsort.
   destruct Hsort; assumption.

   apply LocallySorted_inv_2 in Hsort.
   destruct Hsort; assumption.

  simpl in H, Hseg, Hnp.
  subst pt.
  simpl in Hhps.
  destruct Hhps as [HH| Hhps].
   injection HH; clear HH; intros; subst h hps.
   apply lt_irrefl in Hjh; contradiction.

   destruct Hhps as [HH| Hhps].
    injection HH; clear HH; intros; subst h hps.
    apply lt_irrefl in Hhk; contradiction.

    destruct Hhps as [HH| Hhps].
     subst pt₁.
     apply LocallySorted_inv_2 in Hsort.
     destruct Hsort as (Hlt₂, Hsort).
     unfold fst_lt in Hlt₂; simpl in Hlt₂.
     eapply lt_trans in Hlt₂; [ idtac | eapply Hhk ].
     apply lt_irrefl in Hlt₂; contradiction.

     symmetry in Heqc; apply Qlt_alt in Heqc.
     symmetry in Heqms₁0.
     remember Heqms₁0 as H; clear HeqH.
     clear Hlt₁.
bbb.
*)

Lemma sorted_hd_not_in_tl : ∀ k (jps : puiseux_series α) kps pts,
  LocallySorted fst_lt [(k, jps) … pts] → (k, kps) ∉ pts.
Proof.
intros k jps kps pts H.
induction pts as [| (h, hps)]; [ intros HH; contradiction | idtac ].
intros HH.
destruct HH as [HH| HH].
 injection HH; clear HH; intros; subst h hps.
 apply LocallySorted_inv_2 in H; destruct H as (Hlt, H).
 apply lt_irrefl in Hlt; assumption.

 revert HH; apply IHpts.
 apply LocallySorted_inv_2 in H; destruct H as (Hlt₁, H).
 destruct pts as [| pt₂]; [ constructor | idtac ].
 apply LocallySorted_inv_2 in H; destruct H as (Hlt₂, H).
 constructor; [ assumption | idtac ].
 eapply lt_trans; eassumption.
Qed.

Lemma same_k_same_kps : ∀ pol pts j jps k kps,
  pts = points_of_ps_polynom α fld pol
  → (j, jps) ∈ pts
    → (k, kps) ∈ pts
      → j = k
        → jps = kps.
Proof.
intros pol pts j jps k kps Hpts Hjps Hkps Hjk.
unfold points_of_ps_polynom in Hpts.
apply points_of_polyn_sorted in Hpts.
subst j.
induction pts as [| pt]; intros; [ contradiction | idtac ].
destruct Hjps as [Hjps| Hjps]; [ subst pt | idtac ].
 destruct Hkps as [Hkps| Hkps].
  injection Hkps; clear; intros; subst jps; reflexivity.

  exfalso; revert Hkps; eapply sorted_hd_not_in_tl; eassumption.

 destruct Hkps as [Hkps| Hkps]; [ subst pt | idtac ].
  exfalso; revert Hjps; eapply sorted_hd_not_in_tl; eassumption.

  destruct pts as [| pt₂]; [ contradiction | idtac ].
  apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
  eapply IHpts; eassumption.
Qed.

Lemma k_in_pts : ∀ pts j jps k kps segjk segkx lch,
  lower_convex_hull_points α pts = [(j, jps, segjk); (k, kps, segkx) … lch]
  → (k, kps) ∈ pts.
Proof.
intros pts j jps k kps segjk segkx lch Hlch.
unfold lower_convex_hull_points in Hlch.
remember (length pts) as n; clear Heqn.
destruct n; [ discriminate Hlch | simpl in Hlch ].
destruct pts as [| (l, lps)]; [ discriminate Hlch | idtac ].
destruct pts as [| (m, mps)]; [ discriminate Hlch | idtac ].
injection Hlch; clear Hlch; intros; subst l lps.
remember (minimise_slope α (j, jps) (m, mps) pts) as ms₁.
symmetry in Heqms₁.
subst segjk.
apply min_sl_in in Heqms₁.
apply next_ch_points_hd in H.
rewrite H in Heqms₁.
right; assumption.
Qed.

Lemma gamma_beta_k_in_pts : ∀ pol pts j jps k kps β γ seg,
  pts = points_of_ps_polynom α fld pol
  → gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
    → (k, kps) ∈ pts.
Proof.
intros pol pts j jps k kps β γ seg Hpts Hgb.
unfold gamma_beta in Hgb.
unfold gamma_beta_gen in Hgb.
unfold points_of_ps_polynom in Hpts.
rewrite <- Hpts in Hgb.
remember (lower_convex_hull_points α pts) as lch.
destruct lch as [| ((l, lps), seglx)]; [ discriminate Hgb | idtac ].
destruct lch as [| ((m, mps), segmx)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros; subst γ β l lps m mps seglx.
symmetry in Heqlch.
eapply k_in_pts; eassumption.
Qed.

Lemma points_not_in_newton_segment : ∀ pol pts γ β j jps k kps seg,
  pts = points_of_ps_polynom α fld pol
  → gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
    → ∀ h hps, (h, hps) ∈ pts
      → (h, hps) ∉ [(j, jps); (k, kps) … seg]
        → β < valuation α hps + Qnat h * γ.
Proof.
intros pol pts γ β j jps k kps seg.
intros Hpts Hgb h hps Hhps Hnhps.
destruct (lt_dec k h) as [Hlt| Hge].
 eapply points_after_k; eassumption.

 apply not_gt in Hge.
 destruct (eq_nat_dec h k) as [Heq| Hne].
  eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
   subst h hps.
   simpl in Hnhps.
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (_, Hnhps).
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (Hnhps, _).
   exfalso; apply Hnhps; reflexivity.

   eapply gamma_beta_k_in_pts; eassumption.

  apply le_neq_lt in Hge; [ idtac | assumption ].
  destruct (lt_dec j h) as [Hlt| Hge₂].
   eapply points_between_j_and_k; try eassumption.
    split; assumption.

    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    assumption.

   apply not_gt in Hge₂.
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
         Qeq_bool₁ β βi)
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
       if eq k r then sol_list
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
