(* $Id: Puiseux.v,v 1.215 2013-04-20 10:45:13 deraugla Exp $ *)

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
  | [((j, jps), seg), ((k, kps), _) … _] =>
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

Lemma one_vp_gen : ∀ α fld pow cl cn,
  cn ≠ zero fld → points_of_ps_polynom_gen α fld pow cl cn ≠ [].
Proof.
intros α fld pow cl cn Hcn.
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

Lemma lower_convex_points_empty_iff : ∀ α dpl,
  lower_convex_hull_points α dpl = [ ] ↔ dpl = [].
Proof.
intros α dpl.
unfold lower_convex_hull_points.
split; intros H; [ idtac | subst dpl; reflexivity ].
destruct dpl as [| dp₁ dpl₁]; [ reflexivity | simpl in H ].
destruct dpl₁; discriminate H.
Qed.

Lemma vp_pow_lt : ∀ α fld pow cl cn d₁ p₁ dpl,
  points_of_ps_polynom_gen α fld (S pow) cl cn = dpl
  → (d₁, p₁) ∈ dpl
    → (pow < d₁)%nat.
Proof.
intros α fld pow cl cn d₁ p₁ dpl Hvp Hdp.
revert fld pow cn d₁ p₁ dpl Hvp Hdp.
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

Lemma vp_lt : ∀ α fld pow cl cn d₁ p₁ d₂ p₂ dpl,
  points_of_ps_polynom_gen α fld pow cl cn = [(d₁, p₁) … dpl]
  → (d₂, p₂) ∈ dpl
    → (d₁ < d₂)%nat.
Proof.
intros α fld pow cl cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
revert fld pow cn d₁ p₁ d₂ p₂ dpl Hvp Hdp.
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

Lemma gamma_beta_not_empty : ∀ α fld (pol : polynomial (puiseux_series α)),
  an pol ≠ zero fld
  → (∃ c, c ∈ al pol ∧ c ≠ zero fld)
    → gamma_beta fld pol ≠ None.
Proof.
intros α fld pol an_nz ai_nz.
unfold gamma_beta.
apply gb_gen_not_empty; assumption.
Qed.

Lemma Qlt_minus : ∀ x y, x < y → 0 < y - x.
Proof.
intros x y H.
unfold Qlt in H |-*; simpl.
rewrite Z.mul_1_r, <- Zopp_mult_distr_l.
apply Zlt_left_lt.
assumption.
Qed.

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

Definition fst_lt {α} (x y : nat * α) :=
  (fst x < fst y)%nat.
Definition fst_fst_lt {α β} (x y : (nat * α) * β) :=
  (fst (fst x) < fst (fst y))%nat.

Lemma points_of_polyn_sorted : ∀ α fld deg cl cn pts,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → LocallySorted fst_lt pts.
Proof.
intros α fld deg cl cn pts Hpts.
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
    inversion Hpts; [ constructor | idtac ].
    subst a pts.
    constructor; [ inversion Hpts; assumption | idtac ].
    simpl in H2 |- *.
    eapply lt_trans; [ apply lt_n_Sn | eassumption ].

    subst pts.
    constructor; [ eapply IHcl; reflexivity | apply lt_n_Sn ].
Qed.

Lemma minimise_slope_le : ∀ α pt₁ pt₂ pts₂ ms,
  LocallySorted fst_lt [pt₂ … pts₂]
  → minimise_slope α pt₁ pt₂ pts₂ = ms
    → fst pt₂ ≤ fst (end_pt ms).
Proof.
intros α pt₁ pt₂ pts₂ ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts₂ as [| pt]; intros.
 subst ms; apply le_n.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt pts₂) as ms₁.
 remember (Qle_bool (slope ms₁) (slope_expr α pt₁ pt₂)) as b.
 destruct b.
  subst ms; simpl.
  apply lt_le_weak.
  inversion Hsort.
  eapply lt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.

  subst ms; reflexivity.
Qed.

Lemma min_sl_in : ∀ α pt₁ pt₂ pts₂ ms,
  minimise_slope α pt₁ pt₂ pts₂ = ms
  → end_pt ms ∈ [pt₂ … pts₂].
Proof.
intros α pt₁ pt₂ pts₂ ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts₂ as [| pt]; intros.
 subst ms; left; reflexivity.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt pts₂) as ms₁.
 remember (Qle_bool (slope ms₁) (slope_expr α pt₁ pt₂)) as b.
 destruct b; subst ms; simpl.
  symmetry in Heqms₁.
  apply IHpts₂ in Heqms₁.
  destruct Heqms₁.
   subst pt; right; left; reflexivity.

   right; right; assumption.

  left; reflexivity.
Qed.

Lemma in_rem_pts : ∀ α pt pt₁ pt₂ pts₂,
  pt ∈ rem_pts (minimise_slope α pt₁ pt₂ pts₂)
  → pt ∈ [pt₂ … pts₂].
Proof.
intros α pt pt₁ pt₂ pts₂ Hpt.
revert pt₁ pt₂ pt Hpt.
induction pts₂ as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hpt.
remember (minimise_slope α pt₁ pt₃ pts₂) as ms.
remember (Qle_bool (slope ms) (slope_expr α pt₁ pt₂)) as b.
destruct b; simpl in Hpt.
 subst ms.
 apply IHpts₂ in Hpt.
 right; assumption.

 right; assumption.
Qed.

Lemma np_in : ∀ α n pts lch,
  next_ch_points α n pts = lch
  → ∀ pt, pt ∈ List.map (λ ms, fst ms) lch
    → pt ∈ pts.
Proof.
intros α n pts lch Hnp pt Hpt.
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

Lemma next_ch_points_le : ∀ α n pt₁ pt₂ pts₁ sg lch,
  next_ch_points α n [pt₁ … pts₁] = [(pt₂, sg) … lch]
  → fst pt₁ ≤ fst pt₂.
Proof.
intros α n pt₁ pt₂ pts₁ sg lch Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts₁; injection Hnp; intros; subst pt₁; reflexivity.
Qed.

Lemma minimise_slope_sorted : ∀ α pt₁ pt₂ pts ms,
  LocallySorted fst_lt [pt₁, pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → LocallySorted fst_lt [end_pt ms … rem_pts ms].
Proof.
intros α pt₁ pt₂ pts ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros; [ subst ms; constructor | idtac ].
simpl in Hms.
remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
remember (Qle_bool (slope ms₁) (slope_expr α pt₁ pt₂)) as b.
destruct b.
 subst ms; simpl.
 symmetry in Heqms₁.
 eapply IHpts; [ idtac | eassumption ].
 constructor.
  inversion Hsort; inversion H1; assumption.

  inversion Hsort; inversion H1.
  eapply lt_trans; eassumption.

 subst ms; simpl.
 inversion Hsort; assumption.
Qed.

Lemma next_points_sorted : ∀ α n pts lch,
  LocallySorted fst_lt pts
  → next_ch_points α n pts = lch
    → LocallySorted fst_fst_lt lch.
Proof.
intros α n pts lch Hsort Hnp.
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
   inversion Hsort.
   eassumption.

   eapply le_trans; [ eassumption | idtac ].
   eapply next_ch_points_le; eassumption.

  inversion Hsort; assumption.

 symmetry in Heqms₂.
 eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lower_convex_hull_points_sorted : ∀ α pts lch,
  LocallySorted fst_lt pts
  → lower_convex_hull_points α pts = lch
    → LocallySorted fst_fst_lt lch.
Proof.
intros α pts lch Hsort Hch.
eapply next_points_sorted; eassumption.
Qed.

Lemma next_ch_points_hd : ∀ α n pt₁ pt₂ pts₁ seg lch,
  next_ch_points α n [pt₁ … pts₁] = [(pt₂, seg) … lch]
  → pt₁ = pt₂.
Proof.
intros α n pt₁ pt₂ pts₂ seg₂ lch Hnp.
revert pt₁ pt₂ pts₂ seg₂ lch Hnp.
induction n; intros; [ discriminate Hnp | simpl in Hnp ].
destruct pts₂; injection Hnp; intros; subst pt₂; reflexivity.
Qed.

Lemma minimised_slope : ∀ α j jps k kps pt pts ms,
  minimise_slope α (j, jps) pt pts = ms
  → (k, kps) = end_pt ms
    → slope ms == (valuation α kps - valuation α jps) / Qnat (k - j).
Proof.
intros α j jps k kps pt pts ms Hms Hkps.
revert j jps k kps pt ms Hms Hkps.
induction pts as [| pt₁]; intros.
 subst ms; simpl in Hkps |- *; subst pt; reflexivity.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 destruct pt as (l, lps); simpl in Hms.
 remember (Qle_bool (slope ms₁) (slope_expr α (j, jps) (l, lps))) as b.
 destruct b.
  subst ms; simpl in Hkps |- *.
  symmetry in Heqms₁.
  eapply IHpts; eassumption.

  subst ms; simpl in Hkps |- *.
  injection Hkps; clear Hkps; intros; subst l lps.
  reflexivity.
Qed.

Lemma Qeq_opp_r : ∀ x y, x == y → - x == - y.
Proof.
intros x y H; rewrite H; reflexivity.
Qed.

Lemma Qeq_opp_l : ∀ x y, - x == - y → x == y.
Proof.
intros x y H.
rewrite <- Qopp_opp, H.
apply Qopp_opp.
Qed.

Lemma Qdiv_add_distr_r : ∀ x y z, (x + y) / z == x / z + y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qdiv_sub_distr_r : ∀ x y z, (x - y) / z == x / z - y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qopp_minus : ∀ x y, - (x - y) == y - x.
Proof. intros; field. Qed.

Lemma min_sl_pt_in_newt_segm : ∀ α j jps k kps β γ pt pts ms segkx lch n,
  LocallySorted fst_lt [(j, jps), pt … pts]
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → minimise_slope α (j, jps) pt pts = ms
        → next_ch_points α n [end_pt ms … rem_pts ms] =
            [(k, kps, segkx) … lch]
          → ∀ i ips, (i, ips) ∈ seg ms
            → valuation α ips + Qnat i * γ == β.
Proof.
intros α j jps k kps β γ pt pts ms segkx lch n.
intros Hsort Hβ Hγ Hms Hnp i ips Hips.
revert pt ms lch n i ips Hsort Hips Hms Hnp.
induction pts as [| pt₁]; intros.
 simpl in Hms.
 subst ms; simpl in Hnp, Hips.
 contradiction.

 simpl in Hms.
 remember (minimise_slope α (j, jps) pt₁ pts) as ms₁.
 remember (Qle_bool (slope ms₁) (slope_expr α (j, jps) pt)) as b.
 destruct b; [ idtac | subst ms; contradiction ].
 subst ms; simpl in Hnp, Hips.
 remember (Qeq_bool (slope ms₁) (slope_expr α (j, jps) pt)) as b₁.
 symmetry in Heqms₁.
 destruct b₁.
  clear Heqb.
  symmetry in Heqb₁.
  apply Qeq_bool_iff in Heqb₁.
  remember Hnp as Hnp₁; clear HeqHnp₁.
  apply next_ch_points_hd in Hnp.
  symmetry in Hnp.
  remember Heqms₁ as Hms; clear HeqHms.
  eapply minimised_slope in Heqms₁; [ idtac | eassumption ].
  rewrite Heqb₁ in Heqms₁.
  destruct Hips as [Hips| Hips].
   subst pt.
   simpl in Heqb₁, Heqms₁.
   subst β.
   remember (valuation α kps) as v₃.
   subst γ.
   unfold slope_expr in Heqms₁; simpl in Heqms₁.
   do 2 rewrite Qdiv_sub_distr_r in Heqms₁.
   rewrite Qdiv_sub_distr_r.
   apply Qeq_opp_r in Heqms₁.
   rewrite Qopp_minus in Heqms₁.
   rewrite Qopp_minus in Heqms₁.
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
    inversion Hsort.
    subst i.
    apply lt_irrefl in H4; contradiction.

    apply lt_le_weak; inversion Hsort; assumption.

   eapply IHpts in Hips; try eassumption.
   constructor; [ inversion Hsort; inversion H1; assumption | idtac ].
   inversion Hsort; subst a b l.
   inversion H1; subst a b l.
   eapply lt_trans; eassumption.

  eapply IHpts; try eassumption.
  constructor; [ inversion Hsort; inversion H1; assumption | idtac ].
  inversion Hsort; subst a b l.
  inversion H1; subst a b l.
  eapply lt_trans; eassumption.
Qed.

Lemma in_newt_segm : ∀ α j jps k kps γ β pts segjk segkx lch,
  LocallySorted fst_lt pts
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → lower_convex_hull_points α pts =
          [((j, jps), segjk), ((k, kps), segkx) … lch]
        → ∀ i ips, (i, ips) ∈ segjk
          → valuation α ips + Qnat i * γ == β.
Proof.
intros α j jps k kps γ β pts segjk segkx lch.
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

Lemma points_in_newton_segment : ∀ α fld pol γ β j jps k kps seg,
  gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
  → ∀ i ips, (i, ips) ∈ [(j, jps), (k, kps) … seg]
    → valuation α ips + Qnat i * γ == β.
Proof.
intros α fld pol γ β j jps k kps seg Hgb i ips Hips.
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
  inversion Hpts.
  subst a b l.
  unfold fst_fst_lt in H3; simpl in H3.
  rewrite Nat2Z.inj_sub; [ idtac | apply lt_le_weak; assumption ].
  rewrite QZ_minus.
  field.
  unfold Qminus, Qplus; simpl.
  do 2 rewrite Z.mul_1_r.
  unfold Qeq; simpl.
  rewrite Z.mul_1_r, Z.add_opp_r.
  intros H.
  apply Zminus_eq, Nat2Z.inj in H.
  subst k; apply lt_irrefl in H3; contradiction.

  apply points_of_polyn_sorted in Hpts.
  symmetry in Heqlch.
  eapply in_newt_segm in Heqlch; eassumption.
Qed.

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

Lemma minus_Sn_n : ∀ n, (S n - n = 1)%nat.
Proof.
intros n.
rewrite <- minus_Sn_m; [ rewrite minus_diag; reflexivity | apply le_n ].
Qed.

Lemma zzz : ∀ α j jps k kps β γ pt pts ms segkx lch n,
  LocallySorted fst_lt [(j, jps), pt … pts]
  → LocallySorted fst_fst_lt [(j, jps, seg ms), (k, kps, segkx) … lch]
    → β = valuation α jps + Qnat j * γ
      → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
        → minimise_slope α (j, jps) pt pts = ms
          → next_ch_points α n [end_pt ms … rem_pts ms] =
              [(k, kps, segkx) … lch]
            → ∀ i ips,
              (i, ips) ∈ [pt … pts]
              → (i, ips) ∉ [(j, jps), (k, kps) … seg ms]
                → β < valuation α ips + Qnat i * γ.
Proof.
intros α j jps k kps β γ pt pts ms segkx lch n.
intros Hsort Hsort₂ Hβ Hγ Hms Hnp i ips Hips Hnips.
destruct Hips as [Hips| Hips].
 subst pt.
 remember Hms as Hms₂; clear HeqHms₂.
 apply min_sl_in in Hms.
 simpl in Hms.
 destruct Hms as [Hms| Hms].
  rewrite <- Hms in Hnp.
  apply next_ch_points_hd in Hnp.
  rewrite Hnp in Hnips.
  simpl in Hnips.
  apply Decidable.not_or in Hnips.
  destruct Hnips as (Hjk, Hnips).
  apply Decidable.not_or in Hnips.
  destruct Hnips as (Hnips); exfalso; apply Hnips; reflexivity.
bbb.

Lemma not_in_newt_segm : ∀ α pts j jps k kps γ β segjk segkx lch,
  LocallySorted fst_lt pts
  → LocallySorted fst_fst_lt [(j, jps, segjk), (k, kps, segkx) … lch]
    → β = valuation α jps + Qnat j * γ
      → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
        → lower_convex_hull_points α pts =
            [(j, jps, segjk), (k, kps, segkx) … lch]
          → ∀ i ips,
            (i, ips) ∈ pts
            → (i, ips) ∉ [(j, jps), (k, kps) … segjk]
              → β < valuation α ips + Qnat i * γ.
Proof.
intros α pts j jps k kps γ β segjk segkx lch.
intros Hsort Hsort₂ Hβ Hγ Hch i ips Hips Hnips.
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
eapply zzz; eassumption.
bbb.

Lemma points_not_in_newton_segment : ∀ α fld pol pts γ β j jps k kps seg,
  pts = points_of_ps_polynom α fld pol
  → gamma_beta fld pol = Some (γ, β, (j, jps), (k, kps), seg)
    → ∀ i ips,
       (i, ips) ∈ pts
       → (i, ips) ∉ [(j, jps), (k, kps) … seg]
         → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld pol pts γ β j jps k kps seg.
intros Hpts Hgb i ips Hips Hnips.
unfold gamma_beta in Hgb.
unfold gamma_beta_gen in Hgb.
remember Hpts as Hpts₂; clear HeqHpts₂.
unfold points_of_ps_polynom in Hpts₂.
rewrite <- Hpts₂ in Hgb.
remember (lower_convex_hull_points α pts) as lch.
destruct lch as [| ((l, lps), seg₁)]; [ discriminate Hgb | idtac ].
destruct lch as [| ((m, mps), seg₂)]; [ discriminate Hgb | idtac ].
injection Hgb; clear Hgb; intros; subst l lps m mps seg₁.
rename H4 into Hβ.
rename H5 into Hγ.
rewrite Hγ in Hβ.
symmetry in Hβ, Hγ.
unfold points_of_ps_polynom in Hpts.
apply points_of_polyn_sorted in Hpts.
symmetry in Heqlch.
eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
apply points_of_polyn_sorted in Hpts₂.
bbb.

(*
Lemma xxx : ∀ α fld deg cl cn pts c j jps k kps jk kx lch γ β,
  pts = filter_non_zero_ps α fld (all_points_of_ps_polynom α (S deg) cl cn)
  → next_ch_points α (deg, c) pts = [((j, jps), jk), ((k, kps), kx) … lch]
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → c ≠ zero fld
          → ∀ i ips,
               (i, ips) ∈ pts
               → (i, ips) ∉ points_in_segment α γ β [(deg, c) … pts]
                 → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts c j jps k kps jk kx lch γ β.
intros Hpts Hnp Hγ Hβ Hc i ips Hips Hnips.
revert deg cn pts c lch i ips Hpts Hnp Hc Hips Hnips.
induction cl as [| c₁]; intros.
 simpl in Hpts.
 destruct (is_zero_dec fld cn) as [Heq| Hne].
  subst pts; contradiction.

  subst pts; simpl in Hnp.
  destruct (lt_dec deg (S deg)) as [Hlt| Hge].
   clear Hlt.
   injection Hnp; clear Hnp; intros; subst j jps k kps lch.
   destruct Hips as [Hips| ]; [ idtac | contradiction ].
   injection Hips; clear Hips; intros; subst i ips.
   rewrite minus_Sn_n in Hγ.
   clear Hnips; subst β γ.
   unfold Qnat; simpl.
   unfold Qdiv.
   simpl.
   unfold Qinv.
   simpl.
   rewrite Qmult_1_r.
   unfold Qminus.
   do 2 rewrite Qmult_plus_distr_r.
   simpl.
   rewrite Zpos_P_of_succ_nat.
   rewrite <- Nat2Z.inj_succ.
   remember (valuation α c) as x.
   remember (valuation α cn) as y.
bbb.

Lemma yyy : ∀ α fld deg cl cn pts j jps k kps jk kx lch β γ,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → lower_convex_hull_points α pts = [((j, jps), jk), ((k, kps), kx) … lch]
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → ∀ i ips,
            (i, ips) ∈ pts
            → (i, ips) ∉ points_in_segment α γ β pts
              → β < valuation α ips + Qnat i * γ.
Proof.
intros α fld deg cl cn pts j jps k kps jk kx lch β γ Hpts Hch Hγ Hβ.
intros i ips Hips Hnips.
unfold points_of_ps_polynom_gen in Hpts.
revert deg cn pts lch Hpts Hch i ips Hips Hnips.
induction cl as [| c]; intros.
 simpl in Hpts.
 subst pts.
 destruct (is_zero_dec fld cn); [ contradiction | discriminate Hch ].

 simpl in Hpts.
 destruct (is_zero_dec fld c) as [Hlt| Hge].
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

bbb.
   simpl in Hnips.
   remember (Qeq_bool (valuation α c + Qnat deg * γ) β) as b.
   destruct b.
    simpl in Hnips.
    apply Decidable.not_or in Hnips.
    destruct Hnips as (Hdeg, Hnips).
    symmetry in Heqb.
    apply Qeq_bool_iff in Heqb.
    symmetry in Heqb.
    destruct cl as [| c₁].
     simpl in Heqpts₁.
     destruct (is_zero_dec fld cn) as [Heq| Hne].
      subst pts₁; contradiction.

      subst pts₁.
      destruct Hips as [Hips| ]; [ idtac | contradiction ].
      injection Hips; clear Hips; intros; subst i ips.
      simpl in Hch.
      destruct (lt_dec deg (S deg)) as [Hlt| Hge₂].
       injection Hch; clear Hch; intros; subst j jps k kps lch.
       clear IHcl.
       rewrite minus_Sn_n in Hγ.
       simpl in Hnips.
       remember (Qeq_bool (valuation α cn + Qnat (S deg) * γ) β) as b.
       destruct b.
        simpl in Hnips.
        apply Decidable.not_or in Hnips.
        destruct Hnips as (H, _); exfalso; apply H; reflexivity.

        clear Hlt Hnips Hdeg.
        symmetry in Heqb0.
        apply Qeq_bool_neq in Heqb0.
        symmetry in Heqb.
        symmetry in Hβ.
        clear Heqb.
        rewrite <- Hβ in Heqb0.
        subst γ.
        exfalso; apply Heqb0; clear Heqb0 Hβ.
        unfold Qnat.
        simpl.
        replace (' Pos.of_succ_nat deg # 1) with ((Z.of_nat deg # 1) + 1).
         field.

         unfold Qplus.
         simpl.
         rewrite Zmult_1_r.
         rewrite Zplus_comm.
         rewrite Zpos_P_of_succ_nat.
         simpl.
         destruct (Z.of_nat deg); try reflexivity.
         destruct p; reflexivity.

       discriminate Hch.

     simpl in Heqpts₁.
     destruct (is_zero_dec fld c₁) as [Heq| Hne].

bbb.

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
destruct lch as [| ((l, lt), lm)]; [ discriminate Heqgb | idtac ].
destruct lch as [| ((m, mt), mx)]; [ discriminate Heqgb | idtac ].
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
*)

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
