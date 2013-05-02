(* $Id: Puiseux.v,v 1.449 2013-05-02 06:59:42 deraugla Exp $ *)

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

Fixpoint list_map_pairs α β (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ … ([x₂ … l₂] as l₁)] => [f x₁ x₂ … list_map_pairs α β f l₁]
  end.
Arguments list_map_pairs : default implicits.

Record newton_segment α := mkns
  { γ : Q;
    β : Q;
    ini_pt : (nat * puiseux_series α);
    fin_pt : (nat * puiseux_series α);
    oth_pts : list (nat * puiseux_series α) }.
Arguments γ : default implicits.
Arguments β : default implicits.
Arguments ini_pt : default implicits.
Arguments fin_pt : default implicits.
Arguments oth_pts : default implicits.

Definition gamma_beta_of_pair α hsj hsk :=
  let αj := valuation α (snd (pt hsj)) in
  let αk := valuation α (snd (pt hsk)) in
  let γ := (αj - αk) / Qnat (fst (pt hsk) - fst (pt hsj))%nat in
  let β := αj + Qnat (fst (pt hsj)) * γ in
  mkns α γ β (pt hsj) (pt hsk) (oth hsj).

Definition newton_segments α fld pol :=
  let gdpl := points_of_ps_polynom α fld pol in
  list_map_pairs (gamma_beta_of_pair α) (lower_convex_hull_points α gdpl).
Arguments newton_segments : default implicits.

Section convex_hull.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma fold_points_of_ps_polynom_gen : ∀ pow cl cn,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn) =
  points_of_ps_polynom_gen α fld pow cl cn.
Proof. reflexivity. Qed.

Definition fst_lt {α} (x y : nat * α) := (fst x < fst y)%nat.
Definition hs_x_lt {α} (x y : hull_seg α) := (fst (pt x) < fst (pt y))%nat.

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

Lemma rem_pts_in : ∀ pt₁ pt₂ pts₂ ms pt,
  minimise_slope α pt₁ pt₂ pts₂ = ms
  → pt ∈ rem_pts ms
    → pt ∈ pts₂.
Proof.
intros pt₁ pt₂ pts₂ ms pt Hms Hpt.
revert pt₁ pt₂ ms Hms Hpt.
induction pts₂ as [| pt₃]; intros; [ subst ms; contradiction | idtac ].
simpl in Hms.
remember (minimise_slope α pt₁ pt₃ pts₂) as ms₁.
symmetry in Heqms₁.
remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; simpl in Hpt.
 right; eapply IHpts₂; eassumption.

 assumption.

 right; eapply IHpts₂; eassumption.
Qed.

Lemma end_pt_in : ∀ pt₁ pt₂ pts₂ ms,
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

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pts₁ sg hsl,
  next_ch_points α n [pt₁ … pts₁] = [{| pt := pt₂; oth := sg |} … hsl]
  → fst pt₁ ≤ fst pt₂.
Proof.
intros n pt₁ pt₂ pts₁ sg hsl Hnp.
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

Lemma next_points_sorted : ∀ n pts hsl,
  LocallySorted fst_lt pts
  → next_ch_points α n pts = hsl
    → LocallySorted hs_x_lt hsl.
Proof.
intros n pts hsl Hsort Hnp.
revert pts hsl Hsort Hnp.
induction n; intros; [ subst hsl; constructor | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ subst hsl; constructor | idtac ].
destruct pts as [| pt₂]; [ subst hsl; constructor | idtac ].
remember (minimise_slope α pt₁ pt₂ pts) as ms₂.
remember (next_ch_points α n [end_pt ms₂ … rem_pts ms₂]) as hsl₁.
subst hsl.
symmetry in Heqhsl₁.
remember Heqhsl₁ as Hch; clear HeqHch.
apply IHn in Heqhsl₁.
 destruct hsl₁ as [| (pt₃, sg)]; [ constructor | idtac ].
 constructor; [ assumption | idtac ].
 unfold hs_x_lt; simpl.
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

Lemma lower_convex_hull_points_sorted : ∀ pts hsl,
  LocallySorted fst_lt pts
  → lower_convex_hull_points α pts = hsl
    → LocallySorted hs_x_lt hsl.
Proof.
intros pts hsl Hsort Hch.
eapply next_points_sorted; eassumption.
Qed.

Lemma next_ch_points_hd : ∀ n pt₁ pt₂ pts₁ seg hsl,
  next_ch_points α n [pt₁ … pts₁] = [ahs pt₂ seg … hsl]
  → pt₁ = pt₂.
Proof.
intros n pt₁ pt₂ pts₂ seg₂ hsl Hnp.
revert pt₁ pt₂ pts₂ seg₂ hsl Hnp.
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

(* points in newton segment *)

Lemma Qnat_minus : ∀ a b, b ≤ a → Qnat a - Qnat b == Qnat (a - b).
Proof.
intros a b Hba.
unfold Qnat, Qminus, Qplus; simpl.
do 2 rewrite Zmult_1_r.
rewrite Nat2Z.inj_sub; [ idtac | assumption ].
unfold Zminus; reflexivity.
Qed.

Lemma min_sl_pt_in_newt_segm : ∀ j jps k kps β γ pt pts ms segkx hsl n,
  LocallySorted fst_lt [(j, jps); pt … pts]
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → minimise_slope α (j, jps) pt pts = ms
        → next_ch_points α n [end_pt ms … rem_pts ms] =
            [ahs (k, kps) segkx … hsl]
          → ∀ i ips, (i, ips) ∈ seg ms
            → valuation α ips + Qnat i * γ == β.
Proof.
intros j jps k kps β γ pt pts ms segkx hsl n.
intros Hsort Hβ Hγ Hms Hnp i ips Hips.
revert pt ms hsl n i ips Hsort Hips Hms Hnp.
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
   do 2 rewrite Qnat_minus in Heqms₁.
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

    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    apply minimise_slope_le in Hms; [ idtac | assumption ].
    rewrite <- Hnp in Hms.
    eapply le_trans; [ idtac | eassumption ].
    eapply lt_le_weak.
    eapply le_lt_trans; [ idtac | eassumption ].
    eapply lt_le_weak; eassumption.

    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    apply lt_le_weak; assumption.

    apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
    apply lt_le_weak; assumption.

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

Lemma in_newt_segm : ∀ j jps k kps γ β n pts segjk segkx hsl₁ hsl,
  LocallySorted fst_lt pts
  → β = valuation α jps + Qnat j * γ
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → next_ch_points α n pts =
          hsl₁ ++ [ ahs (j, jps) segjk; ahs (k, kps) segkx … hsl]
        → ∀ i ips, (i, ips) ∈ segjk
          → valuation α ips + Qnat i * γ == β.
Proof.
intros j jps k kps γ β n pts segjk segkx hsl₁ hsl.
intros Hsort Hβ Hγ Hch i ips Hips.
rename Hch into Hnp.
destruct n; [ apply List.app_cons_not_nil in Hnp; contradiction | idtac ].
destruct pts as [| pt₁].
 apply List.app_cons_not_nil in Hnp; contradiction.

 destruct pts as [| pt₂].
  destruct hsl₁ as [| pt₂]; [ discriminate Hnp | idtac ].
  destruct hsl₁; discriminate Hnp.

  revert n pt₁ pt₂ pts Hnp Hsort.
  induction hsl₁ as [| hs₁]; intros.
   injection Hnp; clear Hnp; intros; subst segjk.
   rewrite H1 in H, Hips, Hsort.
   eapply min_sl_pt_in_newt_segm; try eassumption; reflexivity.

   injection Hnp; clear Hnp; intros; subst hs₁.
   rename H into Hnp.
   destruct n; [ apply List.app_cons_not_nil in Hnp; contradiction | idtac ].
   remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
   symmetry in Heqms₁.
   eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
   remember (rem_pts ms₁) as pts₁.
   destruct pts₁ as [| pt₃].
    destruct hsl₁ as [| pt₃]; [ discriminate Hnp | idtac ].
    destruct hsl₁; discriminate Hnp.

    eapply IHhsl₁; eassumption.
Qed.

Lemma two_pts_slope_form : ∀ j jps seg₁ k kps seg₂ hsl,
  LocallySorted hs_x_lt [ahs (j, jps) seg₁; ahs (k, kps) seg₂ … hsl]
  → valuation α jps +
    Qnat j * ((valuation α jps - valuation α kps) / Qnat (k - j)) ==
    valuation α kps +
    Qnat k * ((valuation α jps - valuation α kps) / Qnat (k - j)).
Proof.
intros j jps seg₁ k kps seg₂ hsl Hsort.
apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
unfold hs_x_lt in Hlt; simpl in Hlt.
unfold Qnat.
rewrite Nat2Z.inj_sub; [ idtac | apply lt_le_weak; assumption ].
rewrite QZ_minus.
field.
unfold Qminus, Qplus; simpl.
do 2 rewrite Z.mul_1_r.
unfold Qeq; simpl.
rewrite Z.mul_1_r, Z.add_opp_r.
intros H.
apply Zminus_eq, Nat2Z.inj in H.
subst k; apply lt_irrefl in Hlt; contradiction.
Qed.

Theorem points_in_any_newton_segment : ∀ pol ns,
  ns ∈ newton_segments fld pol
  → ∀ h hps, (h, hps) ∈ [ini_pt ns; fin_pt ns … oth_pts ns]
    → β ns == valuation α hps + Qnat h * γ ns.
Proof.
intros pol ns Hns h hps Hhps.
unfold newton_segments in Hns.
remember (points_of_ps_polynom α fld pol) as pts.
remember (lower_convex_hull_points α pts) as hsl.
symmetry in Heqhsl.
rename Heqpts into Hpts.
apply points_of_polyn_sorted in Hpts.
remember Hpts as Hpts₂; clear HeqHpts₂.
eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
revert n pts ns Heqhsl Hns Hhps Hpts₂.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
simpl in Hns.
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 destruct hs₁ as ((j, jps), seg₁).
 destruct hs₂ as ((k, kps), seg₂).
 subst ns; simpl.
 simpl in Hhps.
 destruct Hhps as [Hhps| Hhps].
  injection Hhps; clear Hhps; intros; subst h hps; reflexivity.

  destruct Hhps as [Hhps| Hhps].
   injection Hhps; clear Hhps; intros; subst h hps.
   eapply two_pts_slope_form; eassumption.

   destruct pts as [| pt₁].
    unfold lower_convex_hull_points in Heqhsl.
    destruct n; discriminate Heqhsl.

    symmetry.
    eapply in_newt_segm with (hsl₁ := []); try eassumption; try reflexivity.

 destruct n; [ discriminate Heqhsl | idtac ].
 simpl in Heqhsl.
 destruct pts as [| pt₁]; [ discriminate Heqhsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Heqhsl | idtac ].
 injection Heqhsl; clear Heqhsl; intros.
 remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 apply LocallySorted_inv_1 in Hpts.
 eapply minimise_slope_sorted in Hpts₂; [ idtac | eassumption ].
 eapply IHhsl; eassumption.
Qed.

(* points not in newton segment *)

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
 apply end_pt_in in Hms.
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

Lemma points_after_k : ∀ n pts j jps k kps seg seg₂ hsl γ β,
  LocallySorted fst_lt pts
  → (j < k)%nat
    → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
      → β = valuation α jps + Qnat j * γ
        → next_ch_points α n pts = [ahs (j, jps) seg; ahs (k, kps) seg₂ … hsl]
          → ∀ h hps, (k < h)%nat
            → (h, hps) ∈ pts
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx hsl γ β.
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
   apply ad_hoc_lt_lt.
    split; [ idtac | assumption ].
    destruct pt₁ as (l, lps).
    apply lt_trans with (m := l).
     apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.

     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
     eapply LocallySorted_hd in Hsort; [ idtac | eassumption ].
     assumption.

    unfold slope_expr in Heqms₁; simpl in Heqms₁.
    do 2 rewrite Qnat_minus in Heqms₁.
     assumption.

     apply lt_le_weak.
     eapply lt_trans; eassumption.

     apply lt_le_weak; assumption.

     apply lt_le_weak; assumption.

   apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
   destruct pts as [| pt₂]; [ constructor | idtac ].
   apply LocallySorted_inv_2 in Hsort; destruct Hsort; assumption.
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

  subst pts₁.
  apply Qgt_alt in Heqc₁.
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
Qed.

Lemma points_between_j_and_k : ∀ n pts j jps k kps sjk skx hsl γ β,
  LocallySorted fst_lt pts
  → γ = (valuation α jps - valuation α kps) / Qnat (k - j)
    → β = valuation α jps + Qnat j * γ
      → next_ch_points α n pts = [ahs (j, jps) sjk; ahs (k, kps) skx … hsl]
        → ∀ h hps, (j < h < k)%nat
          → (h, hps) ∈ pts
            → (h, hps) ∉ sjk
              → β < valuation α hps + Qnat h * γ.
Proof.
intros n pts j jps k kps segjk segkx hsl γ β.
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
    apply ad_hoc_lt_lt.
     split; [ assumption | idtac ].
     eapply lt_trans; eassumption.

     unfold slope_expr in Heqc; simpl in Heqc.
     do 2 rewrite Qnat_minus in Heqc.
      assumption.

      apply lt_le_weak.
      assumption.

      apply lt_le_weak.
      eapply lt_trans; eassumption.

      apply lt_le_weak.
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
     apply ad_hoc_lt_lt.
      split; [ assumption | idtac ].
      eapply lt_trans; eassumption.

      unfold slope_expr in Heqms₁; simpl in Heqms₁.
      do 2 rewrite Qnat_minus in Heqms₁.
       assumption.

       apply lt_le_weak; assumption.

       apply lt_le_weak; eapply lt_trans; eassumption.

       apply lt_le_weak; eapply lt_trans; eassumption.

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

Lemma same_k_same_kps : ∀ pts j jps k (kps : puiseux_series α),
  LocallySorted fst_lt pts
  → (j, jps) ∈ pts
    → (k, kps) ∈ pts
      → j = k
        → jps = kps.
Proof.
intros pts j jps k kps Hpts Hjps Hkps Hjk.
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

Lemma in_ch_in_pts : ∀ n pts pt s,
  ahs pt s ∈ next_ch_points α n pts
  → pt ∈ pts.
Proof.
intros n pts pt s Hhs.
remember (next_ch_points α n pts) as hsl.
rename Heqhsl into Hhsl.
revert n pts pt s Hhsl Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct n; [ discriminate Hhsl | idtac ].
simpl in Hhsl.
destruct pts as [| pt₁]; [ discriminate Hhsl | idtac ].
destruct pts as [| pt₂].
 injection Hhsl; clear Hhsl; intros; subst hs₁ hsl.
 destruct Hhs as [Hhs| ]; [ idtac | contradiction ].
 injection Hhs; clear Hhs; intros; subst pt s.
 left; reflexivity.

 injection Hhsl; clear Hhsl; intros.
 destruct Hhs as [Hhs| Hhs].
  subst hs₁.
  injection H0; clear H0; intros; subst pt₁.
  left; reflexivity.

  remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  eapply IHhsl in H; [ idtac | eassumption ].
  destruct H as [H| H].
   apply end_pt_in in Heqms₁.
   subst pt.
   right; assumption.

   eapply rem_pts_in in H; [ idtac | eassumption ].
   right; right; assumption.
Qed.

Theorem points_not_in_newton_segment : ∀ pol pts ns nsl,
  pts = points_of_ps_polynom α fld pol
  → newton_segments fld pol = [ns … nsl]
    → ∀ h hps, (h, hps) ∈ pts ∧ (h, hps) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < valuation α hps + Qnat h * (γ ns).
Proof.
intros pol pts ns nsl Hpts Hns h hps (Hhps, Hnhps).
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points α pts) as hsl.
destruct hsl as [| ((j, jps), segjx)]; [ discriminate Hns | idtac ].
destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hns | idtac ].
injection Hns; clear Hns; intros; subst ns.
simpl in H |- *.
rename H into Hhsl.
symmetry in Heqhsl.
destruct (lt_dec k h) as [Hlt| Hge].
 apply points_of_polyn_sorted in Hpts.
 remember Hpts as Hpts₂; clear HeqHpts₂.
 eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
 apply LocallySorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
 unfold hs_x_lt in Hlt; simpl in Hlt.
 eapply points_after_k; try eassumption; reflexivity.

 apply not_gt in Hge.
 destruct (eq_nat_dec h k) as [Heq| Hne].
  unfold points_of_ps_polynom in Hpts.
  apply points_of_polyn_sorted in Hpts.
  eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
   subst h hps.
   simpl in Hnhps.
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (_, Hnhps).
   apply Decidable.not_or in Hnhps.
   destruct Hnhps as (Hnhps, _).
   exfalso; apply Hnhps; reflexivity.

   eapply in_ch_in_pts with (n := length pts).
   unfold lower_convex_hull_points in Heqhsl; rewrite Heqhsl.
   right; left; reflexivity.

  apply le_neq_lt in Hge; [ idtac | assumption ].
  destruct (lt_dec j h) as [Hlt| Hge₂].
   apply points_of_polyn_sorted in Hpts.
   remember Hpts as Hpts₂; clear HeqHpts₂.
   eapply lower_convex_hull_points_sorted in Hpts; [ idtac | eassumption ].
   unfold hs_x_lt in Hlt; simpl in Hlt.
   eapply points_between_j_and_k; try eassumption; try reflexivity.
    split; assumption.

    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    assumption.

   apply not_gt in Hge₂.
   apply points_of_polyn_sorted in Hpts.
   unfold lower_convex_hull_points in Heqhsl.
   remember (length pts) as n; clear Heqn.
   destruct n.
    simpl in Heqhsl.
    discriminate Heqhsl.

    simpl in Heqhsl.
    destruct pts as [| (l, lps)]; [ discriminate Heqhsl | idtac ].
    destruct pts as [| (m, mps)]; [ discriminate Heqhsl | idtac ].
    injection Heqhsl; clear Heqhsl; intros; subst l lps.
    destruct Hhps as [Hhps| Hhps].
     injection Hhps; clear Hhps; intros; subst h hps.
     simpl in Hnhps.
     apply Decidable.not_or in Hnhps.
     destruct Hnhps as (HH); exfalso; apply HH; reflexivity.

     eapply LocallySorted_hd in Hpts; [ idtac | eassumption ].
     apply le_not_lt in Hge₂; contradiction.
Qed.

(* is there a way to group together the cases c = Eq and c = Gt? *)
Lemma aft_end_in_rem : ∀ pt₁ pt₂ pts ms,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → ∀ h hps, (h, hps) ∈ [pt₁; pt₂ … pts] 
      → (fst (end_pt ms) < h)%nat
        → (h, hps) ∈ rem_pts ms.
Proof.
intros pt₁ pt₂ pts ms Hsort Hms h hps Hhps Hlt.
destruct Hhps as [Hhps| Hhps].
 subst pt₁.
 apply minimise_slope_le in Hms.
  apply LocallySorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₁).
  eapply lt_trans in Hlt₁; [ idtac | eassumption ].
  apply le_not_lt in Hms; contradiction.

  eapply LocallySorted_inv_1; eassumption.

 destruct Hhps as [Hhps| Hhps].
  subst pt₂.
  apply minimise_slope_le in Hms.
   apply le_not_lt in Hms; contradiction.

   eapply LocallySorted_inv_1; eassumption.

  revert pt₁ pt₂ ms Hsort Hms Hhps Hlt.
  induction pts as [| pt₃]; [ contradiction | intros ].
  simpl in Hms.
  remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr α pt₁ pt₂ ?= slope ms₁) as c.
  symmetry in Heqc.
  destruct c; subst ms; simpl in Hlt |- *.
   destruct Hhps as [Hhps| Hhps].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply le_not_lt in Heqms₁; contradiction.

     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    constructor.
     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
     eapply lt_trans; eassumption.

   assumption.

   destruct Hhps as [Hhps| Hhps].
    subst pt₃.
    apply minimise_slope_le in Heqms₁.
     apply le_not_lt in Heqms₁; contradiction.

     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

    eapply IHpts; try eassumption.
    constructor.
     do 2 apply LocallySorted_inv_1 in Hsort.
     assumption.

     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
     apply LocallySorted_inv_2 in Hsort; destruct Hsort as (Hlt₂, Hsort).
     eapply lt_trans; eassumption.
Qed.

(* similar to 'aft_j_in_end_or_rem' : some merge somewhere? *)
Lemma aft_k_in_rem : ∀ n pt₁ pt₂ pts ms j jps segjk k kps segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → next_ch_points α n [end_pt ms … rem_pts ms] =
        [{| pt := (j, jps); oth := segjk |};
         {| pt := (k, kps); oth := segkx |} … hsl]
      → ∀ h hps, (h, hps) ∈ [pt₁; pt₂ … pts]
        → (k < h)%nat
          → (h, hps) ∈ rem_pts ms.
Proof.
intros n pt₁ pt₂ pts ms j jps segjk k kps segkx hsl.
intros Hsort Hms Hnp h hps Hhps Hkh.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros.
rename H into Hnp.
rename H0 into Hseg.
rename H1 into Hend.
remember (minimise_slope α (end_pt ms) pt₃ pts₁) as ms₁.
symmetry in Heqms₁.
destruct n; [ discriminate Hnp | idtac ].
remember (rem_pts ms₁) as pts₂.
rename Heqpts₂ into Hrem₁.
symmetry in Hrem₁.
subst segjk.
right.
remember Hsort as Hsort₂; clear HeqHsort₂.
eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
rewrite Hend, Hrem in Hsort.
(**)
revert Hsort₂ Hms Hhps Hrem Heqms₁ Hnp Hkh Hsort Hend; clear; intros.
(**)
eapply aft_end_in_rem in Hsort₂; try eassumption.
 rewrite Hrem in Hsort₂.
 destruct Hsort₂ as [Hhps₂| ]; [ idtac | assumption ].
 subst pt₃.
 apply minimise_slope_le in Heqms₁.
  simpl in Hnp.
  destruct pts₂ as [| pt₄].
   injection Hnp; clear Hnp; intros; subst hsl segkx.
   apply le_not_lt in Heqms₁; rewrite H1 in Heqms₁; contradiction.

   injection Hnp; clear Hnp; intros; subst hsl segkx.
   apply le_not_lt in Heqms₁; rewrite H1 in Heqms₁; contradiction.

  eapply LocallySorted_inv_1; eassumption.

 rewrite Hend; simpl.
 eapply lt_trans; [ idtac | eassumption ].
 apply minimise_slope_le in Heqms₁.
  simpl in Hnp.
  apply LocallySorted_inv_2 in Hsort; destruct Hsort.
  destruct pts₂ as [| pt₄].
   injection Hnp; clear Hnp; intros; subst hsl segkx.
   rewrite H3 in Heqms₁; simpl in Heqms₁.
   eapply lt_le_trans; eassumption.

   injection Hnp; clear Hnp; intros; subst hsl segkx.
   rewrite H3 in Heqms₁; simpl in Heqms₁.
   eapply lt_le_trans; eassumption.

  apply LocallySorted_inv_1 in Hsort; assumption.
Qed.

(* similar to 'aft_k_in_rem' : some merge somewhere? *)
Lemma aft_j_in_end_or_rem : ∀ n pt₁ pt₂ pts ms j jps segjk k kps segkx hsl,
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope α pt₁ pt₂ pts = ms
    → next_ch_points α n [end_pt ms … rem_pts ms] =
       [{| pt := (j, jps); oth := segjk |};
        {| pt := (k, kps); oth := segkx |} … hsl]
      → ∀ h hps, (h, hps) ∈ [pt₁; pt₂ … pts]
        → (j < h)%nat
          → (h, hps) ∈ [end_pt ms … rem_pts ms].
Proof.
intros n pt₁ pt₂ pts ms j jps segjk k kps segkx hsl.
intros Hsort Hms Hnp h hps Hhps Hjh.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
remember (rem_pts ms) as pts₁.
rename Heqpts₁ into Hrem.
symmetry in Hrem.
destruct pts₁ as [| pt₃]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros.
rename H into Hnp.
rename H0 into Hseg.
rename H1 into Hend.
remember (minimise_slope α (end_pt ms) pt₃ pts₁) as ms₁.
symmetry in Heqms₁.
destruct n; [ discriminate Hnp | idtac ].
remember (rem_pts ms₁) as pts₂.
rename Heqpts₂ into Hrem₁.
symmetry in Hrem₁.
subst segjk.
right.
remember Hsort as Hsort₂; clear HeqHsort₂.
eapply minimise_slope_sorted in Hsort; [ idtac | eassumption ].
rewrite Hend, Hrem in Hsort.
(**)
revert Hms Hhps Hjh Hend Hsort₂ Hrem; clear; intros.
(**)
eapply aft_end_in_rem in Hsort₂; try eassumption.
 rewrite Hrem in Hsort₂; assumption.

 rewrite Hend; assumption.
Qed.

Fixpoint left_shift_convex_hull_oth α ch :=
  match (ch : list (hull_seg (puiseux_series α))) with
  | [] => []
  | [hs₁ … hsl₁] =>
      match hsl₁ with
      | [] => [ahs (pt hs₁) []]
      | [hs₂ … hsl₂] =>
          let hsl₃ := left_shift_convex_hull_oth α hsl₁ in
          [ahs (pt hs₁) (List.rev (oth hs₂)) … hsl₃]
      end
  end.

Lemma zzz : ∀ pts,
  lower_convex_hull_points α (List.rev pts) =
  left_shift_convex_hull_oth α (List.rev (lower_convex_hull_points α pts)).
Proof.
Admitted. (*
bbb.
*)

Lemma lt_aft_k : ∀ n pts hs₁ hsl j jps segjk k kps segkx,
  LocallySorted fst_lt pts
  → next_ch_points α n pts =
      [hs₁; {| pt := (j, jps); oth := segjk |};
       {| pt := (k, kps); oth := segkx |} … hsl]
    → ∀ h hps, (h, hps) ∈ pts
      → (k < h)%nat
        → valuation α jps +
          Qnat j * ((valuation α jps - valuation α kps) / Qnat (k - j)) <
          valuation α hps +
          Qnat h * ((valuation α jps - valuation α kps) / Qnat (k - j)).
Proof.
intros n pts hs₁ hsl j jps segjk k kps segkx Hsort Hnp h hps Hhps Hkh.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros.
eapply points_after_k; try reflexivity.
 eapply minimise_slope_sorted; [ eassumption | reflexivity ].

 apply next_points_sorted in H.
  apply LocallySorted_inv_2 in H.
  destruct H; assumption.

  eapply minimise_slope_sorted; [ eassumption | reflexivity ].

 eassumption.

 assumption.

 right.
 remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 eapply aft_k_in_rem; eassumption.
Qed.

Theorem points_not_in_any_newton_segment : ∀ pol pts ns,
  pts = points_of_ps_polynom α fld pol
  → ns ∈ newton_segments fld pol
    → ∀ h hps, (h, hps) ∈ pts ∧ (h, hps) ∉ [ini_pt ns; fin_pt ns … oth_pts ns]
      → β ns < valuation α hps + Qnat h * (γ ns).
Proof.
intros pol pts ns Hpts Hns h hps (Hhps, Hnhps).
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
remember (lower_convex_hull_points α pts) as hsl.
symmetry in Heqhsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hhsl.
remember (length pts) as n; clear Heqn.
apply points_of_polyn_sorted in Hpts.
clear pol.
remember (list_map_pairs (gamma_beta_of_pair α) hsl) as nsl.
rename Heqnsl into Hnsl.
symmetry in Hnsl.
revert n pts ns hsl Hpts Hhps Hhsl Hnsl Hns Hnhps.
induction nsl as [| ns₁]; [ contradiction | intros ].
destruct Hns as [Hns| Hns].
 subst ns₁.
 clear IHnsl.
 destruct hsl as [| ((j, jps), segjk)]; [ discriminate Hnsl | idtac ].
 destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hnsl | idtac ].
 simpl in Hnsl.
 injection Hnsl; clear Hnsl; intros.
 rename H0 into Hns.
 unfold gamma_beta_of_pair in Hns; simpl in Hns.
 subst ns; simpl in Hnhps |- *.
 destruct (le_dec k h) as [Hle| Hgt].
  destruct (eq_nat_dec h k) as [Heq| Hne].
   eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
    subst h hps.
    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (Hnhps, _).
    exfalso; apply Hnhps; reflexivity.

    eapply in_ch_in_pts with (n := n).
    rewrite Hhsl.
    right; left; reflexivity.

   remember Hpts as Hpts₂; clear HeqHpts₂.
   eapply points_after_k; try eassumption; try reflexivity.
    apply next_points_sorted in Hhsl; [ idtac | assumption ].
    apply LocallySorted_inv_2 in Hhsl.
    destruct Hhsl; assumption.

    apply not_eq_sym in Hne.
    apply le_neq_lt; try assumption.

  apply not_ge in Hgt.
  destruct (lt_dec j h) as [Hlt| Hge₂].
   eapply points_between_j_and_k; try eassumption; try reflexivity.
    split; assumption.

    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (_, Hnhps).
    assumption.

   apply not_gt in Hge₂.
   destruct n; [ discriminate Hhsl | idtac ].
   simpl in Hhsl.
   destruct pts as [| (l, lps)]; [ discriminate Hhsl | idtac ].
   destruct pts as [| (m, mps)]; [ discriminate Hhsl | idtac ].
   injection Hhsl; clear Hhsl; intros; subst l lps.
   rename H into Hhsl.
   rename H0 into Hseg.
   destruct Hhps as [Hhps| Hhps].
    injection Hhps; clear Hhps; intros; subst h hps.
    simpl in Hnhps.
    apply Decidable.not_or in Hnhps.
    destruct Hnhps as (H); exfalso; apply H; reflexivity.

    eapply LocallySorted_hd in Hpts; [ idtac | eassumption ].
    apply le_not_lt in Hge₂; contradiction.

 clear IHnsl.
 revert n pts ns ns₁ hsl Hpts Hhps Hhsl Hnsl Hns Hnhps.
 induction nsl as [| ns₂]; [ contradiction | intros ].
 destruct Hns as [Hns| Hns].
  subst ns.
  clear IHnsl.
  destruct hsl as [| hs₁]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((j, jps), segjk)]; [ discriminate Hnsl | idtac ].
  destruct hsl as [| ((k, kps), segkx)]; [ discriminate Hnsl | idtac ].
  simpl in Hnsl.
  injection Hnsl; clear Hnsl; intros.
  subst ns₁.
  subst ns₂; simpl in Hnhps |- *.
  destruct (lt_dec k h) as [Hlt| Hge].
   eapply lt_aft_k; eassumption.

   destruct (eq_nat_dec h k) as [Heq| Hne].
    eapply same_k_same_kps with (kps := kps) in Hhps; try eassumption.
     subst h hps.
     apply Decidable.not_or in Hnhps.
     destruct Hnhps as (_, Hnhps).
     apply Decidable.not_or in Hnhps.
     destruct Hnhps as (Hnhps, _).
     exfalso; apply Hnhps; reflexivity.

     eapply in_ch_in_pts with (n := n).
     rewrite Hhsl.
     right; right; left; reflexivity.

    apply not_gt in Hge.
    destruct (lt_dec j h) as [Hlt| Hge₂].
     destruct n; [ discriminate Hhsl | idtac ].
     simpl in Hhsl.
     destruct pts as [| pt₁]; [ discriminate Hhsl | idtac ].
     destruct pts as [| pt₂]; [ discriminate Hhsl | idtac ].
     injection Hhsl; clear Hhsl; intros.
     eapply points_between_j_and_k; try reflexivity.
      eapply minimise_slope_sorted; [ eassumption | reflexivity ].

      eassumption.

      split; [ assumption | idtac ].
      apply le_neq_lt; assumption.

      remember (minimise_slope α pt₁ pt₂ pts) as ms₁.
      symmetry in Heqms₁.
      eapply aft_j_in_end_or_rem; eassumption.

      apply Decidable.not_or in Hnhps.
      destruct Hnhps as (_, Hnhps).
      apply Decidable.not_or in Hnhps.
      destruct Hnhps; assumption.

     apply not_gt in Hge₂.
bbb.

End convex_hull.

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
  let nsl := newton_segments pol in
  let rem_steps := (nb_steps - 1)%nat in
  List.fold_left
    (λ sol_list γβ₁,
       let br :=
         {| initial_polynom := pol; cγl := []; step := 1%nat;
            rem_steps := rem_steps; pol := pol |}
       in
       puiseux_branch k br sol_list γβ₁)
    nsl [].
*)
