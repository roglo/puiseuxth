(* $Id: ConvexHullMisc.v,v 1.7 2013-05-20 23:30:14 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import ConvexHull.
Require Import Slope_base.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Definition fst_lt (x y : Q * Q) := (fst x < fst y).
Definition hs_x_lt (x y : hull_seg) := (fst (pt x) < fst (pt y)).

Lemma Sorted_inv_1 {A} : ∀ (f : A → A → Prop) x l,
  Sorted f [x … l]
  → Sorted f l.
Proof.
intros f x l H.
apply Sorted_LocallySorted_iff in H.
apply Sorted_LocallySorted_iff.
inversion H; [ constructor | assumption ].
Qed.

Lemma Sorted_inv_2 {A} : ∀ (f : A → A → Prop) x y l,
  Sorted f [x; y … l]
  → f x y ∧ Sorted f [y … l].
Proof.
intros f x y l H.
apply Sorted_LocallySorted_iff in H.
rewrite Sorted_LocallySorted_iff.
inversion H; subst a b l0.
split; assumption.
Qed.

Lemma Sorted_in : ∀ pt₁ pt₂ pts,
  Sorted fst_lt [pt₁ … pts]
  → pt₂ ∈ [pt₁ … pts]
    → fst pt₁ <= fst pt₂.
Proof.
intros pt₁ pt₂ pts Hsort H.
revert pt₁ Hsort H.
induction pts as [| pt₃]; intros.
 destruct H as [H| ]; [ idtac | contradiction ].
 subst pt₁; apply Qle_refl.

 destruct H as [H| H].
  subst pt₁; apply Qle_refl.

  eapply Qle_trans with (y := fst pt₃).
   apply Qlt_le_weak.
   apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _); assumption.

   eapply IHpts; try eassumption.
   eapply Sorted_inv_1; eassumption.
Qed.

Lemma Sorted_app {A} : ∀ (f : A → A → Prop) l₁ l₂,
  Sorted f (l₁ ++ l₂) → Sorted f l₁ ∧ Sorted f l₂.
Proof.
intros f l₁ l₂ H.
split.
 induction l₁ as [| x]; [ constructor | simpl in H ].
 destruct l₁ as [| y]; [ constructor; constructor | idtac ].
 constructor; [ eapply IHl₁, Sorted_inv_1; eassumption | idtac ].
 constructor; apply Sorted_inv_2 in H; destruct H; assumption.

 induction l₁ as [| x]; [ assumption | apply IHl₁ ].
 eapply Sorted_inv_1; eassumption.
Qed.

Lemma Sorted_hd : ∀ (pt₁ pt₂ : Q * Q) pts,
  Sorted fst_lt [pt₁ … pts]
  → pt₂ ∈ pts
    → fst pt₁ < fst pt₂.
Proof.
intros pt₁ pt₂ pts Hsort Hpt.
revert pt₁ pt₂ Hsort Hpt.
induction pts as [| pt]; intros; [ contradiction | idtac ].
apply Sorted_inv_2 in Hsort.
destruct Hsort as (Hlt, Hsort).
destruct Hpt as [Hpt| Hpt]; [ subst pt; assumption | idtac ].
eapply Qlt_trans; [ eassumption | idtac ].
apply IHpts; assumption.
Qed.

Lemma Sorted_minus_2nd {A} : ∀ (f : A → A → Prop) x₁ x₂ xl,
  (∀ x y z, f x y → f y z → f x z)
  → Sorted f [x₁; x₂ … xl]
    → Sorted f [x₁ … xl].
Proof.
intros f x₁ x₂ l Ht H.
apply Sorted_LocallySorted_iff.
destruct l as [| x₃]; [ constructor | intros ].
constructor.
 apply Sorted_LocallySorted_iff.
 do 2 apply Sorted_inv_1 in H.
 assumption.

 apply Sorted_inv_2 in H; destruct H as (Hlt₁, H).
 apply Sorted_inv_2 in H; destruct H as (Hlt₂, H).
 eapply Ht; eassumption.
Qed.

Lemma Sorted_minus_3rd {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ xl,
  (∀ x y z, f x y → f y z → f x z)
  → Sorted f [x₁; x₂; x₃ … xl]
    → Sorted f [x₁; x₂ … xl].
Proof.
intros f x₁ x₂ x₃ l Ht H.
apply Sorted_LocallySorted_iff.
constructor.
 apply Sorted_inv_1 in H.
 apply Sorted_LocallySorted_iff.
 eapply Sorted_minus_2nd; eassumption.

 apply Sorted_inv_2 in H; destruct H; assumption.
Qed.

Lemma Sorted_minus_4th {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ x₄ xl,
  (∀ x y z, f x y → f y z → f x z)
  → Sorted f [x₁; x₂; x₃; x₄ … xl]
    → Sorted f [x₁; x₂; x₃ … xl].
Proof.
intros f x₁ x₂ x₃ x₄ l Ht H.
apply Sorted_LocallySorted_iff.
constructor.
 apply Sorted_inv_1 in H.
 apply Sorted_LocallySorted_iff.
 eapply Sorted_minus_3rd; eassumption.

 apply Sorted_inv_2 in H; destruct H; assumption.
Qed.

Lemma Sorted_not_in {A} : ∀ (f : A → A → Prop) a b l,
  (∀ x, ¬f x x)
  → (∀ x y z, f x y → f y z → f x z)
    → Sorted f [b … l]
      → f a b
        → a ∉ [b … l].
Proof.
intros f a b l Hirr Htran Hsort Hab Hin.
destruct Hin as [Hin| Hin].
 subst b.
 eapply Hirr; eassumption.

 induction l as [| c]; [ contradiction | intros ].
 destruct Hin as [Hin| Hin].
  subst c.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
  eapply Htran in Hab; [ eapply Hirr, Hab | eassumption ].

  apply IHl; [ idtac | assumption ].
  eapply Sorted_minus_2nd; eassumption.
Qed.

(* *)

Lemma minimise_slope_le : ∀ pt₁ pt₂ pts₂ ms,
  Sorted fst_lt [pt₂ … pts₂]
  → minimise_slope pt₁ pt₂ pts₂ = ms
    → fst pt₂ <= fst (end_pt ms).
Proof.
intros pt₁ pt₂ pts₂ ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts₂ as [| pt]; intros.
 subst ms; apply Qle_refl.

 simpl in Hms.
 remember (minimise_slope pt₁ pt pts₂) as ms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 destruct c; subst ms; simpl; [ idtac | apply Qle_refl | idtac ].
  apply Qlt_le_weak.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Qlt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.

  apply Qlt_le_weak.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Qlt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.
Qed.

Lemma next_ch_points_hd : ∀ n pt₁ pt₂ pts₁ seg hsl,
  next_ch_points n [pt₁ … pts₁] = [ahs pt₂ seg … hsl]
  → pt₁ = pt₂.
Proof.
intros n pt₁ pt₂ pts₂ seg₂ hsl Hnp.
revert pt₁ pt₂ pts₂ seg₂ hsl Hnp.
induction n; intros; [ discriminate Hnp | simpl in Hnp ].
destruct pts₂; injection Hnp; intros; subst pt₂; reflexivity.
Qed.

Lemma minimise_slope_sorted : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → Sorted fst_lt [end_pt ms … rem_pts ms].
Proof.
intros pt₁ pt₂ pts ms Hsort Hms.
apply Sorted_LocallySorted_iff.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros; [ subst ms; constructor | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqms₁.
apply Sorted_inv_2 in Hsort.
destruct Hsort as (Hlt₁, Hsort).
apply Sorted_LocallySorted_iff.
destruct c; subst ms; simpl; [ idtac | assumption | idtac ].
 apply Sorted_LocallySorted_iff.
 eapply IHpts; [ idtac | eassumption ].
 apply Sorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 apply Sorted_LocallySorted_iff.
 apply Sorted_LocallySorted_iff in Hsort.
 constructor; [ assumption | eapply Qlt_trans; eassumption ].

 apply Sorted_LocallySorted_iff.
 eapply IHpts; [ idtac | eassumption ].
 apply Sorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 apply Sorted_LocallySorted_iff.
 apply Sorted_LocallySorted_iff in Hsort.
 constructor; [ assumption | eapply Qlt_trans; eassumption ].
Qed.

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pts₁ sg hsl₁ hsl,
  Sorted fst_lt [pt₁ … pts₁]
  → next_ch_points n [pt₁ … pts₁] = hsl₁ ++ [ahs pt₂ sg … hsl]
    → fst pt₁ <= fst pt₂.
Proof.
intros n pt₁ pt₂ pts₁ sg hsl₁ hsl Hsort Hnp.
revert n pt₁ pt₂ pts₁ sg hsl Hsort Hnp.
induction hsl₁ as [| hs₁]; intros.
 apply next_ch_points_hd in Hnp; subst pt₁; apply Qle_refl.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts₁ as [| pt₃]; intros.
  destruct hsl₁; discriminate Hnp.

  injection Hnp; clear Hnp; intros Hnp; intros.
  subst hs₁.
  remember (minimise_slope pt₁ pt₃ pts₁) as ms₁.
  symmetry in Heqms₁.
  apply IHhsl₁ in Hnp.
   eapply Qle_trans; [ idtac | eassumption ].
   apply minimise_slope_le in Heqms₁.
    eapply Qle_trans; [ idtac | eassumption ].
    apply Qlt_le_weak.
    apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.

    eapply Sorted_inv_1; eassumption.

   eapply minimise_slope_sorted; eassumption.
Qed.

Lemma next_points_sorted : ∀ n pts hsl,
  Sorted fst_lt pts
  → next_ch_points n pts = hsl
    → Sorted hs_x_lt hsl.
Proof.
intros n pts hsl Hsort Hnp.
revert pts hsl Hsort Hnp.
induction n; intros; [ subst hsl; constructor | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ subst hsl; constructor | idtac ].
apply Sorted_LocallySorted_iff.
destruct pts as [| pt₂]; [ subst hsl; constructor | idtac ].
remember (minimise_slope pt₁ pt₂ pts) as ms₂.
remember (next_ch_points n [end_pt ms₂ … rem_pts ms₂]) as hsl₁.
subst hsl.
symmetry in Heqhsl₁.
remember Heqhsl₁ as Hch; clear HeqHch.
apply IHn in Heqhsl₁.
 destruct hsl₁ as [| (pt₃, sg)]; [ constructor | idtac ].
 constructor.
  apply Sorted_LocallySorted_iff; assumption.

  unfold hs_x_lt; simpl.
  symmetry in Heqms₂.
  remember Heqms₂ as Hms; clear HeqHms.
  apply minimise_slope_le in Heqms₂.
   eapply Qlt_le_trans.
    apply Sorted_inv_2 in Hsort; destruct Hsort; eassumption.

    eapply Qle_trans; [ eassumption | idtac ].
    apply next_ch_points_hd in Hch.
    rewrite Hch; apply Qle_refl.

   apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.

 symmetry in Heqms₂.
 eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lower_convex_hull_points_sorted : ∀ pts hsl,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = hsl
    → Sorted hs_x_lt hsl.
Proof.
intros pts hsl Hsort Hch.
eapply next_points_sorted; eassumption.
Qed.

Lemma minimised_slope : ∀ pt₁ pt₂ pt pts ms,
  minimise_slope pt₁ pt pts = ms
  → pt₂ = end_pt ms
    → slope ms == slope_expr pt₁ pt₂.
Proof.
intros pt₁ pt₂ pt pts ms Hms Hkps.
revert pt₁ pt₂ pt ms Hms Hkps.
induction pts as [| pt₃]; intros.
 subst ms; simpl in Hkps |- *; subst pt; reflexivity.

 simpl in Hms.
 remember (minimise_slope pt₁ pt₃ pts) as ms₁.
 remember (slope_expr pt₁ pt ?= slope ms₁) as c.
 symmetry in Heqms₁.
 destruct c; subst ms; simpl in Hkps |- *.
  eapply IHpts; eassumption.

  subst pt₂; reflexivity.

  eapply IHpts; eassumption.
Qed.

Lemma end_pt_in : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → end_pt ms ∈ [pt₂ … pts].
Proof.
intros pt₁ pt₂ pts ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts as [| pt₃]; intros.
 subst ms; simpl.
 left; reflexivity.

 simpl in Hms.
 remember (minimise_slope pt₁ pt₃ pts) as ms₁.
 rename Heqms₁ into Hms₁.
 symmetry in Hms₁.
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 remember (end_pt ms) as pt.
 destruct c; subst ms; simpl in Heqpt; subst pt.
  right; eapply IHpts; eassumption.

  left; reflexivity.

  right; eapply IHpts; eassumption.
Qed.

Lemma rem_pts_in : ∀ pt₁ pt₂ pts₂ ms pt,
  minimise_slope pt₁ pt₂ pts₂ = ms
  → pt ∈ rem_pts ms
    → pt ∈ pts₂.
Proof.
intros pt₁ pt₂ pts₂ ms pt Hms Hpt.
revert pt₁ pt₂ ms Hms Hpt.
induction pts₂ as [| pt₃]; intros; [ subst ms; contradiction | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts₂) as ms₁.
symmetry in Heqms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; simpl in Hpt.
 right; eapply IHpts₂; eassumption.

 assumption.

 right; eapply IHpts₂; eassumption.
Qed.
