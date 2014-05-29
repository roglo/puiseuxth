(* ConvexHullMisc.v *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.

Require Import Misc.
Require Import ConvexHull.
Require Import Slope_base.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Definition fst_lt (x y : Q * Q) := (fst x < fst y).
(*
Definition hs_x_lt (x y : hull_seg) := (fst (vert x) < fst (vert y)).
*)
Definition hs_x_lt (x y : newton_segment) :=
  (fst (ini_pt x) < fst (ini_pt y)).

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

Lemma Sorted_app_at_r : ∀ α f l (x : α),
  Sorted f l
  → (∀ y, y ∈ l → f y x)
    → Sorted f (l ++ [x]).
Proof.
clear; intros α f l x Hs Hf.
induction l as [| z]; [ constructor; constructor | simpl ].
apply Sorted_inv in Hs.
destruct Hs as (Hs, Hr).
apply IHl in Hs.
 constructor; [ assumption | idtac ].
 destruct l as [| t].
  constructor; apply Hf; left; reflexivity.

  constructor; apply HdRel_inv in Hr; assumption.

 intros y Hy.
 apply Hf; right; assumption.
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

Lemma Sorted_map : ∀ A B P (Q : A → B) (l : list A),
  Sorted (λ x y, P (Q x) (Q y)) l
  → Sorted P (List.map Q l).
Proof.
intros A B P Q l Hsort.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction l as [| a]; [ constructor | simpl ].
destruct l as [| b]; simpl; constructor.
 apply IHl.
 inversion Hsort; subst; assumption.

 inversion Hsort; subst; assumption.
Qed.

Lemma Sorted_trans_app : ∀ A (g : A → A → Prop) x y l,
  (∀ x y z, g x y → g y z → g x z)
  → x ∈ l
    → Sorted g (l ++ [y])
      → g x y.
Proof.
intros A g x y l Htrans Hx Hsort.
apply Sorted_LocallySorted_iff in Hsort.
revert x y Hx Hsort.
induction l as [| z]; intros; [ contradiction | idtac ].
simpl in Hsort.
inversion Hsort.
 symmetry in H1.
 apply List.app_eq_nil in H1.
 destruct H1 as (_, H); discriminate H.

 subst.
 destruct Hx as [Hx| Hx].
  subst z.
  destruct l as [| z].
   simpl in H0.
   injection H0; clear H0; intros; subst.
   assumption.

   eapply Htrans; [ eassumption | idtac ].
   apply IHl.
    simpl in H0.
    injection H0; clear H0; intros; subst.
    left; reflexivity.

    rewrite <- H0; assumption.

  apply IHl; [ assumption | idtac ].
  rewrite <- H0; assumption.
Qed.

Lemma HdRel_app : ∀ A (R : A → A → Prop) a l₁ l₂,
  HdRel R a l₁
  → HdRel R a l₂
    → HdRel R a (l₁ ++ l₂).
Proof.
intros A R a l₁ l₂ H₁ H₂.
destruct l₁ as [| b]; [ assumption | constructor ].
apply HdRel_inv in H₁; assumption.
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

Lemma next_ch_points_hd : ∀ n pt₁ pt₂ pt₃ pts₁ seg hsl,
  next_ch_points n [pt₁ … pts₁] = [mkns pt₂ pt₃ seg … hsl]
  → pt₁ = pt₂.
Proof.
intros n pt₁ pt₂ pt₃ pts₂ seg₂ hsl Hnp.
revert pt₁ pt₂ pt₃ pts₂ seg₂ hsl Hnp.
induction n; intros; [ discriminate Hnp | simpl in Hnp ].
destruct pts₂ as [| pts₄]; [ discriminate Hnp | idtac ].
injection Hnp; intros; subst pt₂; reflexivity.
Qed.

Lemma minimise_slope_rem_length : ∀ pt₁ pt₂ pts ms n,
  (length pts < n)%nat
  → ms = minimise_slope pt₁ pt₂ pts
  → (length (rem_pts ms) < n)%nat.
Proof.
intros pt₁ pt₂ pts ms n Hlen Hms.
revert pt₁ pt₂ n ms Hlen Hms.
induction pts as [| pt]; intros.
 subst ms; assumption.

 simpl in Hms.
 remember (minimise_slope pt₁ pt pts) as ms₁ eqn:Hms₁ .
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c eqn:Hc .
 symmetry in Hc.
 rewrite slope_slope_expr in Hc; [ idtac | symmetry; eassumption ].
 subst ms.
 destruct c; simpl.
  eapply IHpts; try eassumption.
  apply lt_S_n, lt_S; assumption.

  assumption.

  eapply IHpts; try eassumption.
  apply lt_S_n, lt_S; assumption.
Qed.

Lemma minimise_slope_length : ∀ pt₁ pt₂ pts ms n,
  length [pt₁; pt₂ … pts] ≤ S n
  → ms = minimise_slope pt₁ pt₂ pts
  → length [end_pt ms … rem_pts ms] ≤ n.
Proof.
intros pt₁ pt₂ pts ms n Hlen Hms.
simpl in Hlen; simpl.
apply le_S_n in Hlen.
eapply minimise_slope_rem_length; eassumption.
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

Lemma beg_lt_end_pt : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
  → fst (beg_pt ms) < fst (end_pt ms).
Proof.
intros pt₁ pt₂ pts ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros.
 subst ms; simpl.
 eapply Sorted_hd; [ eassumption | left; reflexivity ].

 simpl in Hms.
 remember (minimise_slope pt₁ pt₃ pts) as ms₁ eqn:Hms₁ .
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
 symmetry in Heqc.
 symmetry in Hms₁.
 rewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
 destruct c.
  subst ms; simpl.
  rewrite <- minimised_slope_beg_pt in |- * at 1.
  rewrite <- Hms₁.
  eapply IHpts; [ idtac | reflexivity ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms; simpl.
  eapply Sorted_hd; [ eassumption | left; reflexivity ].

  subst ms₁.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma ini_lt_fin_pt : ∀ pts ns n,
  Sorted fst_lt pts
  → ns ∈ next_ch_points n pts
  → fst (ini_pt ns) < fst (fin_pt ns).
Proof.
intros pts ns n Hsort Hns.
remember (next_ch_points n pts) as nsl eqn:Hnsl .
revert pts ns n Hsort Hnsl Hns.
induction nsl as [| ns₁]; intros; [ contradiction | idtac ].
simpl in Hns.
destruct Hns as [Hns| Hns].
 subst ns₁.
 destruct n; [ discriminate Hnsl | simpl in Hnsl ].
 destruct pts as [| pt₁]; [ discriminate Hnsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnsl | idtac ].
 injection Hnsl; clear Hnsl; intros Hnsl Hns.
 subst ns; simpl.
 remember (minimise_slope pt₁ pt₂ pts) as ms eqn:Hms .
 assert (pt₁ = beg_pt ms) as H.
  rewrite Hms, minimised_slope_beg_pt; reflexivity.

  rewrite H.
  symmetry in Hms.
  eapply beg_lt_end_pt; eassumption.

 destruct n; [ discriminate Hnsl | simpl in Hnsl ].
 destruct pts as [| pt₁]; [ discriminate Hnsl | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnsl | idtac ].
 injection Hnsl; clear Hnsl; intros Hnsl Hns₁.
 eapply IHnsl; [ idtac | eassumption | assumption ].
 eapply minimise_slope_sorted; [ eassumption | reflexivity ].
Qed.

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pt₃ pts₁ sg hsl₁ hsl,
  Sorted fst_lt [pt₁ … pts₁]
  → next_ch_points n [pt₁ … pts₁] = hsl₁ ++ [mkns pt₂ pt₃ sg … hsl]
    → fst pt₁ <= fst pt₂.
Proof.
intros n pt₁ pt₂ pt₃ pts₁ sg hsl₁ hsl Hsort Hnp.
revert n pt₁ pt₂ pt₃ pts₁ sg hsl Hsort Hnp.
induction hsl₁ as [| hs₁]; intros.
 apply next_ch_points_hd in Hnp; subst pt₁; apply Qle_refl.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts₁ as [| pt₄]; intros.
  destruct hsl₁; discriminate Hnp.

  injection Hnp; clear Hnp; intros Hnp; intros.
  subst hs₁.
  remember (minimise_slope pt₁ pt₃ pts₁) as ms₁.
  symmetry in Heqms₁.
  apply IHhsl₁ in Hnp.
   eapply Qle_trans; [ idtac | eassumption ].
   rewrite <- minimised_slope_beg_pt in |- * at 1.
   apply Qlt_le_weak.
   eapply beg_lt_end_pt; [ eassumption | reflexivity ].

   eapply minimise_slope_sorted; try eassumption.
   reflexivity.
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
unfold slope; subst.
rewrite minimised_slope_beg_pt; reflexivity.
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
