(* $Id: Puiseux.v,v 1.464 2013-05-07 00:27:31 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.
Require Import Misc.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

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

(*
Definition apply_poly {α} fld pol (x : α) :=
  List.fold_right (λ accu coeff, add fld (mul fld accu x) coeff) (an pol)
    (al pol).
Arguments apply_poly : default implicits. 

Record alg_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol x, @apply_poly α ac_field pol x = zero ac_field }.
Arguments ac_field : default implicits. 
Arguments ac_prop : default implicits. 
*)

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

Definition newton_segment_of_pair α hsj hsk :=
  let αj := valuation α (snd (pt hsj)) in
  let αk := valuation α (snd (pt hsk)) in
  let γ := (αj - αk) / Qnat (fst (pt hsk) - fst (pt hsj))%nat in
  let β := αj + Qnat (fst (pt hsj)) * γ in
  mkns α γ β (pt hsj) (pt hsk) (oth hsj).

Definition newton_segments α fld pol :=
  let gdpl := points_of_ps_polynom α fld pol in
  list_map_pairs (newton_segment_of_pair α) (lower_convex_hull_points α gdpl).
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

Lemma Sorted_minus_2nd {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ xl,
  (∀ x y z, f x y → f y z → f x z)
  → LocallySorted f [x₁; x₂; x₃ … xl]
    → LocallySorted f [x₁; x₃ … xl].
Proof.
intros f x₁ x₂ x₃ l Ht H.
constructor.
 do 2 eapply LocallySorted_inv_1; eassumption.

 apply LocallySorted_inv_2 in H; destruct H as (Hf, H).
 apply LocallySorted_inv_2 in H; destruct H.
 eapply Ht; eassumption.
Qed.

Lemma Sorted_minus_3rd {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ x₄ xl,
  (∀ x y z, f x y → f y z → f x z)
  → LocallySorted f [x₁; x₂; x₃; x₄ … xl]
    → LocallySorted f [x₁; x₂; x₄ … xl].
Proof.
intros f x₁ x₂ x₃ x₄ l Ht H.
constructor.
 constructor.
  do 3 eapply LocallySorted_inv_1; eassumption.

  apply LocallySorted_inv_2 in H; destruct H as (Hf₁, H).
  apply LocallySorted_inv_2 in H; destruct H as (Hf₂, H).
  apply LocallySorted_inv_2 in H; destruct H as (Hf₃, H).
  eapply Ht; eassumption.

 apply LocallySorted_inv_2 in H; destruct H; assumption.
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

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pts₁ sg hsl,
  next_ch_points α n [pt₁ … pts₁] = [{| pt := pt₂; oth := sg |} … hsl]
  → fst pt₁ ≤ fst pt₂.
Proof.
intros n pt₁ pt₂ pts₁ sg hsl Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts₁; injection Hnp; intros; subst pt₁; reflexivity.
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

Lemma minimised_slope : ∀ pt₁ pt₂ pt pts ms,
  minimise_slope α pt₁ pt pts = ms
  → pt₂ = end_pt ms
    → slope ms == slope_expr α pt₁ pt₂.
Proof.
intros pt₁ pt₂ pt pts ms Hms Hkps.
revert pt₁ pt₂ pt ms Hms Hkps.
induction pts as [| pt₃]; intros.
 subst ms; simpl in Hkps |- *; subst pt; reflexivity.

 simpl in Hms.
 remember (minimise_slope α pt₁ pt₃ pts) as ms₁.
 remember (slope_expr α pt₁ pt ?= slope ms₁) as c.
 symmetry in Heqms₁.
 destruct c; subst ms; simpl in Hkps |- *.
  eapply IHpts; eassumption.

  subst pt₂; reflexivity.

  eapply IHpts; eassumption.
Qed.

End convex_hull.
