(* $Id: Puiseux.v,v 1.471 2013-05-10 15:00:35 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import Sorting.
Require Import Misc.
Require Streams.

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

Record Qpos := { x : Q; pos : x > 0 }.

Record puiseux_series α :=
  { ps_1 : α * Q;
    ps_n : Streams.Stream (α * Qpos) }.

Definition valuation α ps := snd (ps_1 α ps).
Definition valuation_coeff α ps := fst (ps_1 α ps).

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(Qnat pow, ps₁) … all_points_of_ps_polynom α (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end.

Fixpoint filter_non_zero_ps α fld (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      if is_zero_dec fld ps then filter_non_zero_ps α fld dpl₁
      else [(pow, valuation α ps) … filter_non_zero_ps α fld dpl₁]
  | [] =>
      []
  end.

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

Record newton_segment := mkns
  { γ : Q;
    β : Q;
    ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) }.

Definition newton_segment_of_pair hsj hsk :=
  let αj := snd (pt hsj) in
  let αk := snd (pt hsk) in
  let γ := (αj - αk) / (fst (pt hsk) - fst (pt hsj)) in
  let β := αj + fst (pt hsj) * γ in
  mkns γ β (pt hsj) (pt hsk) (oth hsj).

Definition newton_segments α fld pol :=
  let gdpl := points_of_ps_polynom α fld pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).
Arguments newton_segments : default implicits.

Section convex_hull.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma fold_slope_expr : ∀ x₁ y₁ x₂ y₂,
  (y₂ - y₁) / (x₂ - x₁) = slope_expr (x₁, y₁) (x₂, y₂).
Proof. reflexivity. Qed.

Lemma fold_points_of_ps_polynom_gen : ∀ pow cl cn,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn) =
  points_of_ps_polynom_gen α fld pow cl cn.
Proof. reflexivity. Qed.

Definition fst_lt (x y : Q * Q) := (fst x < fst y).
Definition hs_x_lt (x y : hull_seg) := (fst (pt x) < fst (pt y)).

Lemma LSorted_inv_1 {A} : ∀ (f : A → A → Prop) x l,
  LocallySorted f [x … l]
  → LocallySorted f l.
Proof.
intros f x l H.
inversion H; [ constructor | assumption ].
Qed.

Lemma LSorted_inv_2 {A} : ∀ (f : A → A → Prop) x y l,
  LocallySorted f [x; y … l]
  → f x y ∧ LocallySorted f [y … l].
Proof.
intros f x y l H.
inversion H; subst a b l0.
split; assumption.
Qed.

Lemma LSorted_hd : ∀ (pt₁ pt₂ : Q * Q) pts,
  LocallySorted fst_lt [pt₁ … pts]
  → pt₂ ∈ pts
    → fst pt₁ < fst pt₂.
Proof.
intros pt₁ pt₂ pts Hsort Hpt.
revert pt₁ pt₂ Hsort Hpt.
induction pts as [| pt]; intros; [ contradiction | idtac ].
apply LSorted_inv_2 in Hsort.
destruct Hsort as (Hlt, Hsort).
destruct Hpt as [Hpt| Hpt]; [ subst pt; assumption | idtac ].
eapply Qlt_trans; [ eassumption | idtac ].
apply IHpts; assumption.
Qed.

Lemma LSorted_minus_2nd {A} : ∀ (f : A → A → Prop) x₁ x₂ xl,
  (∀ x y z, f x y → f y z → f x z)
  → LocallySorted f [x₁; x₂ … xl]
    → LocallySorted f [x₁ … xl].
Proof.
intros f x₁ x₂ l Ht H.
destruct l as [| x₃]; [ constructor | intros ].
constructor.
 do 2 apply LSorted_inv_1 in H.
 assumption.

 apply LSorted_inv_2 in H; destruct H as (Hlt₁, H).
 apply LSorted_inv_2 in H; destruct H as (Hlt₂, H).
 eapply Ht; eassumption.
Qed.

Lemma LSorted_minus_3rd {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ xl,
  (∀ x y z, f x y → f y z → f x z)
  → LocallySorted f [x₁; x₂; x₃ … xl]
    → LocallySorted f [x₁; x₂ … xl].
Proof.
intros f x₁ x₂ x₃ l Ht H.
constructor.
 apply LSorted_inv_1 in H.
 eapply LSorted_minus_2nd; eassumption.

 apply LSorted_inv_2 in H; destruct H; assumption.
Qed.

Lemma LSorted_minus_4th {A} : ∀ (f : A → A → Prop) x₁ x₂ x₃ x₄ xl,
  (∀ x y z, f x y → f y z → f x z)
  → LocallySorted f [x₁; x₂; x₃; x₄ … xl]
    → LocallySorted f [x₁; x₂; x₃ … xl].
Proof.
intros f x₁ x₂ x₃ x₄ l Ht H.
constructor.
 apply LSorted_inv_1 in H.
 eapply LSorted_minus_3rd; eassumption.

 apply LSorted_inv_2 in H; destruct H; assumption.
Qed.

Lemma LSorted_not_in {A} : ∀ (f : A → A → Prop) a b l,
  (∀ x, ¬f x x)
  → (∀ x y z, f x y → f y z → f x z)
    → LocallySorted f [b … l]
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
  apply LSorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
  eapply Htran in Hab; [ eapply Hirr, Hab | eassumption ].

  apply IHl; [ idtac | assumption ].
  eapply LSorted_minus_2nd; eassumption.
Qed.

(* *)

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
    constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   rewrite fold_points_of_ps_polynom_gen in Hpts.
   destruct (is_zero_dec fld c₂) as [Heq| Hne].
    eapply IHcl with (c := c) in Hpts.
    destruct pts as [| pt]; [ constructor | idtac ].
    apply LSorted_inv_2 in Hpts.
    destruct Hpts as (Hlt, Hpts).
    constructor; [ assumption | idtac ].
    eapply Qlt_trans; [ apply Qnat_lt, lt_n_Sn | eassumption ].

    subst pts.
    constructor; [ eapply IHcl; reflexivity | apply Qnat_lt, lt_n_Sn ].
Qed.

Lemma minimise_slope_le : ∀ pt₁ pt₂ pts₂ ms,
  LocallySorted fst_lt [pt₂ … pts₂]
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
  apply LSorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Qlt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.

  apply Qlt_le_weak.
  apply LSorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Qlt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.
Qed.

Lemma next_ch_points_le : ∀ n pt₁ pt₂ pts₁ sg hsl,
  next_ch_points n [pt₁ … pts₁] = [{| pt := pt₂; oth := sg |} … hsl]
  → fst pt₁ <= fst pt₂.
Proof.
intros n pt₁ pt₂ pts₁ sg hsl Hnp.
destruct n; [ discriminate Hnp | idtac ].
simpl in Hnp.
destruct pts₁; injection Hnp; intros; subst pt₁; apply Qle_refl.
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
  LocallySorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
    → LocallySorted fst_lt [end_pt ms … rem_pts ms].
Proof.
intros pt₁ pt₂ pts ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros; [ subst ms; constructor | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqms₁.
apply LSorted_inv_2 in Hsort.
destruct Hsort as (Hlt₁, Hsort).
destruct c; subst ms; simpl; [ idtac | assumption | idtac ].
 eapply IHpts; [ idtac | eassumption ].
 apply LSorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 constructor; [ assumption | eapply Qlt_trans; eassumption ].

 eapply IHpts; [ idtac | eassumption ].
 apply LSorted_inv_2 in Hsort.
 destruct Hsort as (Hlt₂, Hsort).
 constructor; [ assumption | eapply Qlt_trans; eassumption ].
Qed.

Lemma next_points_sorted : ∀ n pts hsl,
  LocallySorted fst_lt pts
  → next_ch_points n pts = hsl
    → LocallySorted hs_x_lt hsl.
Proof.
intros n pts hsl Hsort Hnp.
revert pts hsl Hsort Hnp.
induction n; intros; [ subst hsl; constructor | idtac ].
simpl in Hnp.
destruct pts as [| pt₁]; [ subst hsl; constructor | idtac ].
destruct pts as [| pt₂]; [ subst hsl; constructor | idtac ].
remember (minimise_slope pt₁ pt₂ pts) as ms₂.
remember (next_ch_points n [end_pt ms₂ … rem_pts ms₂]) as hsl₁.
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
  eapply Qlt_le_trans.
   apply LSorted_inv_2 in Hsort; destruct Hsort; eassumption.

   eapply Qle_trans; [ eassumption | idtac ].
   eapply next_ch_points_le; eassumption.

  apply LSorted_inv_2 in Hsort; destruct Hsort; assumption.

 symmetry in Heqms₂.
 eapply minimise_slope_sorted; eassumption.
Qed.

Lemma lower_convex_hull_points_sorted : ∀ pts hsl,
  LocallySorted fst_lt pts
  → lower_convex_hull_points pts = hsl
    → LocallySorted hs_x_lt hsl.
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

End convex_hull.
