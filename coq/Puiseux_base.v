(* $Id: Puiseux_base.v,v 1.8 2013-05-23 13:56:39 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Sorting.
Require Import Misc.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    mul : α → α → α;
    div : α → α → α;
    is_zero : α → bool }.

(* polynomial of degree ≥ 0 *)
Record polynomial α := mkpol { al : list α; an : α }.

Record Qpos := { x : Q; pos : x > 0 }.

Record ps_monomial α := { coeff : α; power : Q }.

CoInductive series α := Cons : α → series α → series α | End : series α.

Record puiseux_series α := { ps_monoms : series (ps_monomial α) }.

Definition valuation α (ps : puiseux_series α) :=
  match ps_monoms ps with
  | Cons mx _ => power mx
  | End => 1 / 0
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match ps_monoms ps with
  | Cons mx _ => coeff mx
  | End => zero fld
  end.

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(Qnat pow, ps₁) … all_points_of_ps_polynom (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end.

Fixpoint filter_non_zero_ps α fld (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      if is_zero fld ps then filter_non_zero_ps fld dpl₁
      else [(pow, valuation ps) … filter_non_zero_ps fld dpl₁]
  | [] =>
      []
  end.

Definition fps α := field (puiseux_series α).

Definition points_of_ps_polynom_gen α (fld : fps α) pow cl
    cn :=
  filter_non_zero_ps fld (all_points_of_ps_polynom pow cl cn).

Definition points_of_ps_polynom α (fld : fps α) pol :=
  points_of_ps_polynom_gen fld 0%nat (al pol) (an pol).

Fixpoint list_map_pairs α β (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ … ([x₂ … l₂] as l₁)] => [f x₁ x₂ … list_map_pairs f l₁]
  end.

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

Definition newton_segments α (fld : fps α) pol :=
  let gdpl := points_of_ps_polynom fld pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

(* *)

Lemma fold_points_of_ps_polynom_gen : ∀ α (fld : fps α) pow cl cn,
  filter_non_zero_ps fld (all_points_of_ps_polynom pow cl cn) =
  points_of_ps_polynom_gen fld pow cl cn.
Proof. reflexivity. Qed.

Lemma list_map_pairs_length {A B} : ∀ (f : A → A → B) l₁ l₂,
  list_map_pairs f l₁ = l₂
  → List.length l₂ = pred (List.length l₁).
Proof.
intros f l₁ l₂ H.
subst l₂.
destruct l₁ as [| x]; [ reflexivity | idtac ].
revert x.
induction l₁ as [| y]; [ reflexivity | intros ].
simpl in IHl₁ |- *.
apply eq_S, IHl₁.
Qed.

Lemma points_of_polyn_sorted : ∀ α (fld : fps α) deg cl cn pts,
  pts = points_of_ps_polynom_gen fld deg cl cn
  → Sorted fst_lt pts.
Proof.
intros α fld deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (is_zero fld cn); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 rewrite fold_points_of_ps_polynom_gen in Hpts.
 destruct (is_zero fld c) as [Heq| Hne].
  eapply IHcl; eassumption.

  remember (points_of_ps_polynom_gen fld (S deg) cl cn) as pts₁.
  subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
  clear IHcl.
  revert c deg cn pts Hpts.
  induction cl as [| c₂]; intros.
   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   destruct (is_zero fld cn) as [Heq| Hne].
    subst pts; constructor; constructor.

    subst pts.
    apply Sorted_LocallySorted_iff.
    constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   rewrite fold_points_of_ps_polynom_gen in Hpts.
   destruct (is_zero fld c₂) as [Heq| Hne].
    eapply IHcl with (c := c) in Hpts.
    apply Sorted_LocallySorted_iff.
    destruct pts as [| pt]; [ constructor | idtac ].
    apply Sorted_LocallySorted_iff.
    apply Sorted_inv_2 in Hpts.
    destruct Hpts as (Hlt, Hpts).
    apply Sorted_LocallySorted_iff.
    apply Sorted_LocallySorted_iff in Hpts.
    constructor; [ assumption | idtac ].
    eapply Qlt_trans; [ apply Qnat_lt, lt_n_Sn | eassumption ].

    subst pts.
    apply Sorted_LocallySorted_iff.
    constructor; [ idtac | apply Qnat_lt, lt_n_Sn ].
    apply Sorted_LocallySorted_iff.
    eapply IHcl; reflexivity.
Qed.
