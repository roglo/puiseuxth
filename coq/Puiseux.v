(* $Id: Puiseux.v,v 1.476 2013-05-15 13:23:49 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import ConvexHull.
Require Import ConvexHullMisc.
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

(* *)

Lemma fold_points_of_ps_polynom_gen : ∀ α fld pow cl cn,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn) =
  points_of_ps_polynom_gen α fld pow cl cn.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ α fld deg cl cn pts,
  pts = points_of_ps_polynom_gen α fld deg cl cn
  → Sorted fst_lt pts.
Proof.
intros α fld deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (is_zero_dec fld cn); subst pts; constructor; constructor.

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
    subst pts; constructor; constructor.

    subst pts.
    apply Sorted_LocallySorted_iff.
    constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
   rewrite fold_points_of_ps_polynom_gen in Hpts.
   destruct (is_zero_dec fld c₂) as [Heq| Hne].
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
