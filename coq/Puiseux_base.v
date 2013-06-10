(* $Id: Puiseux_base.v,v 1.18 2013-06-10 09:58:54 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Series.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
(*
    sub : α → α → α;
*)
    mul : α → α → α
(*
    div : α → α → α
*)
}.

(* polynomial of degree ≥ 0 *)
Record polynomial α := mkpol { al : list α; an : α }.

Record term α := { coeff : α; power : Q }.

(* [series_head] skip the possible terms with null coefficients and return
   the sub-series of the initial series whose coefficient of the first term
   is not null. E.g.: applied to
       0+0x³+5x⁵+0x⁷+3x⁸+...
   would return
       5x⁵+0x⁷+3x⁸+...

   Supposes axiomatically
   - the decidability of equality of Puiseux series
   - the decidability of equality of Puiseux terms coefficients.

   Without this axiom, the root of a polynomial on Puiseux's series is not
   computable (therefore proof not constructive). *)
Axiom series_head : ∀ α, series (term α) → series (term α).

Definition pow_den_div_com_den α comden (t : term α) :=
  ∃ k, Pos.to_nat (Qden (power t)) = (k * comden)%nat.

Record puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : nat;
    ps_prop : series_forall (pow_den_div_com_den ps_comden) ps_terms }.

Definition valuation α (ps : puiseux_series α) :=
  match series_head (ps_terms ps) with
  | Term mx _ => Some (power mx)
  | End => None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (ps_terms ps) with
  | Term mx _ => coeff mx
  | End => zero fld
  end.

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(Qnat pow, ps₁) … all_points_of_ps_polynom (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end.

Fixpoint filter_non_zero_ps α (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation ps with
      | Some v => [(pow, v) … filter_non_zero_ps dpl₁]
      | None => filter_non_zero_ps dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen α pow cl (cn : puiseux_series α) :=
  filter_non_zero_ps (all_points_of_ps_polynom pow cl cn).

Definition points_of_ps_polynom α (pol : polynomial (puiseux_series α)) :=
  points_of_ps_polynom_gen 0%nat (al pol) (an pol).

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

Definition newton_segments α (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Lemma fold_points_of_ps_polynom_gen : ∀ α pow cl (cn : puiseux_series α),
  filter_non_zero_ps (all_points_of_ps_polynom pow cl cn) =
  points_of_ps_polynom_gen pow cl cn.
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

Lemma points_of_polyn_sorted : ∀ α deg cl (cn : puiseux_series α) pts,
  pts = points_of_ps_polynom_gen deg cl cn
  → Sorted fst_lt pts.
Proof.
intros α deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation cn); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 rewrite fold_points_of_ps_polynom_gen in Hpts.
 destruct (valuation c); [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_polynom_gen (S deg) cl cn) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c.
 revert deg cn q pts Hpts.
 induction cl as [| c₂]; intros.
  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  destruct (valuation cn).
   subst pts.
   apply Sorted_LocallySorted_iff.
   constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   subst pts; constructor; constructor.

  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  rewrite fold_points_of_ps_polynom_gen in Hpts.
  destruct (valuation c₂) as [v₂| ].
   subst pts.
   apply Sorted_LocallySorted_iff.
   constructor; [ idtac | apply Qnat_lt, lt_n_Sn ].
   apply Sorted_LocallySorted_iff.
   eapply IHcl; reflexivity.

   eapply IHcl with (q := q) in Hpts.
   apply Sorted_LocallySorted_iff.
   destruct pts as [| pt]; [ constructor | idtac ].
   apply Sorted_LocallySorted_iff.
   apply Sorted_inv_2 in Hpts.
   destruct Hpts as (Hlt, Hpts).
   apply Sorted_LocallySorted_iff.
   apply Sorted_LocallySorted_iff in Hpts.
   constructor; [ assumption | idtac ].
   eapply Qlt_trans; [ apply Qnat_lt, lt_n_Sn | eassumption ].
Qed.
