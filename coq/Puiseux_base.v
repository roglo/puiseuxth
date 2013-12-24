(* $Id: Puiseux_base.v,v 2.10 2013-12-19 23:59:27 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Newton.
Require Import Polynomial.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Import Nbar.
Require Power_series.
Import Power_series.M.

Set Implicit Arguments.

Definition valuation ps :=
  match null_coeff_range_length rng (ps_terms ps) 0 with
  | fin v => Some (ps_valnum ps + Z.of_nat v # ps_polord ps)
  | ∞ => None
  end.

Definition valuation_coeff ps :=
  match null_coeff_range_length rng (ps_terms ps) 0 with
  | fin v => Some (series_nth rng v (ps_terms ps))
  | ∞ => None
  end.

Fixpoint power_list α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(pow, ps₁) … power_list (S pow) psl₁ psn]
  | [] =>
      [(pow, psn)]
  end.

Definition qpower_list α pow psl (psn : puiseux_series α) :=
  List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow psl psn).

Fixpoint filter_finite_val (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation ps with
      | Some v => [(pow, v) … filter_finite_val dpl₁]
      | None => filter_finite_val dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen pow cl (cn : puiseux_series α) :=
  filter_finite_val (qpower_list pow cl cn).

Definition points_of_ps_polynom (pol : polynomial (puiseux_series α)) :=
  points_of_ps_polynom_gen 0 (al pol) (an pol).

Definition newton_segments (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Lemma fold_points_of_ps_polynom_gen : ∀ pow cl (cn : puiseux_series α),
  filter_finite_val
    (List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow cl cn)) =
  points_of_ps_polynom_gen pow cl cn.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ deg cl (cn : puiseux_series α) pts,
  pts = points_of_ps_polynom_gen deg cl cn
  → Sorted fst_lt pts.
Proof.
intros deg cl cn pts Hpts.
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
