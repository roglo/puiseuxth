(* $Id: Puiseux_base.v,v 1.37 2013-07-03 19:18:29 deraugla Exp $ *)

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

Set Implicit Arguments.

Fixpoint power_list α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(Qnat pow, ps₁) … power_list (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end.

Fixpoint filter_finite_val α fld (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation fld ps with
      | Some v => [(pow, v) … filter_finite_val fld dpl₁]
      | None => filter_finite_val fld dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen α fld pow cl (cn : puiseux_series α) :=
  filter_finite_val fld (power_list pow cl cn).

Definition points_of_ps_polynom α fld (pol : polynomial (puiseux_series α)) :=
  points_of_ps_polynom_gen fld 0%nat (al pol) (an pol).

Definition newton_segments α fld (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom fld pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Lemma fold_points_of_ps_polynom_gen : ∀ α fld pow cl (cn : puiseux_series α),
  filter_finite_val fld (power_list pow cl cn) =
  points_of_ps_polynom_gen fld pow cl cn.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ α fld deg cl (cn : puiseux_series α) pts,
  pts = points_of_ps_polynom_gen fld deg cl cn
  → Sorted fst_lt pts.
Proof.
intros α fld deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation fld cn); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 rewrite fold_points_of_ps_polynom_gen in Hpts.
 destruct (valuation fld c); [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_polynom_gen fld (S deg) cl cn) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c.
 revert deg cn q pts Hpts.
 induction cl as [| c₂]; intros.
  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  destruct (valuation fld cn).
   subst pts.
   apply Sorted_LocallySorted_iff.
   constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   subst pts; constructor; constructor.

  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  rewrite fold_points_of_ps_polynom_gen in Hpts.
  destruct (valuation fld c₂) as [v₂| ].
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
