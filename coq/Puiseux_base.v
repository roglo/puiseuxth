(* Puiseux_base.v *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Newton.
Require Import Polynomial.
Require Import Nbar.
Require Import Field.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Import Ps_mul.
Require Import Ps_div.

Set Implicit Arguments.

Definition valuation α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) 0 with
  | fin v => Some (ps_valnum ps + Z.of_nat v # ps_polord ps)
  | ∞ => None
  end.

Definition valuation_coeff α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) 0 with
  | fin v => series_nth f v (ps_terms ps)
  | ∞ => (.0 f)%F
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

Fixpoint filter_finite_val α f (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation f ps with
      | Some v => [(pow, v) … filter_finite_val f dpl₁]
      | None => filter_finite_val f dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen α f pow cl (cn : puiseux_series α) :=
  filter_finite_val f (qpower_list pow cl cn).

Definition points_of_ps_polynom α f (pol : polynomial (puiseux_series α)) :=
  points_of_ps_polynom_gen f 0 (al pol) (an pol).

Definition newton_segments α f (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom f pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Section theorems.

Variable α : Type.
Variable f : field α.

Lemma fold_points_of_ps_polynom_gen : ∀ pow cl (cn : puiseux_series α),
  filter_finite_val f
    (List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow cl cn)) =
  points_of_ps_polynom_gen f pow cl cn.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ deg cl (cn : puiseux_series α) pts,
  pts = points_of_ps_polynom_gen f deg cl cn
  → Sorted fst_lt pts.
Proof.
intros deg cl cn pts Hpts.
revert deg cn pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation f cn); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 rewrite fold_points_of_ps_polynom_gen in Hpts.
 destruct (valuation f c); [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_polynom_gen f (S deg) cl cn) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c.
 revert deg cn q pts Hpts.
 induction cl as [| c₂]; intros.
  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  destruct (valuation f cn).
   subst pts.
   apply Sorted_LocallySorted_iff.
   constructor; [ constructor | apply Qnat_lt, lt_n_Sn ].

   subst pts; constructor; constructor.

  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  rewrite fold_points_of_ps_polynom_gen in Hpts.
  destruct (valuation f c₂) as [v₂| ].
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

End theorems.
