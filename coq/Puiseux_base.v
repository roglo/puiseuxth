(* Puiseux_base.v *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Nbar.
Require Import Qbar.
Require Import Newton.
Require Import Field.
Require Import Fpolynomial.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Import Ps_mul.
Require Import Ps_div.

Set Implicit Arguments.

Definition valuation {α} {r : ring α} ps :=
  match null_coeff_range_length r (ps_terms ps) 0 with
  | fin v => qfin (ps_valnum ps + Z.of_nat v # ps_polord ps)
  | ∞ => qinf
  end.

Definition valuation_coeff α (r : ring α) ps :=
  match null_coeff_range_length r (ps_terms ps) 0 with
  | fin v => (ps_terms ps) .[v]
  | ∞ => (0)%K
  end.

Fixpoint power_list α pow (psl : list (puiseux_series α)) :=
  match psl with
  | [] => []
  | [ps] => [(pow, ps)]
  | [ps₁ … psl₁] => [(pow, ps₁) … power_list (S pow) psl₁]
  end.

Definition qpower_list α pow (psl : list (puiseux_series α)) :=
  List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow psl).

Fixpoint filter_finite_val α (r : ring α) (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation ps with
      | qfin v => [(pow, v) … filter_finite_val r dpl₁]
      | qinf => filter_finite_val r dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen α r pow (cl : list (puiseux_series α)) :=
  filter_finite_val r (qpower_list pow cl).

Definition points_of_ps_lap α r (lps : list (puiseux_series α)) :=
  points_of_ps_polynom_gen r 0 lps.

Definition points_of_ps_polynom α r (pol : polynomial (puiseux_series α)) :=
  points_of_ps_lap r (al pol).

Definition newton_segments α r (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom r pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Section theorems.

Variable α : Type.
Variable r : ring α.

Lemma fold_points_of_ps_polynom_gen : ∀ pow (cl : list (puiseux_series α)),
  filter_finite_val r
    (List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow cl)) =
  points_of_ps_polynom_gen r pow cl.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ deg (cl : list (puiseux_series α)) pts,
  pts = points_of_ps_polynom_gen r deg cl
  → Sorted fst_lt pts.
Proof.
intros deg cl pts Hpts.
destruct cl as [| c₁]; [ subst pts; constructor | idtac ].
revert deg c₁ pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation c₁); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation c₁) as [q | ]; [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_polynom_gen r (S deg) [c … cl]) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c₁.
 revert deg c q pts Hpts.
 induction cl as [| c₂]; intros.
  simpl.
  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  destruct (valuation c).
   constructor; constructor; [ constructor | constructor | idtac ].
   apply Qnat_lt, lt_n_Sn.

   constructor; constructor.

  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts; simpl.
  destruct (valuation c) as [v₂| ].
   subst pts.
   apply Sorted_LocallySorted_iff.
   constructor; [ idtac | apply Qnat_lt, lt_n_Sn ].
   apply Sorted_LocallySorted_iff.
   eapply IHcl; reflexivity.

   eapply IHcl with (q := q) in Hpts.
   apply Sorted_minus_2nd with (x₂ := (Qnat (S deg), q)).
    unfold fst_lt.
    intros x y z; apply Qlt_trans.

    constructor; [ assumption | constructor; apply Qnat_lt, lt_n_Sn ].
Qed.

End theorems.
