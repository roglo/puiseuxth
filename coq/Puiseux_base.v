(* Puiseux_base.v *)

(* Most of notations are Robert Walker's ones *)

Require Import Utf8.
Require Import QArith.
Require Import Sorting.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Nbar.
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

Definition valuation α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) 0 with
  | fin v => Some (ps_valnum ps + Z.of_nat v # ps_polord ps)
  | ∞ => None
  end.

Definition valuation_coeff α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) 0 with
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

Definition points_of_ps_polynom_gen α f pow (cl : list (puiseux_series α)) :=
  filter_finite_val f (qpower_list pow cl).

Definition points_of_ps_lap α f (lps : list (puiseux_series α)) :=
  points_of_ps_polynom_gen f 0 lps.

Definition points_of_ps_polynom α f (pol : polynomial (puiseux_series α)) :=
  points_of_ps_lap f (al pol).

Definition newton_segments α f (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom f pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

Definition puis_ser_pol α := polynomial (puiseux_series α).

(* *)

Section theorems.

Variable α : Type.
Variable f : field α.

Lemma fold_points_of_ps_polynom_gen : ∀ pow (cl : list (puiseux_series α)),
  filter_finite_val f
    (List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow cl)) =
  points_of_ps_polynom_gen f pow cl.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ deg (cl : list (puiseux_series α)) pts,
  pts = points_of_ps_polynom_gen f deg cl
  → Sorted fst_lt pts.
Proof.
intros deg cl pts Hpts.
destruct cl as [| c₁]; [ subst pts; constructor | idtac ].
revert deg c₁ pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation f c₁); subst pts; constructor; constructor.

 unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
 destruct (valuation f c₁); [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_polynom_gen f (S deg) [c … cl]) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c₁.
 revert deg c q pts Hpts.
 induction cl as [| c₂]; intros.
  simpl.
  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts.
  destruct (valuation f c).
   constructor; constructor; [ constructor | constructor | idtac ].
   apply Qnat_lt, lt_n_Sn.

   constructor; constructor.

  unfold points_of_ps_polynom_gen in Hpts; simpl in Hpts; simpl.
  destruct (valuation f c) as [v₂| ].
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
