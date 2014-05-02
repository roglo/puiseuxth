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

Definition order {α} {r : ring α} ps :=
  match null_coeff_range_length r (ps_terms ps) 0 with
  | fin v => qfin (ps_ordnum ps + Z.of_nat v # ps_polord ps)
  | ∞ => qinf
  end.

Arguments order _ _ ps%ps_scope.

Definition order_coeff α (r : ring α) ps :=
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

Fixpoint filter_finite_ord α (r : ring α) (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match order ps with
      | qfin v => [(pow, v) … filter_finite_ord r dpl₁]
      | qinf => filter_finite_ord r dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_lap_gen α r pow (cl : list (puiseux_series α)) :=
  filter_finite_ord r (qpower_list pow cl).

Definition points_of_ps_lap α r (lps : list (puiseux_series α)) :=
  points_of_ps_lap_gen r 0 lps.

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

Lemma order_inf : ∀ x, order x = qinf ↔ (x = 0)%ps.
Proof.
intros x.
split; intros H.
 apply ps_null_coeff_range_length_inf_iff.
 unfold order in H.
 remember (null_coeff_range_length r (ps_terms x) 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ discriminate H | reflexivity ].

 apply ps_null_coeff_range_length_inf_iff in H.
 unfold order.
 rewrite H; reflexivity.
Qed.

Lemma fold_points_of_ps_polynom_gen : ∀ pow (cl : list (puiseux_series α)),
  filter_finite_ord r
    (List.map (pair_rec (λ pow ps, (Qnat pow, ps))) (power_list pow cl)) =
  points_of_ps_lap_gen r pow cl.
Proof. reflexivity. Qed.

Lemma points_of_polyn_sorted : ∀ deg (cl : list (puiseux_series α)) pts,
  pts = points_of_ps_lap_gen r deg cl
  → Sorted fst_lt pts.
Proof.
intros deg cl pts Hpts.
destruct cl as [| c₁]; [ subst pts; constructor | idtac ].
revert deg c₁ pts Hpts.
induction cl as [| c]; intros.
 unfold points_of_ps_lap_gen in Hpts; simpl in Hpts.
 destruct (order c₁); subst pts; constructor; constructor.

 unfold points_of_ps_lap_gen in Hpts; simpl in Hpts.
 destruct (order c₁) as [q | ]; [ idtac | eapply IHcl; eassumption ].
 remember (points_of_ps_lap_gen r (S deg) [c … cl]) as pts₁.
 subst pts; rename pts₁ into pts; rename Heqpts₁ into Hpts.
 clear IHcl.
 clear c₁.
 revert deg c q pts Hpts.
 induction cl as [| c₂]; intros.
  simpl.
  unfold points_of_ps_lap_gen in Hpts; simpl in Hpts.
  destruct (order c).
   constructor; constructor; [ constructor | constructor | idtac ].
   apply Qnat_lt, lt_n_Sn.

   constructor; constructor.

  unfold points_of_ps_lap_gen in Hpts; simpl in Hpts; simpl.
  destruct (order c) as [v₂| ].
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

Lemma div_gcd_gcd_0_r : ∀ a b c d e f,
  (b / Z.gcd (Z.gcd a b) c)%Z = (e / Z.gcd (Z.gcd d e) f)%Z
  → e = 0%Z
    → (a * e)%Z = (d * b)%Z.
Proof.
intros a b c d e f Hb He.
subst e.
rewrite Z.mul_0_r.
rewrite Z.gcd_0_r in Hb.
destruct (Z_zerop d) as [Hd| Hd].
 subst d; rewrite Z.mul_0_l; reflexivity.

 rewrite Z.div_0_l in Hb.
  rewrite Z.gcd_comm, Z.gcd_assoc in Hb.
  pose proof (Z.gcd_divide_l b (Z.gcd c a)) as H.
  destruct H as (e, H).
  rewrite Z.gcd_comm in H.
  remember (Z.gcd (Z.gcd c a) b) as g.
  rewrite H in Hb.
  destruct (Z_zerop g) as [Hg| Hg].
   move Hg at top; subst g.
   rewrite Z.mul_0_r in H; subst b.
   rewrite Z.mul_0_r; reflexivity.

   rewrite Z.div_mul in Hb; [ idtac | assumption ].
   subst e b.
   rewrite Z.mul_0_l, Z.mul_0_r; reflexivity.

  intros H.
  apply Z.gcd_eq_0_l in H.
  apply Hd.
  apply Z.abs_0_iff; assumption.
Qed.

Lemma div_gcd_gcd_mul_compat : ∀ a b c d e f,
  (a / Z.gcd (Z.gcd a b) c)%Z = (d / Z.gcd (Z.gcd d e) f)%Z
  → (b / Z.gcd (Z.gcd a b) c)%Z = (e / Z.gcd (Z.gcd d e) f)%Z
    → (a * e)%Z = (d * b)%Z.
Proof.
intros a b c d e f Ha Hb.
destruct (Z_zerop e) as [He| He].
 eapply div_gcd_gcd_0_r; eassumption.

 destruct (Z_zerop d) as [Hd| Hd].
  rewrite Z.mul_comm; symmetry.
  rewrite Z.mul_comm; symmetry.
  symmetry.
  apply div_gcd_gcd_0_r with (c := c) (f := f); [ idtac | assumption ].
  replace (Z.gcd b a) with (Z.gcd a b) by apply Z.gcd_comm.
  replace (Z.gcd e d) with (Z.gcd d e) by apply Z.gcd_comm.
  assumption.

  apply Z.mul_cancel_r with (p := e) in Ha; [ idtac | assumption ].
  rewrite Z_div_mul_swap in Ha.
   rewrite Z_div_mul_swap in Ha.
    apply Z.mul_cancel_l with (p := d) in Hb; [ idtac | assumption ].
    rewrite Z.mul_comm in Hb.
    rewrite Z_div_mul_swap in Hb.
     symmetry in Hb.
     rewrite Z.mul_comm in Hb.
     rewrite Z_div_mul_swap in Hb.
      rewrite Z.mul_comm in Hb.
      rewrite Hb in Ha.
      apply Z_div_reg_r in Ha.
       rewrite Ha; apply Z.mul_comm.

       apply Z.divide_mul_l.
       rewrite <- Z.gcd_assoc.
       apply Z.gcd_divide_l.

       apply Z.divide_mul_l.
       rewrite Z.gcd_comm, Z.gcd_assoc.
       apply Z.gcd_divide_r.

      rewrite Z.gcd_comm, Z.gcd_assoc.
      apply Z.gcd_divide_r.

     rewrite Z.gcd_comm, Z.gcd_assoc.
     apply Z.gcd_divide_r.

    rewrite <- Z.gcd_assoc.
    apply Z.gcd_divide_l.

   rewrite <- Z.gcd_assoc.
   apply Z.gcd_divide_l.
Qed.

Add Parametric Morphism α (R : ring α) : (@order α R)
  with signature eq_ps ==> Qbar.qeq
  as order_morph.
Proof.
intros a b Hab.
inversion Hab; subst.
unfold canonic_ps in H; simpl in H.
unfold order.
remember (null_coeff_range_length R (ps_terms a) 0) as na eqn:Hna .
remember (null_coeff_range_length R (ps_terms b) 0) as nb eqn:Hnb .
symmetry in Hna, Hnb.
destruct na as [na| ].
 destruct nb as [nb| ].
  inversion_clear H.
  simpl in H0, H1, H2.
  unfold Qbar.qeq, Qeq; simpl.
  unfold canonify_series in H2.
  remember (greatest_series_x_power R (ps_terms a) na) as apn.
  remember (greatest_series_x_power R (ps_terms b) nb) as bpn.
  assert (0 < gcd_ps na apn a)%Z as Hpga by apply gcd_ps_is_pos.
  assert (0 < gcd_ps nb bpn b)%Z as Hpgb by apply gcd_ps_is_pos.
  unfold gcd_ps in H0, H1, H2, Hpga, Hpgb.
  remember (ps_ordnum a + Z.of_nat na)%Z as ao eqn:Hao .
  remember (ps_ordnum b + Z.of_nat nb)%Z as bo eqn:Hbo .
  remember (Z.of_nat apn) as ap eqn:Hap ; subst apn.
  remember (Z.of_nat bpn) as bp eqn:Hbp ; subst bpn.
  remember (' ps_polord a)%Z as oa eqn:Hoa .
  remember (' ps_polord b)%Z as ob eqn:Hob .
  apply Z2Pos.inj in H1.
   eapply div_gcd_gcd_mul_compat; eassumption.

   apply Z.div_str_pos.
   split; [ assumption | idtac ].
   rewrite Z.gcd_comm, Z.gcd_assoc, Hoa.
   apply Z_gcd_pos_r_le.

   apply Z.div_str_pos.
   split; [ assumption | idtac ].
   rewrite Z.gcd_comm, Z.gcd_assoc, Hob.
   apply Z_gcd_pos_r_le.

  apply ps_null_coeff_range_length_inf_iff in Hnb.
  rewrite Hnb in Hab.
  apply ps_null_coeff_range_length_inf_iff in Hab.
  rewrite Hab in Hna; discriminate Hna.

 apply ps_null_coeff_range_length_inf_iff in Hna.
 rewrite Hna in Hab.
 symmetry in Hab.
 apply ps_null_coeff_range_length_inf_iff in Hab.
 rewrite Hab in Hnb.
 subst nb; reflexivity.
Qed.
