(* Puiseux.v *)

Require Import Utf8 QArith NPeano Sorting.

Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import Qbar.
Require Import Nbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import NotInSegment.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import PosOrder.
Require Import F1Prop.
Require Import InK1m.
Require Import Q_field.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

(* to be moved in the good file *)
Theorem ps_inv_monom : ∀ c pow,
  (c ≠ 0)%K
  → (¹/(ps_monom c pow) = ps_monom ¹/c%K (- pow))%ps.
Proof.
intros c pow Hc.
unfold ps_inv.
unfold ps_monom; simpl.
do 2 rewrite fold_series_const.
remember (null_coeff_range_length R (series_const c) 0) as v eqn:Hv .
symmetry in Hv.
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv.
simpl in Hv.
destruct v as [v| ].
 destruct Hv as (Hiv, Hv).
 symmetry.
 rewrite ps_adjust_eq with (n := v) (k := xH).
 unfold adjust_ps; simpl.
 rewrite series_stretch_1, Z.mul_1_r, Pos.mul_1_r.
 apply mkps_morphism; try reflexivity.
 unfold series_inv; simpl.
 unfold series_shift, series_left_shift; simpl.
 constructor; intros i; simpl.
 rewrite Nat.add_0_r.
 destruct (zerop v) as [H₁| H₁].
  subst v; simpl.
  rewrite Nat.sub_0_r.
  destruct (zerop i) as [H₁| H₁]; [ reflexivity | idtac ].
  rewrite fold_series_const.
  rewrite summation_split_first; auto; simpl.
  rewrite rng_mul_0_l, rng_add_0_l.
  rewrite all_0_summation_0.
   rewrite rng_mul_0_r; reflexivity.

   intros j (Hj, Hji).
   destruct (zerop j) as [H₂| H₂].
    subst j.
    apply Nat.nlt_ge in Hj.
    exfalso; apply Hj, Nat.lt_0_succ.

    rewrite rng_mul_0_l; reflexivity.

  exfalso; apply Hv; reflexivity.

 pose proof (Hv O) as H; simpl in H.
 contradiction.
Qed.

Theorem null_coeff_range_length_const : ∀ c,
  (c ≠ 0)%K
  → null_coeff_range_length R (series_const c) 0 = 0%Nbar.
Proof.
intros c Hc.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop; simpl.
split; [ idtac | assumption ].
intros i Hi.
exfalso; revert Hi; apply Nat.nlt_0_r.
Qed.

Lemma normalise_ps_monom : ∀ c q,
  (c ≠ 0)%K
  → normalise_ps (ps_monom c q) ≐ ps_monom c (Qred q).
Proof.
intros c q Hc.
unfold normalise_ps; simpl.
rewrite fold_series_const.
rewrite null_coeff_range_length_const; auto; simpl.
rewrite Z.add_0_r.
erewrite greatest_series_x_power_series_const; [ idtac | reflexivity ].
unfold gcd_ps; simpl.
rewrite Z.add_0_r; simpl.
rewrite Z.gcd_0_r; simpl.
unfold Qred; simpl.
destruct q as (q₁, q₂).
pose proof (Z.ggcd_correct_divisors q₁ (' q₂)) as H.
remember (Z.ggcd q₁ (' q₂)) as g.
destruct g as (g, (aa, bb)).
destruct H as (Hq₁, Hq₂); simpl.
rewrite Hq₁, Hq₂; simpl.
pose proof (Z.ggcd_gcd q₁ (' q₂)) as Hg.
rewrite <- Heqg in Hg; simpl in Hg.
assert (0 <= g)%Z as Hgnn by (subst g; apply Z.gcd_nonneg).
assert (g ≠ 0)%Z as Hgnz.
 subst g; intros H.
 apply Z.gcd_eq_0_r in H.
 revert H; apply Pos2Z_ne_0.

 rewrite Z.gcd_mul_mono_l_nonneg; auto.
 assert (Z.gcd aa bb = 1)%Z as Hg1.
  apply Z.mul_reg_l with (p := g); auto.
  rewrite Z.mul_1_r.
  rewrite <- Z.gcd_mul_mono_l_nonneg; auto.
  rewrite <- Hq₁, <- Hq₂.
  symmetry; assumption.

  rewrite Z.abs_eq.
   rewrite Z.div_mul_cancel_l; auto.
    rewrite Hg1, Z.div_1_r, Z.mul_1_r.
    rewrite Z.mul_comm.
    rewrite Z.div_mul; auto.
    unfold normalise_series.
    rewrite series_left_shift_0.
    unfold ps_monom; simpl.
    rewrite fold_series_const.
    constructor; auto; simpl.
    apply series_shrink_const.

    rewrite Hg1; intros H; discriminate H.

   apply Z.mul_nonneg_nonneg; auto.
   rewrite Hg1; apply Z.le_0_1.
Qed.

(* *)

Definition phony_ns :=
  {| ini_pt := (0, 0); fin_pt := (0, 0); oth_pts := [] |}.

(* f₁(x,y₁) = 0 => f(x,c₁.x^γ+x^γ.y₁) = 0 *)
Lemma f₁_root_f_root : ∀ f f₁ β γ c₁ y y₁,
  f₁ = next_pol f β γ c₁
  → (y = ps_monom c₁ γ + ps_monom 1%K γ * y₁)%ps
  → (ps_pol_apply f₁ y₁ = 0)%ps
  → (ps_pol_apply f y = 0)%ps.
Proof.
intros f f₁ β γ c₁ y y₁ Hpol₁ Hy Happ.
destruct (ps_zerop R 1%ps) as [Hzo| Hnzo].
 apply eq_1_0_all_0; assumption.

 subst f₁.
 unfold next_pol in Happ.
 unfold ps_pol_apply, apply_poly in Happ; simpl in Happ.
 unfold next_lap in Happ; simpl in Happ.
 unfold ps_pol_apply, apply_poly.
 rewrite apply_lap_mul in Happ.
 rewrite apply_lap_compose in Happ.
 simpl in Happ.
 rewrite ps_mul_0_l in Happ.
 do 2 rewrite ps_add_0_l in Happ.
 rewrite ps_add_comm, <- Hy in Happ.
 apply fld_eq_mul_0_r in Happ; [ assumption | apply ps_field | idtac ].
 simpl; intros H.
 apply ps_monom_0_coeff_0 in H.
 apply Hnzo.
 unfold ps_one; rewrite H.
 apply ps_zero_monom_eq.
Qed.

Lemma minimise_slope_end_2nd_pt : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → snd pt₂ < snd pt₁
    → (∀ pt₃, pt₃ ∈ pts → snd pt₂ <= snd pt₃)
      → ms = minimise_slope pt₁ pt₂ pts
        → end_pt ms = pt₂.
Proof.
intros pt₁ pt₂ pts ms Hsort Hpt₁ Hpt Hms.
revert ms pt₂ Hsort Hpt Hpt₁ Hms.
induction pts as [| pt]; intros.
 simpl in Hms; subst ms; reflexivity.

 simpl in Hms.
 remember (minimise_slope pt₁ pt pts) as ms₁ eqn:Hms₁ .
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c eqn:Hc .
 symmetry in Hc.
 remember Hms₁ as Hsl₁; clear HeqHsl₁.
 symmetry in Hsl₁.
 eapply minimised_slope in Hsl₁; [ idtac | reflexivity ].
 rewrite Hsl₁ in Hc.
 remember Hms₁ as Hsnde; clear HeqHsnde.
 symmetry in Hsnde.
 apply end_pt_in in Hsnde.
 remember (end_pt ms₁) as pte eqn:Hpte .
 remember Hsnde as Hein; clear HeqHein.
 apply Hpt in Hsnde.
 apply Qminus_le_compat_r with (z := snd pt₂) in Hsnde.
 rewrite Qminus_diag in Hsnde.
 apply Qminus_lt_compat_r with (z := snd pt₁) in Hpt₁.
 rewrite Qminus_diag in Hpt₁.
 apply Q_div_lt_mono with (c := fst pt₂ - fst pt₁) in Hpt₁.
  unfold Qdiv at 2 in Hpt₁.
  rewrite Qmult_0_l in Hpt₁.
  apply Q_div_le_mono with (c := fst pte - fst pt₂) in Hsnde.
   unfold Qdiv at 1 in Hsnde.
   rewrite Qmult_0_l in Hsnde.
   destruct c; subst ms; [ simpl | reflexivity | simpl ].
    apply Qlt_not_le in Hpt₁.
    apply Qeq_alt in Hc.
    eapply slope_expr_eq in Hc; try eassumption.
    unfold slope_expr in Hc.
    rewrite Hc in Hpt₁; contradiction.

    apply Qgt_alt in Hc.
    remember Hc as Hd; clear HeqHd.
    apply slope_lt_1312_2313 in Hc.
     eapply Qlt_trans in Hd; [ idtac | eassumption ].
     eapply Qlt_trans in Hpt₁; [ idtac | eassumption ].
     apply Qlt_not_le in Hpt₁.
     contradiction.

     split.
      apply Sorted_inv in Hsort.
      destruct Hsort as (_, Hrel).
      apply HdRel_inv in Hrel.
      assumption.

      apply Sorted_inv_1 in Hsort.
      eapply Sorted_hd; eassumption.

   apply Qlt_minus.
   apply Sorted_inv_1 in Hsort.
   eapply Sorted_hd; eassumption.

  apply Qlt_minus.
  apply Sorted_inv in Hsort.
  destruct Hsort as (_, Hrel).
  apply HdRel_inv in Hrel.
  assumption.
Qed.

Lemma minimise_slope_2_pts : ∀ ms pt₁ pt₂ pts,
  ms = minimise_slope pt₁ pt₂ pts
  → pt₂ ∉ pts
  → end_pt ms = pt₂
  → seg ms = [].
Proof.
intros ms pt₁ pt₂ pts Hms Hnin Hend.
revert ms pt₂ Hms Hnin Hend.
induction pts as [| pt]; intros; [ subst ms; reflexivity | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
destruct c.
 subst ms; simpl in Hend; simpl.
 symmetry in Heqms₁.
 apply end_pt_in in Heqms₁.
 rewrite Hend in Heqms₁; contradiction.

 subst ms; reflexivity.

 subst ms; simpl in Hend; simpl.
 symmetry in Heqms₁.
 apply end_pt_in in Heqms₁.
 rewrite Hend in Heqms₁; contradiction.
Qed.

Lemma pouet : ∀ f ffo ms a₀ a₁ la v₀ v₁ j k αj αk,
  f = pair_rec (λ pow ps, (Qnat pow, ps))
  → ffo = filter_finite_ord R (List.map f (power_list 2 la))
  → ms = minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo
  → (∀ i : nat, (order (List.nth i [a₀; a₁ … la] 0%ps) ≥ 0)%Qbar)
  → v₁ == 0
  → 0 < v₀
  → (Qnat 0, v₀) = (Qnat j, αj)
  → end_pt ms = (Qnat k, αk)
  → (j = 0)%nat ∧ (j < k)%nat ∧ (k ≤ 1)%nat ∧ 0 < αj ∧ αk == 0 ∧ seg ms = [].
Proof.
intros f ffo ms a₀ a₁ la v₀ v₁ j k αj αk.
intros Heqf Heqffo Heqms Hnneg Hz Hpos Hini Hfin.
remember Heqms as Hms; clear HeqHms.
apply minimise_slope_end_2nd_pt in Heqms.
 rewrite Heqms in Hfin.
 injection Hini; clear Hini; intros; subst αj.
 injection Hfin; clear Hfin; intros; subst αk.
 apply Z2Nat.inj_iff in H0; [ idtac | reflexivity | apply Nat2Z.is_nonneg ].
 apply Z2Nat.inj_iff in H1; [ idtac | idtac | apply Nat2Z.is_nonneg ].
  rewrite Nat2Z.id in H0, H1.
  simpl in H0, H1.
  rewrite Pos2Nat.inj_1 in H1.
  subst j k.
  split; [ reflexivity | idtac ].
  split; [ apply Nat.lt_0_1 | idtac ].
  split; [ reflexivity | idtac ].
  split; [ assumption | idtac ].
  split; [ assumption | idtac ].
  eapply minimise_slope_2_pts; try eassumption.
  subst ffo; revert Heqf; clear; intros.
  remember 2%nat as pow.
  assert (2 <= pow)%nat as Hpow by (subst pow; reflexivity).
  clear Heqpow.
  revert pow Hpow.
  induction la as [| a]; intros; [ intros H; assumption | simpl ].
  rewrite Heqf; simpl; rewrite <- Heqf.
  destruct (order a) as [v| ].
   intros H; simpl in H.
   destruct H as [H| H].
    injection H; clear H; intros; subst v.
    apply Z2Nat.inj_iff in H0.
     rewrite Nat2Z.id in H0; simpl in H0.
     unfold Pos.to_nat in H0; simpl in H0.
     rewrite H0 in Hpow.
     apply Nat.nlt_ge in Hpow.
     apply Hpow, Nat.lt_1_2.

     apply Nat2Z.is_nonneg.

     apply Z.le_0_1.

    revert H; apply IHla.
    apply Nat.le_le_succ_r; assumption.

   apply IHla.
   apply Nat.le_le_succ_r; assumption.

  apply Z.le_0_1.

 subst ffo; revert Heqf; clear; intros.
 constructor.
  remember 2%nat as pow.
  assert (1 < pow)%nat as Hpow by (subst pow; apply Nat.lt_1_2).
  clear Heqpow.
  remember 1%nat as n.
  clear Heqn.
  revert n v₁ pow Hpow.
  induction la as [| a]; intros.
   constructor; [ constructor; constructor | constructor ].

   unfold fst_lt; simpl.
   rewrite Heqf; simpl; rewrite <- Heqf.
   destruct (order a) as [v| ].
    constructor.
     apply IHla, Nat.lt_succ_r; reflexivity.

     constructor.
     unfold fst_lt; simpl.
     apply Qnat_lt; assumption.

    apply IHla, Nat.lt_lt_succ_r; assumption.

  constructor.
  unfold fst_lt; simpl.
  apply Qnat_lt, Nat.lt_0_1.

 simpl.
 rewrite Hz; assumption.

 intros pt Hpt; simpl; rewrite Hz.
 rewrite Heqffo in Hpt.
 revert Heqf Hnneg Hpt; clear; intros.
 remember 2%nat as pow; clear Heqpow.
 revert pow Hpt.
 induction la as [| a]; intros; [ contradiction | idtac ].
 simpl in Hpt.
 rewrite Heqf in Hpt; simpl in Hpt; rewrite <- Heqf in Hpt.
 remember (order a) as v.
 symmetry in Heqv.
 destruct v as [v| ].
  simpl in Hpt.
  destruct Hpt as [Hpt| Hpt].
   subst pt; simpl.
   pose proof (Hnneg 2%nat) as H; simpl in H.
   rewrite Heqv in H.
   apply Qbar.qfin_le_mono; assumption.

   eapply IHla; [ intros i | eassumption ].
   revert Hnneg; clear; intros.
   revert la Hnneg.
   induction i; intros; simpl.
    pose proof (Hnneg 0%nat); assumption.

    destruct i; [ pose proof (Hnneg 1%nat); assumption | idtac ].
    pose proof (Hnneg (3 + i)%nat) as H; assumption.

  eapply IHla; [ intros i | eassumption ].
  revert Hnneg; clear; intros.
  revert la Hnneg.
  induction i; intros; simpl.
   pose proof (Hnneg 0%nat); assumption.

   destruct i; [ pose proof (Hnneg 1%nat); assumption | idtac ].
   pose proof (Hnneg (3 + i)%nat) as H; assumption.
Qed.

Lemma root_multiplicity_ne_0 : ∀ pol ns c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) ≠ 0%nat.
Proof.
intros pol ns c Hns Hc.
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
unfold root_multiplicity; simpl.
rewrite skipn_pad, Nat.sub_diag; simpl.
rewrite Hini; simpl.
rewrite nat_num_Qnat.
rewrite fold_char_pol with (αj := αj).
rewrite <- Hini.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point pol) pl) as tl eqn:Htl .
remember (make_char_pol R j tl) as cpol eqn:Hcpol .
destruct (ac_zerop (lap_mod_deg_1 cpol c)) as [| Hnz].
 intros H; discriminate H.

 exfalso; apply Hnz; clear Hnz.
 apply apply_lap_mod_deg_1.
 rewrite Hc.
 remember Hns as Happ; clear HeqHapp.
 apply cpol_degree_ge_1 with (K := K) (acf := acf) in Happ.
 apply ac_prop_root in Happ.
 unfold apply_poly in Happ.
 simpl in Happ.
 rewrite skipn_pad, Nat.sub_diag in Happ.
 rewrite fold_char_pol with (αj := αj) in Happ.
 rewrite Hini in Happ.
 remember List.map as f; simpl in Happ; subst f.
 rewrite nat_num_Qnat in Happ.
 rewrite <- Hini, <- Hpl in Happ.
 rewrite <- Htl, <- Hcpol in Happ.
 assumption.
Qed.

Lemma r_1_j_0_k_1 : ∀ pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ k₁ = 1%nat ∧ αj₁ > 0 ∧ αk₁ == 0 ∧ oth_pts ns₁ = [].
Proof.
intros pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁.
intros Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
assert (0 < 1)%nat as H by apply Nat.lt_0_1.
apply Hpos in H; clear Hpos; rename H into Hpos.
unfold newton_segments in Hns₁; simpl in Hns₁.
unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
unfold ps_poly_nth in Hnneg, Hz, Hpos.
remember (al pol₁) as la.
destruct la as [| a₀].
 unfold ps_lap_nth in Hz; simpl in Hz.
 rewrite order_0 in Hz; inversion Hz.

 unfold ps_lap_nth in Hnneg, Hz, Hpos.
 simpl in Hz, Hpos.
 unfold points_of_ps_lap in Hns₁.
 unfold points_of_ps_lap_gen in Hns₁.
 simpl in Hns₁.
 remember (order a₀) as v₀.
 symmetry in Heqv₀.
 destruct v₀ as [v₀| ].
  destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].
  simpl in Hz, Hns₁.
  remember (order a₁) as v₁.
  symmetry in Heqv₁.
  destruct v₁ as [v₁| ]; [ idtac | contradiction ].
  apply Qbar.qfin_inj in Hz.
  apply Qbar.qfin_lt_mono in Hpos.
  remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
  simpl in Hns₁.
  remember (filter_finite_ord R (List.map f (power_list 2 la))) as ffo.
  remember (minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo) as ms.
  subst ns₁; simpl in Hini₁, Hfin₁.
  rewrite Heqms, minimised_slope_beg_pt in Hini₁.
  eapply pouet in Hfin₁; try eassumption.
  destruct Hfin₁ as (H₁, (H₂, (H₃, (H₄, (H₅, H₆))))).
  split; [ assumption | idtac ].
  split; [ omega | idtac ].
  split; [ assumption | idtac ].
  split; assumption.

  unfold ps_poly_nth in Hps₀.
  rewrite <- Heqla in Hps₀.
  unfold ps_lap_nth in Hps₀; simpl in Hps₀.
  contradiction.
Qed.

Lemma minimise_slope_seg_cons : ∀ pt₁ pt₂ pt₃ pts,
  slope_expr pt₁ pt₂ < slope (minimise_slope pt₁ pt₃ pts)
  → seg (minimise_slope pt₁ pt₂ [pt₃ … pts]) = [].
Proof.
intros pt₁ pt₂ pt₃ pts H.
apply -> Qlt_alt in H.
simpl; rewrite H; reflexivity.
Qed.

Lemma no_pts_order_inf : ∀ la,
  points_of_ps_lap la = []
  → order (List.nth 0 la 0%ps) = ∞%Qbar.
Proof.
intros la H.
destruct la as [| a]; [ apply order_0 | idtac ].
unfold points_of_ps_lap in H.
unfold points_of_ps_lap_gen in H.
simpl in H; simpl.
remember (order a) as oa eqn:Hoa .
symmetry in Hoa.
destruct oa; [ discriminate H | reflexivity ].
Qed.

Lemma one_pt_order_inf : ∀ la pt,
  points_of_ps_lap la = [pt]
  → (order (List.nth 1 la 0%ps) = 0)%Qbar
  → order (List.nth 0 la 0%ps) = ∞%Qbar.
Proof.
intros la pt Hpts Hz.
destruct la as [| a₀]; [ apply order_0 | simpl ].
unfold points_of_ps_lap in Hpts.
unfold points_of_ps_lap_gen in Hpts.
simpl in Hpts, Hz.
remember (order a₀) as oa₀ eqn:Hoa₀ .
destruct oa₀ as [oa₀| ]; [ idtac | reflexivity ].
destruct la as [| a₁]; simpl in Hz.
 rewrite order_0 in Hz; inversion Hz.

 simpl in Hpts.
 remember (order a₁) as oa₁ eqn:Hoa₁ .
 destruct oa₁ as [oa₁| ]; [ idtac | inversion Hz ].
 discriminate Hpts.
Qed.

Lemma pow_ord_of_point : ∀ la pt pow,
  pt ∈ points_of_ps_lap_gen pow la
  → ∃ n,
    fst pt = Qnat (pow + n)
    ∧ qfin (snd pt) = order (ps_lap_nth n la).
Proof.
intros la pt pow Hpt.
revert pow Hpt.
induction la as [| a]; intros; [ contradiction | idtac ].
unfold points_of_ps_lap_gen in Hpt.
simpl in Hpt.
remember (order a) as oa eqn:Hoa .
symmetry in Hoa.
rewrite fold_qpower_list in Hpt.
rewrite fold_points_of_ps_lap_gen in Hpt.
destruct oa as [oa| ].
 destruct Hpt as [Hpt| Hpt].
  subst pt; simpl.
  unfold ps_lap_nth.
  symmetry in Hoa.
  exists 0%nat; split; [ rewrite Nat.add_comm; reflexivity | assumption ].

  apply IHla in Hpt.
  destruct Hpt as (m, (Hpow, Hord)).
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hpow.
  unfold ps_lap_nth in Hord.
  unfold ps_lap_nth.
  exists (S m); split; assumption.

 apply IHla in Hpt.
 destruct Hpt as (m, (Hpow, Hord)).
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hpow.
 unfold ps_lap_nth in Hord.
 unfold ps_lap_nth.
 exists (S m); split; assumption.
Qed.

Lemma exists_ini_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, ini_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_ini_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Lemma exists_fin_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, fin_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_fin_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Lemma multiplicity_1_remains : ∀ pol ns c₁ c₂ pol₁ ns₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₂ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c₂ (Φq pol₁ ns₁) = 1%nat.
Proof.
intros pol ns c₁ c₂ pol₁ ns₁.
intros Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
symmetry in Hr.
unfold root_multiplicity; simpl.
rewrite Nat.sub_diag; simpl.
rewrite skipn_pad; simpl.
remember (al pol₁) as la eqn:Hla .
unfold term_of_point; rewrite <- Hla.
unfold next_pol in Hpol₁.
remember Hla as H; clear HeqH.
rewrite Hpol₁ in H; simpl in H.
clear Hpol₁; rename H into Hpol₁.
unfold ps_poly_nth in Hps₀; rewrite <- Hla in Hps₀.
unfold newton_segments, points_of_ps_polynom in Hns₁; rewrite <- Hla in Hns₁.
unfold Φq, summation_ah_xh_pol, characteristic_polynomial in Hc₂.
unfold term_of_point in Hc₂; rewrite <- Hla in Hc₂.
unfold ps_poly_nth in Hnneg; rewrite <- Hla in Hnneg.
unfold ps_poly_nth in Hpos; rewrite <- Hla in Hpos.
unfold ps_poly_nth in Hz; rewrite <- Hla in Hz.
unfold ps_lap_nth in Hnneg, Hpos, Hz, Hps₀.
assert (0 < 1)%nat as Hp by apply Nat.lt_0_1.
apply Hpos in Hp; simpl in Hp.
clear Hpos; rename Hp into Hpos.
remember (points_of_ps_lap la) as pts eqn:Hpts .
unfold points_of_ps_lap in Hpts.
unfold points_of_ps_lap_gen in Hpts.
clear pol₁ Hla; simpl in Hc₂.
unfold poly_left_shift in Hc₂; simpl in Hc₂.
rewrite skipn_pad, Nat.sub_diag, list_pad_0 in Hc₂.
assert (nat_num (fst (ini_pt ns₁)) = 0)%nat as Hini.
 destruct pts as [| pt₁]; [ subst ns₁; reflexivity | idtac ].
 destruct pts as [| pt₂]; [ subst ns₁; reflexivity | idtac ].
 unfold lower_convex_hull_points in Hns₁.
 rewrite Hns₁; simpl.
 rewrite minimised_slope_beg_pt.
 destruct la as [| a₁]; [ discriminate Hpts | idtac ].
 simpl in Hpts.
 unfold ps_lap_nth in Hps₀; simpl in Hps₀.
 remember (order a₁) as o₁ eqn:Ho₁ .
 symmetry in Ho₁.
 destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
 injection Hpts; clear Hpts; intros Hpts Hpt₁.
 subst pt₁; reflexivity.

 rewrite Hini in Hc₂; rewrite Hini.
 assert (oth_pts ns₁ = [] (*∧ nat_num (fst (fin_pt ns₁)) = 1%nat*)) as Hoth.
  symmetry in Hpts.
  destruct pts as [| pt₁].
   exfalso; apply Hps₀, no_pts_order_inf; assumption.

   destruct pts as [| pt₂].
    apply one_pt_order_inf in Hpts; [ contradiction | assumption ].

    unfold lower_convex_hull_points in Hns₁.
    rewrite Hns₁; simpl.
    destruct la as [| a₁]; [ discriminate Hpts | simpl in Hpts ].
    unfold ps_lap_nth in Hps₀; simpl in Hps₀.
    simpl in Hpos.
    remember (order a₁) as o₁ eqn:Ho₁ .
    symmetry in Ho₁.
    destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
    apply Qbar.qfin_lt_mono in Hpos.
    injection Hpts; clear Hpts; intros Hpts Hpt₁; simpl in Hz.
    destruct la as [| a₂]; [ discriminate Hpts | idtac ].
    simpl in Hpts, Hz.
    remember (order a₂) as o₂ eqn:Ho₂ .
    symmetry in Ho₂.
    destruct o₂ as [o₂| ]; [ apply Qbar.qfin_inj in Hz | inversion Hz ].
    injection Hpts; clear Hpts; intros Hpts Hpt₂.
    subst pt₁ pt₂.
revert Hnneg Hpos Hz Hpts; clear; intros.
    destruct pts as [| pt₁]; [ reflexivity | idtac ].
    rewrite minimise_slope_seg_cons; [ reflexivity | idtac ].
    unfold slope; simpl.
    rewrite minimised_slope_beg_pt.
    unfold Qnat; simpl.
    unfold slope_expr; simpl.
    rewrite Hz.
    rewrite Q_sub_0_l, Q_sub_0_r, Q_sub_0_r, Q_div_1_r.
    remember (minimise_slope (0, o₁) pt₁ pts) as ms eqn:Hms .
    remember (end_pt ms) as pt eqn:Hend .
    symmetry in Hend.
    destruct pt as (pow, ord); simpl.
    assert (pow >= Qnat 2) as Hp2.
     revert Hpts Hms Hend; clear; intros.
     remember 2 as n.
     assert (2 ≤ n)%nat as Hn by (subst n; reflexivity).
     clear Heqn.
     revert o₁ pt₁ pts ms pow ord n Hpts Hms Hend Hn.
     induction la as [| a]; intros; [ discriminate Hpts | idtac ].
     destruct n.
      exfalso; apply Nat.nle_gt in Hn; apply Hn, Nat.le_0_1.

      simpl in Hpts.
      remember (order a) as oa eqn:Hoa .
      symmetry in Hoa.
      destruct oa as [oa| ].
       injection Hpts; clear Hpts; intros Hpts Hpt₁; subst pt₁.
       destruct pts as [| pt₁].
        simpl in Hms.
        subst ms; simpl in Hend.
        injection Hend; clear Hend; intros; subst pow; apply Qle_refl.

        simpl in Hms.
        remember (minimise_slope (0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
        remember (slope_expr (0, o₁) (Qnat (S n), oa) ?= slope ms₁) as c
         eqn:Hc .
        symmetry in Hc.
        destruct c.
         rewrite Hms in Hend; simpl in Hend.
         eapply IHla in Hpts; try eassumption.
          eapply Qle_trans; [ idtac | eassumption ].
          apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

          apply Nat.le_le_succ_r; assumption.

         rewrite Hms in Hend; simpl in Hend.
         injection Hend; clear Hend; intros; subst pow; apply Qle_refl.

         move Hms at top; subst ms₁.
         eapply IHla in Hpts; try eassumption.
          eapply Qle_trans; [ idtac | eassumption ].
          apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

          apply Nat.le_le_succ_r; assumption.

       eapply IHla in Hpts; try eassumption.
        eapply Qle_trans; [ idtac | eassumption ].
        apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

        apply Nat.le_le_succ_r; assumption.

     assert (ord >= 0) as Hop.
      revert Hnneg Hpts Hms Hend; clear; intros.
      remember 2 as n.
      assert (2 ≤ n)%nat as Hn by (subst n; reflexivity).
      clear Heqn.
      revert o₁ pt₁ pts ms pow ord n Hpts Hms Hend Hn.
      induction la as [| a]; intros; [ discriminate Hpts | idtac ].
      destruct n.
       exfalso; apply Nat.nle_gt in Hn; apply Hn, Nat.le_0_1.

       simpl in Hpts.
       remember (order a) as oa eqn:Hoa .
       symmetry in Hoa.
       destruct oa as [oa| ].
        injection Hpts; clear Hpts; intros Hpts Hpt₁; subst pt₁.
        destruct pts as [| pt₁].
         simpl in Hms.
         subst ms; simpl in Hend.
         injection Hend; clear Hend; intros; subst pow oa.
         pose proof (Hnneg 2) as H.
         simpl in H.
         rewrite Hoa in H.
         apply Qbar.qfin_le_mono; assumption.

         simpl in Hms.
         remember (minimise_slope (0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
         remember (slope_expr (0, o₁) (Qnat (S n), oa) ?= slope ms₁) as c
          eqn:Hc .
         symmetry in Hc.
         destruct c.
          rewrite Hms in Hend; simpl in Hend.
          eapply IHla in Hpts; try eassumption.
           intros i.
           destruct i; simpl.
            pose proof (Hnneg 0%nat); assumption.

            destruct i.
             pose proof (Hnneg 1%nat); assumption.

             pose proof (Hnneg (3 + i)%nat) as H; assumption.

           apply Nat.le_le_succ_r; assumption.

          rewrite Hms in Hend; simpl in Hend.
          injection Hend; clear Hend; intros; subst pow.
          subst oa.
          pose proof (Hnneg 2) as H; simpl in H.
          rewrite Hoa in H.
          apply Qbar.qfin_le_mono; assumption.

          move Hms at top; subst ms₁.
          eapply IHla in Hpts; try eassumption.
           intros i.
           destruct i; simpl.
            pose proof (Hnneg 0%nat); assumption.

            destruct i.
             pose proof (Hnneg 1%nat); assumption.

             pose proof (Hnneg (3 + i)%nat) as H; assumption.

           apply Nat.le_le_succ_r; assumption.

        eapply IHla in Hpts; try eassumption.
         intros i.
         destruct i; simpl.
          pose proof (Hnneg 0%nat); assumption.

          destruct i.
           pose proof (Hnneg 1%nat); assumption.

           pose proof (Hnneg (3 + i)%nat) as H; assumption.

         apply Nat.le_le_succ_r; assumption.

      revert Hpos Hp2 Hop; clear; intros.
      rewrite <- Qopp_minus, <- Q_div_opp_opp, Q_div_opp_r.
      apply Qopp_lt_compat.
      rewrite Qopp_opp.
      apply Qle_lt_trans with (y := o₁ / pow).
       apply Q_div_le_mono.
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 0 with (Qnat 0) by reflexivity.
        apply Qnat_lt, Nat.lt_0_succ.

        apply Qle_sub_le_add_l.
        assert (0 + o₁ == o₁) as H by apply Qplus_0_l.
        rewrite <- H in |- * at 1.
        apply Qplus_le_l; assumption.

       apply Qlt_shift_div_r.
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 0 with (Qnat 0) by reflexivity.
        apply Qnat_lt, Nat.lt_0_succ.

        rewrite <- Qmult_1_r in |- * at 1.
        apply Qmult_lt_l; [ assumption | idtac ].
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 1 with (Qnat 1) by reflexivity.
        apply Qnat_lt, Nat.lt_succ_r; reflexivity.

  rewrite Hoth; simpl.
  assert (nat_num (fst (fin_pt ns₁)) = 1)%nat as Hfin.
   symmetry in Hpts.
   destruct pts as [| pt₁].
    exfalso; apply Hps₀, no_pts_order_inf; assumption.

    destruct pts as [| pt₂].
     apply one_pt_order_inf in Hpts; [ contradiction | assumption ].

     unfold lower_convex_hull_points in Hns₁.
     rewrite Hns₁; simpl.
     destruct la as [| a₁]; [ discriminate Hpts | simpl in Hpts ].
     unfold ps_lap_nth in Hps₀; simpl in Hps₀.
     simpl in Hpos.
     remember (order a₁) as o₁ eqn:Ho₁ .
     symmetry in Ho₁.
     destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
     apply Qbar.qfin_lt_mono in Hpos.
     injection Hpts; clear Hpts; intros Hpts Hpt₁; simpl in Hz.
     destruct la as [| a₂]; [ discriminate Hpts | idtac ].
     simpl in Hpts, Hz.
     remember (order a₂) as o₂ eqn:Ho₂ .
     symmetry in Ho₂.
     destruct o₂ as [o₂| ]; [ apply Qbar.qfin_inj in Hz | inversion Hz ].
     injection Hpts; clear Hpts; intros Hpts Hpt₂.
     subst pt₁ pt₂.
     remember (minimise_slope (Qnat 0, o₁) (Qnat 1, o₂) pts) as ms eqn:Hms .
     destruct pts as [| pt₁]; [ subst ms; reflexivity | idtac ].
     simpl in Hpts, Hms.
     remember (minimise_slope (Qnat 0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
     unfold slope_expr in Hms; simpl in Hms.
     unfold Qnat in Hms; simpl in Hms.
     rewrite Q_sub_0_r, Q_div_1_r in Hms.
     rewrite Hz, Q_sub_0_l in Hms.
     unfold slope in Hms.
     rewrite Hms₁ in Hms at 1.
     rewrite minimised_slope_beg_pt in Hms.
     unfold slope_expr, Qnat in Hms; simpl in Hms.
     rewrite Q_sub_0_r in Hms.
     remember (end_pt ms₁) as p eqn:Hp .
     symmetry in Hp.
     destruct p as (pow, ord); simpl in Hms.
     remember (- o₁ ?= (ord - o₁) / pow) as c eqn:Hc .
     symmetry in Hc.
     destruct c.
      subst ms; simpl.
      apply Qeq_alt in Hc.
      symmetry in Hc.
      apply Qeq_shift_mult_l in Hc.
       apply Qminus_eq_eq_plus_r in Hc.
       setoid_replace (- o₁ * pow + o₁) with (- o₁ * (pow - 1)) in Hc by
        ring.
       remember Hms₁ as Hend; clear HeqHend.
       symmetry in Hend.
       apply end_pt_in in Hend.
       rewrite fold_qpower_list in Hpts.
       rewrite fold_points_of_ps_lap_gen in Hpts.
       rewrite <- Hpts in Hend.
       apply pow_ord_of_point in Hend.
       destruct Hend as (n, (Hpow, Hord)).
       rewrite Hp in Hpow; simpl in Hpow.
       rewrite Hp in Hord; simpl in Hord.
       assert (qfin ord ≥ 0)%Qbar as Hop.
        rewrite Hord.
        pose proof (Hnneg (2 + n)%nat) as H; assumption.

        rewrite Hc in Hop.
        apply Qbar.qfin_le_mono in Hop.
        rewrite Qmult_opp_l in Hop.
        apply Qopp_le_compat in Hop.
        rewrite Qopp_opp in Hop.
        apply Qle_not_lt in Hop.
        exfalso; apply Hop.
        unfold Qopp at 1; simpl.
        rewrite Hpow; simpl.
        rewrite <- Qnat_1.
        rewrite <- Qnat_inj_sub; [ simpl | apply le_n_S, Nat.le_0_l ].
        apply Q_mul_pos_pos; [ assumption | idtac ].
        rewrite <- Qnat_0.
        apply Qnat_lt, Nat.lt_0_succ.

       remember Hms₁ as Hend; clear HeqHend.
       symmetry in Hend.
       apply end_pt_in in Hend.
       rewrite fold_qpower_list in Hpts.
       rewrite fold_points_of_ps_lap_gen in Hpts.
       rewrite <- Hpts in Hend.
       apply pow_ord_of_point in Hend.
       destruct Hend as (n, (Hpow, Hord)).
       rewrite Hp in Hpow; simpl in Hpow.
       rewrite Hp in Hord; simpl in Hord.
       rewrite Hpow.
       rewrite <- Qnat_0.
       unfold Qnat, Qeq; simpl.
       apply Pos2Z_ne_0.

      subst ms; reflexivity.

      move Hms at top; subst ms₁.
      rewrite Hp; simpl.
      apply Qgt_alt in Hc.
      remember Hms₁ as Hend; clear HeqHend.
      symmetry in Hend.
      apply end_pt_in in Hend.
      rewrite fold_qpower_list in Hpts.
      rewrite fold_points_of_ps_lap_gen in Hpts.
      rewrite <- Hpts in Hend.
      apply pow_ord_of_point in Hend.
      destruct Hend as (n, (Hpow, Hord)).
      rewrite Hp in Hpow; simpl in Hpow.
      rewrite Hp in Hord; simpl in Hord.
      apply Qlt_shift_mult_l in Hc.
       apply Qminus_lt_lt_plus_r in Hc.
       setoid_replace (- o₁ * pow + o₁) with (o₁ * (1 - pow)) in Hc by ring.
       eapply Qlt_trans with (z := 0) in Hc.
        pose proof (Hnneg (2 + n)%nat) as H; simpl in H.
        rewrite fold_ps_lap_nth in H.
        rewrite <- Hord in H.
        apply Qbar.qfin_le_mono in H.
        apply Qlt_not_le in Hc; contradiction.

        rewrite <- Qopp_opp.
        setoid_replace 0 with (- 0) by reflexivity.
        apply Qopp_lt_compat.
        rewrite <- Qmult_opp_r.
        rewrite Qopp_minus, Hpow, <- Qnat_1.
        rewrite <- Qnat_inj_sub; [ simpl | apply le_n_S, Nat.le_0_l ].
        apply Q_mul_pos_pos; [ assumption | idtac ].
        rewrite <- Qnat_0.
        apply Qnat_lt, Nat.lt_0_succ.

       rewrite Hpow.
       rewrite <- Qnat_0.
       apply Qnat_lt, Nat.lt_0_succ.

   rewrite Hfin; simpl.
   rewrite Hoth in Hc₂; simpl in Hc₂.
   rewrite Hfin in Hc₂; simpl in Hc₂.
   remember
    [order_coeff (List.nth 0 la 0%ps); order_coeff (List.nth 1 la 0%ps) … []]%pol as la₂.
   remember POL la₂%pol as pol₂ eqn:Hpol₂ .
   assert (order_coeff (List.nth 1 la 0%ps) ≠ 0)%K as Hnz.
    intros Hoc₁.
    move Hz at bottom.
    unfold order_coeff in Hoc₁.
    unfold order in Hz.
    remember (ps_terms (List.nth 1 la 0%ps)) as s.
    remember (null_coeff_range_length R s 0) as v eqn:Hv .
    destruct v as [v| ].
     apply Qbar.qfin_inj in Hz.
     symmetry in Hv.
     apply null_coeff_range_length_iff in Hv.
     unfold null_coeff_range_length_prop in Hv.
     simpl in Hv.
     destruct Hv as (Hvi, Hv).
     rewrite Hoc₁ in Hv.
     apply Hv; reflexivity.

     inversion Hz.

    assert (degree ac_zerop pol₂ ≥ 1)%nat as Hpol.
     subst pol₂ la₂.
     unfold degree; simpl.
     remember (order_coeff (List.nth 1 la 0%ps)) as oc₁ eqn:Hoc₁ .
     symmetry in Hoc₁.
     destruct (ac_zerop oc₁) as [| Hne]; [ contradiction | idtac ].
     apply Nat.le_refl.

     apply ac_prop_root in Hpol.
     rewrite <- Hc₂, Hpol₂ in Hpol.
     unfold apply_poly in Hpol; simpl in Hpol.
     destruct (ac_zerop (lap_mod_deg_1 la₂ c₂)) as [Heq| Hne].
      apply eq_S.
      destruct (ac_zerop (lap_mod_deg_1 (lap_div_deg_1 la₂ c₂) c₂))
       as [Heq₁| ]; [ idtac | reflexivity ].
      apply lap_mod_deg_1_apply in Heq₁.
      rewrite Heqla₂ in Heq₁; simpl in Heq₁.
      rewrite rng_mul_0_l in Heq₁.
      do 2 rewrite rng_add_0_l in Heq₁.
      contradiction.

      apply apply_lap_mod_deg_1 in Hpol.
      contradiction.
Qed.

Lemma r_1_γ_eq_β_eq_αj : ∀ pol ns c₁ pol₁ ns₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → γ ns₁ == β ns₁ ∧ γ ns₁ == snd (ini_pt ns₁).
Proof.
intros pol ns c₁ pol₁ ns₁ Hns Hc₁ Hr Hpol₁ Hns₁ Hps₀.
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
rewrite Hini₁; simpl.
unfold γ, β; simpl.
rewrite Hini₁, Hfin₁; simpl.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁; rewrite Hαk₁.
unfold Qnat; simpl.
do 2 rewrite Q_sub_0_r.
rewrite Qmult_0_l, Qplus_0_r.
rewrite Q_div_1_r.
split; reflexivity.
Qed.

(* *)

Fixpoint nth_pol n pol ns :=
  match n with
  | 0%nat => pol
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_pol n₁ pol₁ ns₁
  end.

Fixpoint nth_ns n pol ns :=
  match n with
  | 0%nat => ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_ns n₁ pol₁ ns₁
  end.

Fixpoint nth_c n pol ns :=
  match n with
  | 0%nat => ac_root (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_c n₁ pol₁ ns₁
  end.

Fixpoint nth_γ n pol ns :=
  match n with
  | 0%nat => γ ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_γ n₁ pol₁ ns₁
  end.

Definition same_r pol ns :=
  let c₁ := ac_root (Φq pol ns) in
  let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
  let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
  let ns₁ := List.hd phony_ns (newton_segments pol₁) in
  let c₂ := ac_root (Φq pol₁ ns₁) in
  let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
  let r₂ := root_multiplicity acf c₂ (Φq pol₁ ns₁) in
  r₁ = r₂.

(* [Walker, p 102] ... *)
(*
Lemma www : ∀ pol ns q c₁ pol₁ ns₁,
  same_r pol ns
  → c₁ = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → q = q_of_ns pol₁ ns₁
  → q = 1%positive.
Proof.
intros pol ns q c₁ pol₁ ns₁ Hsr Hc₁ Hpol₁ Hns₁ Hq; subst q.
ccc.
unfold same_r in Hsr.
rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hsr.
remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
do 2 rewrite Φq_pol in Hsr.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember [ini_pt ns₁ … oth_pts ns₁ ++ [fin_pt ns₁]] as pl₁ eqn:Hpl₁ .
unfold root_multiplicity in Hsr.
simpl in Hsr.
ccc.
*)

Fixpoint polydromy_if_r_reaches_one acf m pol {struct m} :=
  match m with
  | 0%nat => 0%nat
  | S m₁ =>
      let ns := List.hd phony_ns (newton_segments pol) in
      let c₁ := ac_root (Φq pol ns) in
      let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
      if eq_nat_dec r₁ 1 then 1%nat
      else
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let v := polydromy_if_r_reaches_one acf m₁ pol₁ in
        (v * Pos.to_nat (Qden (γ ns)))%nat
  end.

Definition next_pow pow ns₁ pol_ord :=
  let n := (γ ns₁ * inject_Z ('pol_ord)) in
  (pow + Z.to_nat (Qnum n / ' Qden n))%nat.

Fixpoint find_coeff max_iter npow pol_ord pol ns i :=
  match max_iter with
  | 0%nat => 0%K
  | S m =>
      if ps_zerop _ (ps_poly_nth 0 pol) then 0%K
      else if eq_nat_dec npow i then ac_root (Φq pol ns)
      else if lt_dec npow i then
        let c₁ := ac_root (Φq pol ns) in
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        let npow₁ := next_pow npow ns₁ pol_ord in
        find_coeff m npow₁ pol_ord pol₁ ns₁ i
      else 0%K
  end.

Definition root_series_from_cγ_list pol_ord pol ns i :=
  find_coeff (S i) 0%nat pol_ord pol ns i.

Definition root_from_cγ_list m pol ns :=
  {| ps_terms := {| terms := root_series_from_cγ_list m pol ns |};
     ps_ordnum := Qnum (γ ns) * ' m / ' Qden (γ ns);
     ps_polord := m |}.

Definition γ_sum n pol ns :=
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ i pol ns.

Definition root_head n pol ns :=
  let pr := ps_ring R in
  if ps_zerop _ (ps_poly_nth 0 pol) then 0%ps
  else Σ (i = 0, n), ps_monom (nth_c i pol ns) (γ_sum i pol ns).

Definition root_tail m n pol ns :=
  let poln := nth_pol n pol ns in
  if ps_zerop _ (ps_poly_nth 0 poln) then 0%ps
  else root_from_cγ_list m poln (nth_ns n pol ns).

Lemma nth_pol_succ : ∀ n pol ns pol₁ ns₁ c₁,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_pol (S n) pol ns = next_pol pol₁ (β ns₁) (γ ns₁) c₁.
Proof.
intros n pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Lemma nth_ns_succ : ∀ n pol ns pol₁,
  pol₁ = nth_pol (S n) pol ns
  → nth_ns (S n) pol ns = List.hd phony_ns (newton_segments pol₁).
Proof.
intros n pol ns pol₁ Hpol₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Lemma exists_ini_pt_nat_n : ∀ pol ns n nsn,
  ns ∈ newton_segments pol
  → nsn = nth_ns n pol ns
  → ∃ i αi, ini_pt nsn = (Qnat i, αi).
Proof.
intros pol ns n nsn Hns Hnsn.
destruct n.
 subst nsn; simpl.
 eapply exists_ini_pt_nat; eassumption.

 simpl in Hnsn.
 remember (ac_root (Φq pol ns)) as c.
 remember (next_pol pol (β ns) (γ ns) c) as polp.
 remember (List.hd phony_ns (newton_segments polp)) as nsp.
 clear Heqpolp.
 revert polp nsp nsn Heqnsp Hnsn.
 induction n; intros.
  subst nsn; simpl.
  eapply exists_ini_pt_nat_fst_seg; eassumption.

  simpl in Hnsn.
  remember (ac_root (Φq pol ns)) as c₁.
  remember (next_pol pol (β ns) (γ ns) c) as pol₁.
  remember (List.hd phony_ns (newton_segments polp)) as ns₁.
  eapply IHn; [ idtac | eassumption ].
  reflexivity.
Qed.

Lemma exists_fin_pt_nat_n : ∀ pol ns n nsn,
  ns ∈ newton_segments pol
  → nsn = nth_ns n pol ns
  → ∃ i αi, fin_pt nsn = (Qnat i, αi).
Proof.
intros pol ns n nsn Hns Hnsn.
destruct n.
 subst nsn; simpl.
 eapply exists_fin_pt_nat; eassumption.

 simpl in Hnsn.
 remember (ac_root (Φq pol ns)) as c.
 remember (next_pol pol (β ns) (γ ns) c) as polp.
 remember (List.hd phony_ns (newton_segments polp)) as nsp.
 clear Heqpolp.
 revert polp nsp nsn Heqnsp Hnsn.
 induction n; intros.
  subst nsn; simpl.
  eapply exists_fin_pt_nat_fst_seg; eassumption.

  simpl in Hnsn.
  remember (ac_root (Φq pol ns)) as c₁.
  remember (next_pol pol (β ns) (γ ns) c) as pol₁.
  remember (List.hd phony_ns (newton_segments polp)) as ns₁.
  eapply IHn; [ idtac | eassumption ].
  reflexivity.
Qed.

Lemma Qnum_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qnum (/ (Qnat k - Qnat j)) = 1%Z.
Proof.
intros j k Hjk.
rewrite Qnum_inv; [ reflexivity | simpl ].
do 2 rewrite Z.mul_1_r.
rewrite Z.add_opp_r.
rewrite <- Nat2Z.inj_sub.
 rewrite <- Nat2Z.inj_0.
 apply Nat2Z.inj_lt.
 apply Nat.lt_add_lt_sub_r; assumption.

 apply Nat.lt_le_incl; assumption.
Qed.

Lemma Qden_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qden (/ (Qnat k - Qnat j)) = Pos.of_nat (k - j).
Proof.
intros j k Hjk.
apply Pos2Z.inj.
rewrite Qden_inv.
 simpl.
 do 2 rewrite Z.mul_1_r.
 symmetry.
 rewrite <- positive_nat_Z; simpl.
 rewrite Nat2Pos.id.
  rewrite Nat2Z.inj_sub; auto.
  apply Nat.lt_le_incl; assumption.

  intros H.
  apply Nat.sub_0_le in H.
  apply Nat.nlt_ge in H; contradiction.

 simpl.
 do 2 rewrite Z.mul_1_r.
 rewrite Z.add_opp_r.
 rewrite <- Nat2Z.inj_sub.
  rewrite <- Nat2Z.inj_0.
  apply Nat2Z.inj_lt.
  apply Nat.lt_add_lt_sub_r; assumption.

  apply Nat.lt_le_incl; assumption.
Qed.

Lemma hd_newton_segments : ∀ pol ns j k αj αk,
  ns = List.hd phony_ns (newton_segments pol)
  → ini_pt ns = (Qnat j, αj)
  → fin_pt ns = (Qnat k, αk)
  → (j < k)%nat
  → ns ∈ newton_segments pol.
Proof.
intros pol ns j k αj αk Hns Hini Hfin Hjk.
remember (newton_segments pol) as nsl.
symmetry in Heqnsl.
destruct nsl as [| ns₁]; simpl in Hns.
 subst ns; simpl in Hini, Hfin.
 injection Hini; intros; subst.
 injection Hfin; intros; subst.
 rewrite <- Nat2Z.inj_0 in H0.
 rewrite <- Nat2Z.inj_0 in H1.
 apply Nat2Z.inj in H0.
 apply Nat2Z.inj in H1.
 subst j k; exfalso; revert Hjk; apply Nat.lt_irrefl.

 subst ns; left; reflexivity.
Qed.

Lemma ps_lap_in_0th : ∀ la, (la ≠ [])%pslap → ps_lap_in (ps_lap_nth 0 la) la.
Proof.
intros la Hla.
unfold ps_lap_nth.
destruct la as [| a]; [ exfalso; apply Hla; reflexivity | simpl ].
left; split; [ assumption | reflexivity ].
Qed.

Lemma next_lap_not_nil : ∀ pol ns ns₁ c la αj₁ αk₁,
  la = next_lap pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments POL la%pol)
  → ini_pt ns₁ = (0, αj₁)
  → fin_pt ns₁ = (1, αk₁)
  → (la ≠ [])%pslap.
Proof.
intros pol ns ns₁ c la αj₁ αk₁ Hla Hns₁ Hini₁ Hfin₁.
intros H.
symmetry in Hla.
inversion H; subst.
 rewrite <- H0 in Hini₁, Hfin₁.
 simpl in Hini₁, Hfin₁.
 discriminate Hfin₁.

 rewrite <- H2 in Hini₁, Hfin₁.
 unfold newton_segments in Hini₁, Hfin₁.
 unfold points_of_ps_polynom in Hini₁, Hfin₁.
 unfold points_of_ps_lap in Hini₁, Hfin₁.
 unfold points_of_ps_lap_gen in Hini₁, Hfin₁.
 simpl in Hini₁, Hfin₁.
 simpl in H0.
 apply order_inf in H0.
 rewrite H0 in Hini₁, Hfin₁.
 remember 1%nat as pow.
 assert (1 <= pow)%nat as Hpow by (subst pow; reflexivity).
 clear Heqpow.
 clear x H0 H2.
 revert pow Hpow Hini₁ Hfin₁.
 induction l as [| a]; intros; [ discriminate Hfin₁ | idtac ].
 simpl in Hini₁, Hfin₁.
 apply lap_eq_cons_nil_inv in H1.
 destruct H1 as (Ha, Hla).
 simpl in Ha.
 apply order_inf in Ha.
 rewrite Ha in Hini₁, Hfin₁.
 apply IHl with (pow := S pow); auto.
Qed.

(* similar to q_mj_mk_eq_p_h_j₂ *)
Theorem q_mj_mk_eq_p_h_j : ∀ pol ns j αj m mj p q,
  ns ∈ newton_segments pol
  → (Qnat j, αj) = ini_pt ns
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → mj = mh_of_m m αj (ps_poly_nth j pol)
  → p = p_of_m m (γ ns)
  → q = Pos.to_nat (q_of_m m (γ ns))
  → ∀ h αh mh, (Qnat h, αh) ∈ oth_pts ns ++ [fin_pt ns]
  → mh = mh_of_m m αh (ps_poly_nth h pol)
  → αh == mh # m
    ∧ (Z.of_nat q * (mj - mh) = p * Z.of_nat (h - j))%Z.
Proof.
intros pol ns j αj m mj p q Hns Hj Hm Hmj Hp Hq h αh mh Hh Hmh.
remember (points_of_ps_polynom pol) as pts eqn:Hpts .
remember (ps_poly_nth h pol) as hps.
apply List.in_app_or in Hh.
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
split.
 rewrite Hmh; simpl.
 unfold Qeq; simpl.
 unfold mh_of_m; simpl.
 subst hps.
 destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ].
  erewrite <- qden_αh_is_ps_polord; eauto .
  rewrite Z_div_mul_swap.
   rewrite Z.div_mul; auto.

   eapply den_αh_divides_num_αh_m; eauto .

  erewrite <- qden_αk_is_ps_polord; eauto .
  rewrite Z_div_mul_swap.
   rewrite Z.div_mul; auto.

   eapply den_αk_divides_num_αk_m; eauto .

 destruct Hh as [Hh| [Hh| ]]; [ idtac | idtac | contradiction ].
  remember Hns as Hgh; clear HeqHgh.
  eapply gamma_value_jh in Hgh; try eassumption.
  remember (q_of_m m (γ ns)) as pq eqn:Hpq .
  pose proof (any_is_p_mq (γ ns) m Hp Hpq) as H.
  destruct H as (Hgamma, Hg).
  rewrite Hgamma in Hgh.
  unfold Qnat in Hgh.
  rewrite <- Qnum_minus_distr_r in Hgh.
  rewrite Nat2Z.inj_sub.
   rewrite Hq.
   rewrite positive_nat_Z.
   eapply pmq_qmpm; try reflexivity.
    eapply j_lt_h; try eassumption; reflexivity.

    rewrite Hgh.
    remember Heqhps as Hhps; clear HeqHhps.
    eapply in_pts_in_pol in Hhps; try eassumption.
     destruct Hhps as (Hhps, Hαh).
     do 2 rewrite Qnum_minus_distr_r.
     eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
     eapply pol_ord_of_oth_pt in Hh; try eassumption.
      rewrite Hh; reflexivity.

      subst hps; assumption.

     eapply oth_pts_in_init_pts; try eassumption.
     unfold newton_segments in Hns.
     rewrite <- Hpts in Hns; assumption.

   apply Nat.lt_le_incl.
   eapply j_lt_h; try eassumption; reflexivity.

  remember Hj as Hgh; clear HeqHgh.
  symmetry in Hh.
  eapply gamma_value_jk in Hgh; [ idtac | eassumption ].
  remember (q_of_m m (γ ns)) as pq eqn:Hpq .
  pose proof (any_is_p_mq (γ ns) m Hp Hpq) as H.
  destruct H as (Hgamma, Hg).
  rewrite Hgh in Hgamma.
  unfold Qnat in Hgamma.
  rewrite <- Qnum_minus_distr_r in Hgamma.
  rewrite Nat2Z.inj_sub.
   rewrite Hq.
   rewrite positive_nat_Z.
   eapply pmq_qmpm; try reflexivity.
    eapply j_lt_k; try eassumption.
     rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

     rewrite <- Hh; simpl; rewrite nat_num_Qnat; reflexivity.

    rewrite <- Hgamma.
    remember Heqhps as Hhps; clear HeqHhps.
    eapply in_pts_in_pol with (hv := αh) in Hhps; try eassumption.
     destruct Hhps as (Hhps, Hαh).
     do 2 rewrite Qnum_minus_distr_r.
     eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
     eapply pol_ord_of_fin_pt in Hh; try eassumption.
      rewrite Hh; reflexivity.

      subst hps; assumption.

     rewrite Hh.
     eapply ini_fin_ns_in_init_pts; try eassumption.
     unfold newton_segments in Hns.
     rewrite <- Hpts in Hns; assumption.

   apply Nat.lt_le_incl.
   eapply j_lt_k; try eassumption.
    rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

    rewrite <- Hh; simpl; rewrite nat_num_Qnat; reflexivity.
Qed.

(* similar to CharactPolyn.p_and_q_have_no_common_factors₂ *)
Theorem p_and_q_have_no_common_factors : ∀ a m p q,
  p = p_of_m m a
  → q = q_of_m m a
  → Z.gcd p (' q) = 1%Z.
Proof.
intros a m p q Hp Hq.
eapply any_is_p_mq; eauto .
Qed.

(* similar to CharactPolyn.q_is_factor_of_h_minus_j₂ *)
Theorem q_is_factor_of_h_minus_j : ∀ pol ns j αj m q,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → (Qnat j, αj) = ini_pt ns
  → q = Pos.to_nat (q_of_m m (γ ns))
  → ∀ h αh, (Qnat h, αh) ∈ oth_pts ns ++ [fin_pt ns]
  → (q | h - j)%nat.
Proof.
intros pol ns j αj m q Hns Hm Hj Hq h αh Hh.
remember (p_of_m m (γ ns)) as p eqn:Hp .
remember Hns as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j in H; try eassumption; try reflexivity.
destruct H as (Hαh, Hqjh).
apply List.in_app_or in Hh.
remember (q_of_m m (γ ns)) as pq eqn:Hpq ; subst q.
rename pq into q; rename Hpq into Hq.
remember Hp as Hgcd; clear HeqHgcd.
eapply p_and_q_have_no_common_factors in Hgcd; eauto .
rewrite Z.gcd_comm in Hgcd.
rewrite <- positive_nat_Z in Hgcd.
rewrite Z.gcd_comm in Hgcd.
rewrite Z.gcd_comm in Hgcd.
apply Z.gauss with (p := Z.of_nat (h - j)) in Hgcd.
 2: rewrite <- Hqjh.
 2: apply Z.divide_factor_l.

 destruct Hgcd as (c, Hc).
 exists (Z.to_nat c).
 apply Nat2Z.inj.
 rewrite Nat2Z.inj_mul.
 rewrite Z2Nat.id; [ assumption | idtac ].
 eapply mul_pos_nonneg; try eassumption.
 destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ].
  eapply j_lt_h; try eassumption; reflexivity.

  eapply j_lt_k; try eassumption.
   rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

   rewrite Hk; simpl; rewrite nat_num_Qnat; reflexivity.
Qed.

Lemma q_eq_1 : ∀ pol ns pol₁ ns₁ c₁ m q₀,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → ps_lap_forall (λ a, in_K_1_m a (m * q₀)) (al pol₁)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → q_of_m (m * q₀) (γ ns₁) = 1%positive.
Proof.
intros pol ns pol₁ ns₁ c₁ m q₀ Hns Hm Hq₀ Hc₁ Hr Hpol₁ Hns₁ Hps₀.
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁; simpl.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
eapply hd_newton_segments in Hns₁; eauto .
remember Hns₁ as Hqhj; clear HeqHqhj.
remember (Pos.to_nat (q_of_m (m * q₀) (γ ns₁))) as q.
eapply q_is_factor_of_h_minus_j in Hqhj; eauto .
 2: apply List.in_or_app; right; left; symmetry; eauto .

 simpl in Hqhj.
 destruct Hqhj as (c, Hc).
 symmetry in Hc.
 apply Nat.eq_mul_1 in Hc.
 move Hc at top; destruct Hc; subst c q.
 symmetry in Heqq.
 rewrite <- Pos2Nat.inj_1 in Heqq.
 apply Pos2Nat.inj in Heqq.
 assumption.
Qed.

Lemma points_of_nil_ps_lap : ∀ la,
  (la = [])%pslap
  → points_of_ps_lap la = [].
Proof.
intros la Hla.
unfold points_of_ps_lap, points_of_ps_lap_gen, qpower_list.
remember O as pow; clear Heqpow; revert pow.
induction la as [| a]; intros; [ reflexivity | simpl ].
apply lap_eq_cons_nil_inv in Hla.
destruct Hla as (Ha, Hla); simpl in Ha.
apply order_inf in Ha; rewrite Ha.
apply IHla; assumption.
Qed.

Lemma sss : ∀ pol ns pol₁ ns₁ c m q₀,
  ns ∈ newton_segments pol
  → m = ps_list_com_polord (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → (root_tail (m * q₀) 0 pol₁ ns₁ =
       root_head n pol₁ ns₁ +
       ps_monom 1%K (γ_sum n pol₁ ns₁) * root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n Hpsi.
remember Hm as HinK1m; clear HeqHinK1m.
apply com_polord_in_K_1_m with (R := R) in HinK1m.
induction n; intros.
 remember Hns₁ as Hini₁; clear HeqHini₁.
 apply exists_ini_pt_nat_fst_seg in Hini₁.
 destruct Hini₁ as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as Hfin₁; clear HeqHfin₁.
 apply exists_fin_pt_nat_fst_seg in Hfin₁.
 destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
 unfold root_tail, root_head; simpl.
 unfold root_tail, root_head; simpl.
 destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [Hps₀| Hps₀].
  pose proof (Hpsi 0%nat (Nat.le_0_l 0)) as H.
  contradiction.

  remember Hns as H; clear HeqH.
  eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
  subst j₁ k₁; simpl.
  unfold Qlt in Hαj₁; simpl in Hαj₁.
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαj₁, Hαk₁.
  remember Hns₁ as HinK₁; clear HeqHinK₁.
  eapply hd_newton_segments in HinK₁; eauto .
  eapply next_pol_in_K_1_mq in HinK₁; eauto .
   erewrite q_eq_1 with (q₀ := q₀) in HinK₁; eauto .
    rewrite Pos.mul_1_r in HinK₁.
    unfold root_head, γ_sum; simpl.
    unfold summation; simpl.
    do 2 rewrite rng_add_0_r.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
    remember Hns₂ as Hini₂; clear HeqHini₂.
    apply exists_ini_pt_nat_fst_seg in Hini₂.
    destruct Hini₂ as (j₂, (αj₂, Hini₂)).
    remember Hns₂ as Hfin₂; clear HeqHfin₂.
    apply exists_fin_pt_nat_fst_seg in Hfin₂.
    destruct Hfin₂ as (k₂, (αk₂, Hfin₂)).
    remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
    eapply hd_newton_segments in Hns₁₁; eauto .
    destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [Hps₁| Hps₁].
     rewrite ps_mul_0_r, ps_add_0_r.
     unfold root_from_cγ_list, ps_monom; simpl.
     rewrite Hini₁, Hfin₁; simpl.
     rewrite Hαk₁; simpl.
     rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
     rewrite Z.mul_shuffle0.
     do 2 rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     rewrite ps_adjust_eq with (n := O) (k := (Qden αj₁ * Qden αk₁)%positive).
     symmetry.
     rewrite ps_adjust_eq with (n := O) (k := (m * q₀)%positive).
     unfold adjust_ps; simpl.
     rewrite fold_series_const.
     do 2 rewrite series_shift_0.
     rewrite series_stretch_const.
     do 2 rewrite Z.sub_0_r.
     symmetry.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto.
      rewrite Pos2Z.inj_mul, <- Z.mul_assoc, Z.mul_comm, Z.mul_assoc.
      rewrite Z.div_mul; auto.
      apply mkps_morphism.
       unfold series_stretch.
       constructor; intros i; simpl.
       destruct (zerop (i mod Pos.to_nat (Qden αj₁ * Qden αk₁))) as [H₁| H₁].
        apply Nat.mod_divides in H₁; auto.
        destruct H₁ as (d, Hd).
        rewrite Nat.mul_comm in Hd.
        rewrite Hd.
        rewrite Nat.div_mul; auto.
        unfold root_series_from_cγ_list.
        rewrite <- Hd.
        destruct (zerop i) as [H₁| H₁].
         subst i.
         apply Nat.eq_mul_0_l in H₁; auto.
         subst d; simpl; rewrite <- Hc₁.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto; contradiction.

         simpl.
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
         destruct d.
          rewrite Hd in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          destruct (lt_dec 0 (S d)) as [H₃| H₃]; [ simpl | reflexivity ].
          destruct (ps_zerop R (ps_poly_nth 0 pol₂)); auto; contradiction.

        destruct (zerop i); [ subst i | reflexivity ].
        rewrite Nat.mod_0_l in H₁; auto.
        exfalso; revert H₁; apply Nat.lt_irrefl.

       rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0.
       rewrite <- Z.mul_assoc, Z.mul_comm; reflexivity.

       rewrite Pos.mul_comm; reflexivity.

      eapply den_αj_divides_num_αj_m; eauto .
      eapply next_pol_in_K_1_mq in HinK1m; eauto .

     remember Hns as Hr₁; clear HeqHr₁.
     eapply multiplicity_1_remains in Hr₁; eauto .
     remember Hns₁₁ as H; clear HeqH.
     eapply r_1_j_0_k_1 in H; try eassumption.
     destruct H as (Hj₂, (Hk₂, (Hαj₂, (Hαk₂, Hoth₂)))).
     subst j₂ k₂; simpl.
     unfold Qlt in Hαj₂; simpl in Hαj₂.
     unfold Qeq in Hαk₂; simpl in Hαk₂.
     rewrite Z.mul_1_r in Hαj₂, Hαk₂.
     unfold root_from_cγ_list; simpl.
     rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
     rewrite Hαk₁, Hαk₂; simpl.
     do 2 rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
     rewrite Z.mul_shuffle0.
     do 2 rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     unfold ps_add, ps_mul; simpl.
     unfold cm; simpl.
     rewrite Hini₁, Hfin₁; simpl.
     rewrite Hαk₁; simpl.
     rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
     rewrite fold_series_const.
     unfold ps_terms_add; simpl.
     rewrite Hini₁, Hfin₁; simpl.
     rewrite Hαk₁; simpl.
     unfold ps_ordnum_add; simpl.
     rewrite Hini₁, Hfin₁; simpl.
     rewrite Hαk₁; simpl.
     rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
     remember (Qden αj₁ * Qden αk₁)%positive as dd.
     rewrite fold_series_const.
     rewrite series_stretch_const.
     rewrite series_mul_1_l.
     remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
     do 2 rewrite Z2Nat_sub_min.
     rewrite Z.mul_add_distr_r.
     remember (m * q₀)%positive as m₁.
     rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
     rewrite Z.sub_add_distr.
     rewrite Z.sub_diag; simpl.
     rewrite Z.add_simpl_l.
     rewrite Z.min_l.
      rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
      unfold adjust_ps; simpl.
      rewrite series_shift_0.
      rewrite Z.sub_0_r.
      apply mkps_morphism.
       Focus 2.
       rewrite Pos2Z.inj_mul, Z.mul_assoc.
       apply Z.mul_cancel_r; auto.
       subst dd nd.
       rewrite Pos2Z.inj_mul, Z.mul_assoc.
       symmetry; rewrite Z.mul_shuffle0.
       apply Z.mul_cancel_r; auto.
       symmetry.
       rewrite Z.mul_comm.
       rewrite <- Z.divide_div_mul_exact; auto.
        rewrite Z.mul_comm.
        rewrite Z.div_mul; auto.

        eapply den_αj_divides_num_αj_m; eauto .
        eapply next_pol_in_K_1_mq in HinK1m; eauto .
        subst m₁; assumption.

       remember Hns₂ as Hns₂₁; clear HeqHns₂₁.
       eapply hd_newton_segments in Hns₂₁; eauto .
       remember Hns₂₁ as H; clear HeqH.
       eapply den_αj_divides_num_αj_m in H; eauto .
       destruct H as (d, Hd).
       rewrite Hd.
       rewrite Z.div_mul; auto.
       destruct d as [| d| d].
        simpl in Hd.
        apply Z.eq_mul_0_l in Hd; auto.
        rewrite Hd in Hαj₂.
        exfalso; revert Hαj₂; apply Z.lt_irrefl.

        simpl.
        unfold adjust_series; simpl.
        rewrite series_shift_0.
        rewrite series_stretch_const.
        rewrite <- series_stretch_stretch.
        rewrite <- Pos.mul_assoc, Pos2Nat.inj_mul.
        rewrite <- stretch_shift_series_distr.
        rewrite <- series_stretch_const with (k := (dd * dd)%positive).
        rewrite <- series_stretch_add_distr.
        apply stretch_morph; [ reflexivity | idtac ].
        unfold series_add; simpl.
        constructor; intros i; simpl.
        destruct (zerop i) as [H₁| H₁].
         subst i; simpl.
         destruct (lt_dec 0 (Pos.to_nat d)) as [H₁| H₁].
          rewrite rng_add_0_r.
          unfold root_series_from_cγ_list; simpl.
          rewrite <- Hc₁.
          destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
          contradiction.

          exfalso; apply H₁; auto.

         rewrite rng_add_0_l.
         assert (next_pow 0 ns₂ m₁ = Pos.to_nat d) as Hnpow.
          unfold next_pow; simpl.
          rewrite Hini₂, Hfin₂; simpl.
          rewrite Hαk₂; simpl.
          rewrite Z.add_0_r, Z.mul_1_r.
          do 2 rewrite Pos.mul_1_r.
          rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
          rewrite Z.div_mul_cancel_r; auto.
          rewrite Hd, Z.div_mul; auto.

          destruct (lt_dec i (Pos.to_nat d)) as [H₂| H₂].
           unfold root_series_from_cγ_list; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [| H₃]; auto.
           destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
           destruct (lt_dec 0 (S i)) as [H₄| ]; auto.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [| H₅]; auto.
           rewrite Hnpow.
           destruct (eq_nat_dec (Pos.to_nat d) (S i)) as [H₆| H₆].
            rewrite H₆ in H₂.
            exfalso; revert H₂; apply Nat.lt_irrefl.

            destruct (lt_dec (Pos.to_nat d) (S i)) as [H₇| ]; auto.
            apply Nat.lt_le_incl, Nat.nlt_ge in H₇.
            contradiction.

           unfold root_series_from_cγ_list; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
            contradiction.

            destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₄| H₄].
             contradiction.

             rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
             destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
             destruct (lt_dec 0 (S i)) as [H₅| H₅].
              apply Nat.nlt_ge in H₂.
              remember (S i - Pos.to_nat d)%nat as id.
              destruct id.
               simpl.
               destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₆| H₆].
                contradiction.

                rewrite Hnpow.
                clear H₆.
                destruct (eq_nat_dec (Pos.to_nat d) (S i)) as [| H₆]; auto.
                destruct (lt_dec (Pos.to_nat d) (S i)) as [H₇| H₇].
                 exfalso; fast_omega Heqid H₇.

                 apply Nat.nlt_ge in H₇.
                 exfalso; fast_omega H₂ H₆ H₇.

               rewrite Hnpow.
               destruct (lt_dec 0 (S id)) as [H₆| H₆].
                remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
                remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
                remember (List.hd phony_ns (newton_segments pol₃)) as ns₃
                 eqn:Hns₃ .
                remember Hns₃ as Hini₃; clear HeqHini₃.
                apply exists_ini_pt_nat_fst_seg in Hini₃.
                destruct Hini₃ as (j₃, (αj₃, Hini₃)).
                remember Hns₃ as Hfin₃; clear HeqHfin₃.
                apply exists_fin_pt_nat_fst_seg in Hfin₃.
                destruct Hfin₃ as (k₃, (αk₃, Hfin₃)).
                remember (next_pow 0 ns₃ m₁) as g₃.
                simpl.
                destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₇| H₇].
                 contradiction.

                 destruct (eq_nat_dec (Pos.to_nat d) (S i)) as [H₈| H₈].
                  rewrite H₈, Nat.sub_diag in Heqid; discriminate Heqid.

                  destruct (lt_dec (Pos.to_nat d) (S i)) as [H₉| H₉].
                   rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                   destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₁₀| H₁₀].
                    destruct i; [ reflexivity | simpl ].
                    destruct (ps_zerop R (ps_poly_nth 0 pol₃)); auto.
                    contradiction.

                    remember Hns₂ as Hr₂; clear HeqHr₂.
                    eapply multiplicity_1_remains with (ns := ns₁) in Hr₂;
                     eauto .
                    remember Hns₂₁ as H; clear HeqH.
                    eapply r_1_j_0_k_1 in H; try eassumption.
                    destruct H as (Hj₃, (Hk₃, (Hαj₃, (Hαk₃, Hoth₃)))).
                    subst j₃ k₃; simpl.
                    unfold Qlt in Hαj₃; simpl in Hαj₃.
                    unfold Qeq in Hαk₃; simpl in Hαk₃.
                    rewrite Z.mul_1_r in Hαj₃, Hαk₃.
                    unfold next_pow in Heqg₃; simpl in Heqg₃.
                    rewrite Hini₃, Hfin₃ in Heqg₃; simpl in Heqg₃.
                    rewrite Hαk₃ in Heqg₃; simpl in Heqg₃.
                    rewrite Z.mul_1_r, Z.add_0_r in Heqg₃.
                    do 2 rewrite Pos.mul_1_r in Heqg₃.
                    rewrite Z.mul_shuffle0 in Heqg₃.
                    rewrite Pos2Z.inj_mul in Heqg₃.
                    rewrite Z.div_mul_cancel_r in Heqg₃; auto.
                    destruct (eq_nat_dec g₃ (S id)) as [H₁₁| H₁₁].
                     remember (next_pow (Pos.to_nat d) ns₃ m₁) as g₄.
                     destruct i; simpl.
                      apply Nat.lt_1_r in H₉.
                      exfalso; revert H₉; apply Pos2Nat_ne_0.

                      clear H₁ H₅ H₆ H₇ H₈.
                      destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₁| H₁].
                       contradiction.

                       clear H₁.
                       destruct (eq_nat_dec g₄ (S (S i))) as [H₁| H₁]; auto.
                       destruct (lt_dec g₄ (S (S i))) as [H₅| H₅].
                        clear H₁.
                        remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
                        remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄
                         eqn:Hpol₄ .
                        remember
                         (List.hd phony_ns (newton_segments pol₄)) as ns₄
                         eqn:Hns₄ .
                        destruct i.
                         simpl.
                         unfold next_pow in Heqg₄.
                         simpl in Heqg₄.
                         rewrite Hini₃, Hfin₃ in Heqg₄; simpl in Heqg₄.
                         rewrite Hαk₃ in Heqg₄; simpl in Heqg₄.
                         rewrite Z.add_0_r, Z.mul_1_r in Heqg₄.
                         do 2 rewrite Pos.mul_1_r in Heqg₄.
                         rewrite Z.mul_shuffle0, Pos2Z.inj_mul in Heqg₄.
                         rewrite Z.div_mul_cancel_r in Heqg₄; auto.
                         rewrite <- Heqg₃, H₁₁ in Heqg₄.
                         remember (Pos.to_nat d) as pd eqn:Hpd .
                         symmetry in Hpd.
                         destruct pd.
                          exfalso; revert Hpd; apply Pos2Nat_ne_0.

                          fast_omega Heqg₄ H₅.

                         simpl.
                         destruct (ps_zerop R (ps_poly_nth 0 pol₄))
                          as [H₁| H₁].
                          unfold next_pow in Heqg₄.
                          simpl in Heqg₄.
                          rewrite Hini₃, Hfin₃ in Heqg₄; simpl in Heqg₄.
                          rewrite Hαk₃ in Heqg₄; simpl in Heqg₄.
                          rewrite Z.add_0_r, Z.mul_1_r in Heqg₄.
                          do 2 rewrite Pos.mul_1_r in Heqg₄.
                          rewrite Z.mul_shuffle0, Pos2Z.inj_mul in Heqg₄.
                          rewrite Z.div_mul_cancel_r in Heqg₄; auto.
                          rewrite <- Heqg₃, H₁₁ in Heqg₄.
                          rewrite Heqid in Heqg₄.
                          rewrite Nat.add_sub_assoc in Heqg₄; auto.
                          rewrite Nat.add_comm, Nat.add_sub in Heqg₄.
                          rewrite <- Heqg₄ in H₅.
                          exfalso; revert H₅; apply Nat.lt_irrefl.

                          Focus 1.
bbb.

intros pol ns pol₁ ns₁ c m Hns Hc Hr Hpol₁ Hns₁ Hm n.
remember Hm as HinK1m; clear HeqHinK1m.
apply com_polord_in_K_1_m with (R := R) in HinK1m.
induction n; intros.
 remember Hns₁ as Hini₁; clear HeqHini₁.
 apply exists_ini_pt_nat_fst_seg in Hini₁.
 destruct Hini₁ as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as Hfin₁; clear HeqHfin₁.
 apply exists_fin_pt_nat_fst_seg in Hfin₁.
 destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
 destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [Hps₀| Hps₀].
 remember Hns as H; clear HeqH.
 eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁; simpl.
 unfold Qlt in Hαj₁; simpl in Hαj₁.
 unfold Qeq in Hαk₁; simpl in Hαk₁.
 rewrite Z.mul_1_r in Hαj₁, Hαk₁.
 remember Hns₁ as HinK₁; clear HeqHinK₁.
 eapply hd_newton_segments in HinK₁; eauto .
 eapply next_pol_in_K_1_mq in HinK₁; eauto .
 erewrite q_eq_1 in HinK₁; eauto .
 rewrite Pos.mul_1_r in HinK₁.
 unfold root_head, γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 unfold root_tail; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember Hns₂ as Hini₂; clear HeqHini₂.
 apply exists_ini_pt_nat_fst_seg in Hini₂.
 destruct Hini₂ as (j₂, (αj₂, Hini₂)).
 remember Hns₂ as Hfin₂; clear HeqHfin₂.
 apply exists_fin_pt_nat_fst_seg in Hfin₂.
 destruct Hfin₂ as (k₂, (αk₂, Hfin₂)).
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply hd_newton_segments in Hns₁₁; eauto .
 remember Hns₁₁ as H; clear HeqH.
 eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₂, (Hk₂, (Hαj₂, (Hαk₂, Hoth₂)))).
  subst j₂ k₂.
  unfold Qlt in Hαj₂; simpl in Hαj₂.
  unfold Qeq in Hαk₂; simpl in Hαk₂.
  rewrite Z.mul_1_r in Hαj₂, Hαk₂.
bbb.

(* false because we must start after r=1 *)
Lemma sss₁ : ∀ pol ns n c₁ m,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → m = ps_list_com_polord (al pol)
  → (root_tail m 0 pol ns =
     root_head n pol ns +
     ps_monom 1%K (γ_sum n pol ns) * root_tail m (S n) pol ns)%ps.
Proof.
intros pol ns n c₁ m Hns Hc₁ Hr Hm.
remember Hm as HinK1m; clear HeqHinK1m.
apply com_polord_in_K_1_m with (R := R) in HinK1m.
revert pol ns c₁ m Hns Hc₁ Hr Hm HinK1m.
induction n; intros.
 unfold root_head, γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 unfold root_tail; simpl.
 rewrite <- Hc₁.
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember Hns as HinK1mq; clear HeqHinK1mq.
 eapply next_pol_in_K_1_mq in HinK1mq; eauto .
bbb.
 remember (q_of_ns pol ns) as q eqn:Hq.
 remember Hns as Hini; clear HeqHini.
 apply exists_ini_pt_nat in Hini.
 destruct Hini as (j, (αj, Hini)).
 remember Hns as Hfin; clear HeqHfin.
 apply exists_fin_pt_nat in Hfin.
 destruct Hfin as (k, (αk, Hfin)).
 remember Hns₁ as Hini₁; clear HeqHini₁.
 apply exists_ini_pt_nat_fst_seg in Hini₁.
 destruct Hini₁ as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as Hfin₁; clear HeqHfin₁.
 apply exists_fin_pt_nat_fst_seg in Hfin₁.
 destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
 assert (j < k)%nat as Hjk.
  eapply j_lt_k; try eassumption.
   rewrite Hini; simpl; rewrite nat_num_Qnat; reflexivity.

   rewrite Hfin; simpl; rewrite nat_num_Qnat; reflexivity.

  remember Hns as H; clear HeqH.
  eapply r_1_j_0_k_1 in H; try eassumption.
   destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
   subst j₁ k₁.
   unfold Qnat in Hini₁, Hfin₁; simpl in Hini₁, Hfin₁.
   unfold Qeq in Hαk₁; simpl in Hαk₁.
   rewrite Z.mul_1_r in Hαk₁.
   unfold Qlt in Hαj₁; simpl in Hαj₁.
   rewrite Z.mul_1_r in Hαj₁.
   unfold root_from_cγ_list; simpl.
   unfold γ; simpl.
   rewrite Hini, Hfin, Hini₁, Hfin₁; simpl.
   unfold ps_mul; simpl.
   unfold cm; simpl.
   rewrite fold_series_const.
   unfold ps_add; simpl.
   unfold cm; simpl.
   remember (Qden αj * Qden αk)%positive as dd.
   remember (Qnum αj * ' Qden αk)%Z as nd.
   unfold ps_ordnum_add; simpl.
   rewrite <- Heqdd, <- Heqnd, Hαk₁.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   rewrite Z.add_0_r, Pos.mul_1_r.
   do 2 rewrite Z.mul_1_r.
   rewrite Z.min_l.
    unfold ps_terms_add; simpl.
    rewrite fold_series_const.
    rewrite <- Heqdd, <- Heqnd.
    rewrite Qnum_inv_Qnat_sub; auto.
    rewrite Qden_inv_Qnat_sub; auto.
    rewrite Z.mul_1_r.
    rewrite Z.min_l.
     rewrite Z.min_r.
      rewrite Z.sub_diag; simpl.
      unfold adjust_series.
      rewrite series_shift_0.
      remember (dd * Pos.of_nat (k - j))%positive as ddkj.
      rewrite ps_adjust_eq with (n := O) (k := (ddkj * ddkj)%positive).
      unfold adjust_ps; simpl.
      rewrite series_shift_0.
      rewrite Z.sub_0_r.
      subst dd nd ddkj.
      remember (Pos.of_nat (k - j)) as kj.
      rewrite Z.mul_opp_l, Z.add_opp_r.
      repeat rewrite Pos.mul_assoc.
      repeat rewrite Pos2Z.inj_mul.
      apply mkps_morphism.
       do 2 rewrite series_stretch_const.
       rewrite series_mul_1_l.
       remember (Qnum αj * ' Qden αk)%Z as nd.
       remember (Qnum αk * ' Qden αj)%Z as dn.
       remember (Qnum αj₁ * ' Qden αk₁)%Z as nd₁.
       rewrite <- Pos2Z.inj_mul.
       rewrite <- Pos2Z.inj_mul.
       remember (Qden αj * Qden αk)%positive as dd.
       remember (Qden αj₁ * Qden αk₁)%positive as dd₁.
       do 2 rewrite <- Pos.mul_assoc.
       rewrite Pos.mul_comm.
       do 2 rewrite Pos.mul_assoc.
       rewrite <- Heqdd.
       rewrite Z.mul_add_distr_r.
       rewrite Z.mul_shuffle0.
       do 5 rewrite Z.mul_assoc.
       rewrite Z.add_simpl_l.
       rewrite Z.mul_comm in Heqnd₁.
       rewrite Pos.mul_comm in Heqdd₁.
       subst nd₁ dd₁.
       rewrite Pos2Z.inj_mul.
       do 4 rewrite <- Z.mul_assoc.
       rewrite Z.div_mul_cancel_l; auto.
       do 2 rewrite Z.mul_assoc.
       rewrite <- Pos2Z.inj_mul.
       rewrite Z2Nat.inj_mul; simpl; auto.
        rewrite <- stretch_shift_series_distr.
        rewrite <- Z.mul_assoc.
        rewrite <- Pos2Z.inj_mul.
        rewrite Z2Nat.inj_mul; simpl; auto.
         rewrite <- stretch_shift_series_distr.
         rewrite <- series_stretch_stretch.
         rewrite Pos.mul_assoc.
         rewrite <- series_stretch_const.
         rewrite <- series_stretch_add_distr.
         apply stretch_morph; [ reflexivity | idtac ].
         unfold series_add; simpl.
         constructor; intros i; simpl.
         destruct (zerop i) as [H₁| H₁].
          subst i; simpl.
          remember (Qnum αj₁ * ' m / ' Qden αj₁)%Z as nmd.
          destruct (lt_dec 0 (Z.to_nat nmd)) as [H₁| H₁].
           rewrite rng_add_0_r.
           unfold root_series_from_cγ_list; simpl.
           rewrite <- Hc₁.
           destruct (ac_zerop c₁); [ symmetry; assumption | reflexivity ].

           exfalso; apply H₁; clear H₁.
           assert (in_K_1_m (ps_lap_nth 0 (al pol₁)) (m * q)) as Hin.
            eapply ps_lap_forall_forall in HinK1mq; eauto .
             intros a b Hab Hamq.
             rewrite <- Hab; assumption.

             apply ps_lap_in_0th.
             eapply next_lap_not_nil; eauto .
             rewrite Hpol₁; reflexivity.

            inversion Hin.
            destruct H as (ps, (Hps, Hpo)).
            remember Hini₁ as H; clear HeqH.
            replace 0 with (Qnat 0) in H by reflexivity.
            eapply rrr in H; eauto .
            destruct H as (c, Hc).
bbb.

Lemma uuu₂ : ∀ pol ns n,
  ns ∈ newton_segments pol
  → (root_head n pol ns +
       ps_monom 1%K (γ_sum n pol ns) * root_tail n pol ns =
     root_head (S n) pol ns +
       ps_monom 1%K (γ_sum (S n) pol ns) * root_tail (S n) pol ns)%ps.
Proof.
intros pol ns n Hns.
revert pol ns Hns.
induction n; intros.
 unfold root_head, root_tail; simpl.
 unfold summation; simpl.
 do 2 rewrite ps_add_0_r.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 rewrite rng_add_0_r.
 rewrite rng_add_0_r.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
 apply ttt with (n := 0%nat) in Hns.
 simpl in Hns.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hns.
 rewrite <- Hc₂ in Hns.
 unfold root_tail in Hns.
 simpl in Hns.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hns.
bbb.

Lemma uuu : ∀ pol ns n,
  let qr := Q_ring in
  (root_head (S n) pol ns =
   root_head n pol ns +
   ps_monom (nth_c n pol ns) (Σ (i = 0, n), nth_γ i pol ns))%ps.
Proof.
intros pol ns n qr.
revert pol ns.
induction n; intros.
 simpl.
 unfold summation; simpl.
 rewrite ps_mul_0_r, ps_add_0_r, ps_add_0_l, rng_add_0_r.
 reflexivity.

 remember (S n) as n₁; simpl; subst n₁.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.

Lemma vvv : ∀ pol ns n,
  (root_when_r_1 pol ns =
   root_head n pol ns +
   root_when_r_1 (nth_pol n pol ns) (nth_ns n pol ns))%ps.
Proof.
intros pol ns n.
revert pol ns.
induction n; intros; [ rewrite ps_add_0_l; reflexivity | idtac ].
bbb.
destruct n.
 simpl.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite ps_mul_0_r, ps_add_0_r.
bbb.

intros pol ns n.
revert pol ns.
induction n; intros; [ rewrite ps_add_0_l; reflexivity | idtac ].
remember (root_head (S n)) as x; simpl; subst x.
remember (next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))) as pol₁.
rename Heqpol₁ into Hpol₁.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.

(*
Fixpoint ps_poly_root m pol ns :=
  match m with
  | 0%nat => None
  | S m₁ =>
      let c := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c in
      if ps_zerop R (List.hd ps_zero (al pol₁)) then
        Some (ps_monom c (γ ns))
      else
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        let r := root_multiplicity acf c (Φq pol ns) in
        if eq_nat_dec r 1 then Some (root_when_r_1 pol ns)
        else if infinite_with_same_r r pol₁ ns₁ then ...
        else
          match ps_poly_root m₁ pol₁ ns₁ with
          | None => None
          | Some y => Some (ps_monom c (γ ns) + ps_monom 1%K (γ ns) * y)%ps
          end
  end.
*)

(*
Lemma yyy₁ : ∀ pol ns m ps,
  ns = List.hd phony_ns (newton_segments pol)
  → ps_poly_root m pol ns = Some ps
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m ps Hns Hps.
revert pol ns ps Hns Hps.
induction m; intros; [ discriminate Hps | simpl in Hps ].
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ps_poly_root m pol₁ ns₁) as pso eqn:Hpso .
symmetry in Hpso.
unfold next_pol in Hpol₁.
remember (next_lap (al pol) (β ns) (γ ns) c) as la₁ eqn:Hla₁ .
destruct (ps_zerop R (List.hd 0%ps la₁)) as [Hz| Hnz].
 injection Hps; clear Hps; intros Hps.
 rewrite <- Hps; simpl.
 eapply f₁_root_f_root with (y₁ := 0%ps).
  unfold next_pol.
  rewrite Hla₁ in Hpol₁.
  eassumption.

  rewrite ps_mul_0_r, ps_add_0_r; reflexivity.

  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  rewrite Hpol₁; simpl.
  destruct la₁ as [| a]; [ reflexivity | simpl ].
  simpl in Hz.
  rewrite Hz, ps_mul_0_r, ps_add_0_r; reflexivity.

 destruct pso as [ps₁| ]; [ idtac | discriminate Hps ].
 injection Hps; clear Hps; intros Hps.
 apply IHm in Hpso; [ idtac | assumption ].
 symmetry in Hps.
 subst la₁.
 eapply f₁_root_f_root; try eassumption.
 rewrite Hps; reflexivity.
Qed.
*)

(*
Lemma yyy : ∀ pol ns m ps,
  degree (ps_zerop R) pol ≥ 1
  → ns ∈ newton_segments pol
  → ps_poly_root m pol ns = Some ps
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m ps Hdeg Hns Hps.
revert pol ns ps Hdeg Hns Hps.
induction m; intros; [ discriminate Hps | simpl in Hps ].
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ps_poly_root m pol₁ ns₁) as pso eqn:Hpso .
symmetry in Hpso.
unfold next_pol in Hpol₁.
remember (next_lap (al pol) (β ns) (γ ns) c) as la₁ eqn:Hla₁ .
destruct (ps_zerop R (List.hd 0%ps la₁)) as [Hz| Hnz].
 injection Hps; clear Hps; intros Hps.
 rewrite <- Hps; simpl.
 eapply f₁_root_f_root with (y₁ := 0%ps).
  unfold next_pol.
  rewrite Hla₁ in Hpol₁.
  eassumption.

  rewrite ps_mul_0_r, ps_add_0_r; reflexivity.

  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  rewrite Hpol₁; simpl.
  destruct la₁ as [| a]; [ reflexivity | simpl ].
  simpl in Hz.
  rewrite Hz, ps_mul_0_r, ps_add_0_r; reflexivity.

 destruct pso as [ps₁| ]; [ idtac | discriminate Hps ].
 injection Hps; clear Hps; intros Hps.
 apply IHm in Hpso.
  symmetry in Hps.
  subst la₁.
  eapply f₁_root_f_root; try eassumption.
  rewrite Hps; reflexivity.
bbb.
*)

Lemma zzz : ∀ pol ns c₁ ps pol₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ps = root_when_r_1 pol ns
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
 Focus 2.
 apply order_inf.
 unfold order.
 remember (ps_terms (ps_pol_apply pol₁ ps₁)) as s eqn:Hs .
 remember (null_coeff_range_length R s 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ]; [ exfalso | reflexivity ].
 apply null_coeff_range_length_iff in Hv.
 unfold null_coeff_range_length_prop in Hv; simpl in Hv.
 destruct Hv as (Hiv, Hv).
 apply Hv; clear Hv.
 rewrite Hs.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
 Focus 2.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 rewrite Hpol₁; simpl.
 unfold next_lap; simpl.
 rewrite apply_lap_mul.
 simpl.
 rewrite ps_mul_0_l, ps_add_0_l.
 rewrite apply_lap_compose; simpl.
 rewrite ps_mul_0_l, ps_add_0_l.
 rewrite Hps₁; simpl.
 unfold root_when_r_1; simpl.
 rewrite Hini₁, Hfin₁; simpl.
 rewrite Z.mul_1_r, Pos.mul_1_r.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
apply order_inf.
unfold order.
remember (ps_terms (ps_pol_apply pol ps)) as s eqn:Hs .
remember (null_coeff_range_length R s 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; [ exfalso | reflexivity ].
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv; simpl in Hv.
destruct Hv as (Hiv, Hv).
apply Hv; clear Hv.
rewrite Hs.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
bbb.
 eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
  Focus 2.
  apply order_inf.
  unfold order.
  remember (ps_terms (ps_pol_apply pol₁ ps₁)) as s₁ eqn:Hs₁ .
  remember (null_coeff_range_length R s₁ 0) as v₁ eqn:Hv₁ .
  symmetry in Hv₁.
  destruct v₁ as [v₁| ]; [ exfalso | reflexivity ].
  apply null_coeff_range_length_iff in Hv₁.
  unfold null_coeff_range_length_prop in Hv₁; simpl in Hv₁.
  destruct Hv₁ as (Hiv₁, Hv₁).
  apply Hv₁; clear Hv₁.
  rewrite Hs₁; simpl.
  rewrite Hps₁; simpl.
  unfold root_when_r_1; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Z.mul_1_r, Pos.mul_1_r.
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαk₁.
  rewrite Hαk₁.
  rewrite Z.mul_0_l, Z.add_0_r.
  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  unfold apply_lap; simpl.
  assert ({| terms := root_term_when_r_1 pol₁ ns₁ |} = 0)%ser as Hsz.
   apply series_null_coeff_range_length_inf_iff.
   apply null_coeff_range_length_iff.
   unfold null_coeff_range_length_prop; simpl.
   intros i.
   unfold root_term_when_r_1; simpl.
   rewrite Hini₁, Hfin₁; simpl.
   rewrite Pos.mul_1_r.
bbb.

intros pol ns c₁ ps Hns Hc₁ Hr Hps.
remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
 apply order_inf.
 unfold order.
 remember (ps_terms (ps_pol_apply pol ps)) as s eqn:Hs .
 remember (null_coeff_range_length R s 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ]; [ exfalso | reflexivity ].
 apply null_coeff_range_length_iff in Hv.
 unfold null_coeff_range_length_prop in Hv; simpl in Hv.
 destruct Hv as (Hiv, Hv).
 apply Hv; clear Hv.
 rewrite Hs; simpl.
 rewrite Hps; simpl.
 unfold root_when_r_1; simpl.
 rewrite Hini, Hfin; simpl.
 rewrite Qnum_inv; simpl.
  rewrite Z.mul_1_r.
bbb.

intros pol ns c₁ ps Hns Hc₁ Hr Hps.
remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
 eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
  rewrite Hps, Hps₁.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  rewrite Hini, Hfin; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Pos.mul_1_r.
  rewrite Z.mul_1_r.
  unfold Qeq in Hαk₁.
  simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαk₁.
  rewrite Hαk₁.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  rewrite Pos2Z.inj_mul.
  rewrite Pos2Z.inj_mul.
  rewrite Pos2Z.inj_mul.
  rewrite Qden_inv.
   rewrite Qnum_inv.
bbb.

(*
Lemma zzz : ∀ pol ns m,
  ns = List.hd phony_ns (newton_segments pol)
  → polydromy_if_r_reaches_one acf m pol ≠ 0%nat
  → ∃ ps, (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m Hns Hpnz.
revert pol ns Hns Hpnz.
induction m; intros; [ exfalso; apply Hpnz; reflexivity | idtac ].
simpl in Hpnz.
rewrite <- Hns in Hpnz.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
destruct (eq_nat_dec r 1) as [Hr1| Hrn1].
 subst r; clear Hpnz.
bbb.
 exists (root_when_r_1 pol ns).
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember (root_when_r_1 pol₁ ns₁) as y₁ eqn:Hy₁ .
 eapply f₁_root_f_root with (y₁ := y₁); try eassumption.
bbb.

intros pol ns c₁ c₂ pol₁ ns₁ m.
intros Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂ Hpnz.
remember (polydromy_if_r_one acf m pol) as p eqn:Hp .
revert pol pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂ Hp.
induction m; [ contradiction | intros ].
simpl in Hp.
rewrite <- Hns in Hp.
destruct (ac_zerop (ac_root (Φq pol ns))) as [Hz| Hnz].
 remember Hpol₁ as H; clear HeqH.
 eapply multiplicity_1_remains in H; try eassumption.
bbb.

bbb.
remember Hpol₁ as H; clear HeqH.
eapply f₁_root_f_root in H; [ idtac | reflexivity | idtac ].
bbb.
*)

End theorems.
