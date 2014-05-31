(* Puiseux.v *)

Require Import Utf8 QArith NPeano Sorting.

Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import Qbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
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

Set Implicit Arguments.

Lemma Qnat_0 : ∀ A h (αh v : A), (Qnat h, αh) = (0, v) → h = 0%nat.
Proof.
intros A h αh v H.
injection H; clear H; intros H1 H; subst.
rewrite <- Nat2Z.inj_0 in H.
apply Nat2Z.inj in H.
assumption.
Qed.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition phony_ns :=
  {| ini_pt := (0, 0); fin_pt := (0, 0); oth_pts := [] |}.

(* f₁(x,y₁) = 0 => f(x,c₁.x^γ+x^γ.y₁) = 0 *)
Lemma f₁_root_f_root : ∀ f f₁ β γ c₁ y y₁,
  f₁ = next_pol f β γ c₁
  → y = (ps_monom c₁ γ + ps_monom 1%K γ * y₁)%ps
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
  → (j = 0)%nat ∧ (k = 1)%nat ∧ 0 < αj ∧ αk == 0 ∧ seg ms = [].
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

Lemma r_1_j_0_k_1 : ∀ pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
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
revert Hns₁ Hini₁ Hfin₁ Hps₀ Hnneg Hpos Hz; clear; intros.
rename pol₁ into pol.
rename ns₁ into ns.
rename j₁ into j.
rename αj₁ into αj.
rename k₁ into k.
rename αk₁ into αk.
rename Hns₁ into Hns.
rename Hini₁ into Hini.
rename Hfin₁ into Hfin.
assert (0 < 1)%nat as H by apply Nat.lt_0_1.
apply Hpos in H; clear Hpos; rename H into Hpos.
unfold newton_segments in Hns; simpl in Hns.
unfold points_of_ps_polynom in Hns; simpl in Hns.
unfold ps_poly_nth in Hps₀, Hnneg, Hz, Hpos.
remember (al pol) as la.
clear pol Heqla.
unfold ps_lap_nth in Hps₀.
destruct la as [| a₀].
 exfalso; apply Hps₀; rewrite order_0; reflexivity.

 unfold ps_lap_nth in Hnneg, Hz, Hpos.
 simpl in Hps₀, Hz, Hpos.
 unfold points_of_ps_lap in Hns.
 unfold points_of_ps_lap_gen in Hns.
 simpl in Hns.
 remember (order a₀) as v₀.
 symmetry in Heqv₀.
 destruct v₀ as [v₀| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
 clear Hps₀.
 destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].
 simpl in Hz, Hns.
 remember (order a₁) as v₁.
 symmetry in Heqv₁.
 destruct v₁ as [v₁| ]; [ idtac | contradiction ].
 apply Qbar.qfin_inj in Hz.
 apply Qbar.qfin_lt_mono in Hpos.
 remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
 simpl in Hns.
 remember (filter_finite_ord R (List.map f (power_list 2 la))) as ffo.
 remember (minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo) as ms.
 subst ns; simpl in Hini, Hfin.
 rewrite Heqms, minimised_slope_beg_pt in Hini.
 eapply pouet; eassumption.
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

Lemma zzz : ∀ pol ns c₁ c₂ pol₁ ns₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₂ = ac_root (Φq pol₁ ns₁) ∧ (c₂ ≠ 0)%K
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
     revert Hnneg Hpos Hz Hpts; clear; intros.
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
     Focus 1.
bbb.

(* following code abandonned, I used another trick *)
(* to be able to use r_1_j_0_k_1 above *)
assert (ns₁ ∈ newton_segments pol₁) as Hns₁in.
 rewrite Hns₁.
 remember (newton_segments pol₁) as nsl.
 symmetry in Heqnsl.
 destruct nsl as [| ns₂].
  Focus 1.
  unfold newton_segments in Heqnsl.
  remember (lower_convex_hull_points (points_of_ps_polynom pol₁)) as chpts.
  symmetry in Heqchpts.
  destruct chpts as [| pt₁].
   unfold lower_convex_hull_points in Heqchpts.
   remember (points_of_ps_polynom pol₁) as pts.
   symmetry in Heqpts.
   destruct pts as [| pt₁].
    unfold points_of_ps_polynom in Heqpts.
    unfold points_of_ps_lap in Heqpts.
    unfold points_of_ps_lap_gen in Heqpts.
    remember (qpower_list 0 (al pol₁)) as pl.
    symmetry in Heqpl.
    destruct pl as [| p].
     unfold qpower_list in Heqpl.
bbb.

remember Hns₁in as Hini₁; clear HeqHini₁.
remember Hns₁in as Hfin₁; clear HeqHfin₁.
apply exists_ini_pt_nat in Hini₁.
apply exists_fin_pt_nat in Hfin₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
rewrite Hini₁, Hfin₁; simpl.

rewrite nat_num_Qnat.
remember Hr as Hjk; clear HeqHjk.
eapply r_1_j_0_k_1 in Hjk; try eassumption.
destruct Hjk as (Hj, (Hk, (Hαj, (Hαk, Hoth)))).
subst j₁ k₁.
rewrite fold_char_pol with (αj := αj₁).
rewrite Hoth; simpl.
rewrite nat_num_Qnat; simpl.
rewrite nat_num_Qnat; simpl.
unfold Φq in Hc₂.
rewrite Hini₁ in Hc₂; simpl in Hc₂.
rewrite nat_num_Qnat in Hc₂.
unfold poly_left_shift in Hc₂.
rewrite list_skipn_0 in Hc₂.
simpl in Hc₂.
rewrite Nat.sub_diag in Hc₂.
rewrite Hini₁ in Hc₂; simpl in Hc₂.
rewrite nat_num_Qnat in Hc₂.
rewrite Hoth, Hfin₁ in Hc₂; simpl in Hc₂.
rewrite nat_num_Qnat in Hc₂.
remember (order_coeff (List.nth 0 (al pol₁) 0%ps)) as v₀.
remember (order_coeff (List.nth 1 (al pol₁) 0%ps)) as v₁.
remember POL [v₀; v₁ … []]%pol as cpol.
assert (apply_poly cpol c₂ = 0)%K as Happ.
 destruct Hc₂ as (Hc₂, Hc₂nz).
 rewrite Hc₂.
 apply ac_prop_root.
 subst cpol; simpl.
 unfold degree; simpl.
 destruct (ac_zerop v₁) as [H₁| H₁].
  exfalso.
  unfold order_coeff in Heqv₁.
  symmetry in Heqv₁.
  remember (List.nth 1 (al pol₁) 0%ps) as a₁.
  remember (null_coeff_range_length R (ps_terms a₁) 0) as v.
  symmetry in Heqv.
  destruct v as [v| ].
   apply null_coeff_range_length_iff in Heqv.
   unfold null_coeff_range_length_prop in Heqv.
   simpl in Heqv.
   destruct Heqv as (_, Heqv).
   rewrite Heqv₁ in Heqv.
   contradiction.

   apply null_coeff_range_length_iff in Heqv.
   unfold null_coeff_range_length_prop in Heqv.
   simpl in Heqv.
bbb.

End theorems.
