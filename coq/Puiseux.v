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
Require Import Q_field.

Set Implicit Arguments.

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

(*
Lemma j_0_k_r : ∀ pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ r,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → r = root_multiplicity acf c₁ (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ k₁ ≤ r ∧ αj₁ > 0 ∧ αk₁ == 0 ∧ oth_pts ns₁ = [].
Proof.
intros pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ r.
intros Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
destruct r.
 exfalso; symmetry in Hr; revert Hr.
 apply root_multiplicity_ne_0; assumption.

 eapply f₁_orders in H; try eassumption.
 destruct H as (Hnneg, (Hpos, Hz)).
 revert Hns₁ Hini₁ Hfin₁ Hps₀ Hnneg Hpos Hz; clear; intros.
 assert (0 < S r)%nat as H by apply Nat.lt_0_succ.
 apply Hpos in H; clear Hpos; rename H into Hpos.
 unfold newton_segments in Hns₁; simpl in Hns₁.
 unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
 unfold ps_poly_nth in Hps₀, Hnneg, Hz, Hpos.
 remember (al pol₁) as la.
 clear pol₁ Heqla.
 unfold ps_lap_nth in Hps₀.
 destruct la as [| a₀].
  exfalso; apply Hps₀; rewrite order_0; reflexivity.

  unfold ps_lap_nth in Hnneg, Hz, Hpos.
  simpl in Hps₀, Hz, Hpos.
  unfold points_of_ps_lap in Hns₁.
  unfold points_of_ps_lap_gen in Hns₁.
  simpl in Hns₁.
  remember (order a₀) as v₀.
  symmetry in Heqv₀.
  destruct v₀ as [v₀| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
  clear Hps₀.
  remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
  remember (filter_finite_ord R (List.map f (power_list 1 la))) as ffo.
  remember 1%nat as pow eqn:Hpow  in Heqffo.
  assert (1 ≤ pow)%nat as H by omega.
  clear Hpow; rename H into Hpow.
  revert la pow Heqffo Hnneg Hz Hpow.
  induction r; intros.
   destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].
   simpl in Hz, Hns₁.
   remember (order a₁) as v₁.
   symmetry in Heqv₁.
   destruct v₁ as [v₁| ]; [ idtac | contradiction ].
   apply Qbar.qfin_inj in Hz.
   apply Qbar.qfin_lt_mono in Hpos.
   simpl in Heqffo.
   rewrite Heqf in Heqffo; simpl in Heqffo.
   rewrite <- Heqf in Heqffo.
   rewrite Heqv₁ in Heqffo.
   subst ffo ns₁; simpl in Hini₁, Hfin₁; simpl.
   rewrite minimised_slope_beg_pt in Hini₁.
   remember (filter_finite_ord R (List.map f (power_list (S pow) la))) as ffo.
   remember (minimise_slope (Qnat 0, v₀) (Qnat pow, v₁) ffo) as ms.
bbb.
   eapply pouet in Heqf; try eassumption; try reflexivity.
   destruct Heqf as (H₁, (H₂, (H₃, (H₄, (H₅, H₆))))).
   split; [ assumption | idtac ].
   split; [ assumption | idtac ].
   split; [ assumption | idtac ].
   split; assumption.

   destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].
   simpl in Hz, Hns₁, Heqffo.
   rewrite Heqf in Heqffo; simpl in Heqffo; rewrite <- Heqf in Heqffo.
bbb.
*)

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
 eapply pouet in Hfin; try eassumption.
 destruct Hfin as (H₁, (H₂, (H₃, (H₄, (H₅, H₆))))).
 split; [ assumption | idtac ].
 split; [ omega | idtac ].
 split; [ assumption | idtac ].
 split; assumption.
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
bbb.
unfold same_r in Hsr.
rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hsr.
remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
do 2 rewrite Φq_pol in Hsr.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember [ini_pt ns₁ … oth_pts ns₁ ++ [fin_pt ns₁]] as pl₁ eqn:Hpl₁ .
unfold root_multiplicity in Hsr.
simpl in Hsr.
bbb.
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

Fixpoint find_coeff max_iter pow pol_ord pol ns i :=
  match max_iter with
  | 0%nat => 0%K
  | S m =>
      let c₁ := ac_root (Φq pol ns) in
      if eq_nat_dec pow i then c₁
      else if lt_dec pow i then
        let γ₁ := snd (ini_pt ns) in
        let pow₁ := (pow + nat_num (Qred (γ₁ * inject_Z ('pol_ord))))%nat in
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        find_coeff m pow pol_ord pol₁ ns₁ i
      else 0%K
  end.

Definition root_series_from_cγ_list pol ns i :=
  if zerop (i mod Pos.to_nat (Qden (γ ns))) then
    find_coeff (S i) 0%nat (Qden (γ ns)) pol ns i
  else 0%K.

Definition root_from_cγ_list pol ns :=
  {| ps_terms := {| terms := root_series_from_cγ_list pol ns |};
     ps_ordnum := Qnum (γ ns);
     ps_polord := Qden (γ ns) |}.

Definition γ_sum n pol ns :=
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ i pol ns.

Definition root_head n pol ns :=
  let pr := ps_ring R in
  Σ (i = 0, n), ps_monom (nth_c i pol ns) (γ_sum i pol ns).

Definition root_tail n pol ns :=
  root_from_cγ_list (nth_pol n pol ns) (nth_ns n pol ns).

Lemma find_coeff_le: ∀ pol nc po m i,
  (m ≤ i)%nat
  → find_coeff m 0 po pol nc i = 0%K.
Proof.
intros pol nc po m i Him.
revert pol nc i Him.
induction m; intros; [ reflexivity | idtac ].
remember O as z; simpl; subst z.
destruct (eq_nat_dec 0 i) as [H₁| H₁].
 exfalso; fast_omega Him H₁.

 destruct (lt_dec 0 i) as [H₂| H₂]; [ idtac | reflexivity ].
 apply IHm; omega.
Qed.

Lemma sss : ∀ pol ns n αj αk,
  ns ∈ newton_segments pol
  → αj > 0
  → αk == 0
  → ini_pt ns = (0, αj)
  → fin_pt ns = (1, αk)
  → (root_tail 0 pol ns =
     root_head n pol ns +
     ps_monom 1%K (γ_sum n pol ns) * root_tail (S n) pol ns)%ps.
Proof.
intros pol ns n αj αk Hns Hαj Hαk Hini Hfin.
revert pol ns αj αk Hns Hαj Hαk Hini Hfin.
induction n; intros.
 unfold root_head, γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 unfold root_tail; simpl.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
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
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαk₁.
  unfold Qlt in Hαj₁; simpl in Hαj₁.
  rewrite Z.mul_1_r in Hαj₁.
  unfold Qnat in Hini₁, Hfin₁.
  simpl in Hini₁, Hfin₁.
  unfold Qlt in Hαj; simpl in Hαj.
  rewrite Z.mul_1_r in Hαj.
  unfold Qeq in Hαk; simpl in Hαk.
  rewrite Z.mul_1_r in Hαk.
  unfold root_from_cγ_list; simpl.
  rewrite Hini, Hfin, Hini₁, Hfin₁; simpl.
  rewrite Hαk, Hαk₁.
  rewrite Z.mul_0_l, Z.add_0_r.
  rewrite Z.mul_0_l, Z.add_0_r.
  rewrite Z.mul_1_r, Pos.mul_1_r.
  rewrite Z.mul_1_r, Pos.mul_1_r.
  unfold ps_mul; simpl.
  unfold cm; simpl.
  rewrite Hini, Hfin; simpl.
  unfold ps_add; simpl.
  unfold cm; simpl.
  rewrite Hini, Hfin; simpl.
  rewrite Pos.mul_1_r.
  rewrite Hαk; simpl.
  rewrite Z.add_0_r, Z.mul_1_r.
  remember (Qden αj * Qden αk)%positive as dd.
  remember (Qnum αj * ' Qden αk)%Z as nd.
  remember (Qden αj₁ * Qden αk₁)%positive as dd₁.
  unfold ps_ordnum_add; simpl.
  rewrite Hini, Hfin; simpl.
  rewrite <- Heqdd.
  rewrite <- Heqnd.
  rewrite Z.mul_1_r.
  rewrite Pos.mul_1_r.
  rewrite Z.min_l.
   unfold ps_terms_add; simpl.
   rewrite Hini, Hfin; simpl.
   rewrite Z.mul_1_r.
   rewrite Pos.mul_1_r.
   rewrite <- Heqdd.
   rewrite <- Heqnd.
   rewrite Hαk; simpl.
   rewrite Z.add_0_r.
   rewrite Z.min_l.
    rewrite Z.min_r.
     rewrite Z.sub_diag; simpl.
     unfold adjust_series.
     rewrite series_shift_0.
     rewrite ps_adjust_eq with (n := O) (k := (dd * dd₁)%positive).
     unfold adjust_ps; simpl.
     rewrite Z.sub_0_r.
     apply mkps_morphism; try reflexivity.
     rewrite series_shift_0.
     rewrite Z.mul_add_distr_r.
     rewrite Z.mul_shuffle0.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     rewrite Z.add_simpl_l.
     rewrite Z2Nat.inj_mul.
      simpl.
      rewrite <- stretch_shift_series_distr.
      rewrite fold_series_const.
      rewrite fold_series_const.
      rewrite stretch_series_const.
      rewrite stretch_series_const.
      symmetry.
      rewrite <- stretch_series_const with (k := dd).
      rewrite <- series_stretch_add_distr.
      rewrite series_add_comm.
      rewrite <- stretch_series_const with (k := dd).
      rewrite <- series_stretch_mul.
      rewrite series_mul_1_l.
      rewrite Z2Nat.inj_mul.
       simpl.
       rewrite <- stretch_shift_series_distr.
       rewrite <- stretch_series_const with (k := dd).
       remember (Qnum αj₁ * ' Qden αk₁)%Z as nd₁.
       rewrite <- series_stretch_add_distr.
       rewrite <- series_stretch_stretch.
       rewrite series_stretch_stretch.
       rewrite series_stretch_stretch.
       apply stretch_morph; [ reflexivity | idtac ].
       unfold series_stretch; simpl.
       constructor; simpl; intros i.
       destruct (zerop (i mod Pos.to_nat dd)) as [H₁| H₁].
        apply Nat.mod_divides in H₁; auto.
        destruct H₁ as (c, Hc).
        rewrite Nat.mul_comm in Hc; rewrite Hc.
        rewrite Nat.div_mul; auto.
        destruct (lt_dec c (Z.to_nat nd₁)) as [H₁| H₁].
         rewrite rng_add_0_l.
         destruct (zerop c) as [H₂| H₂].
          move H₂ at top; subst c; simpl.
          rewrite Nat.mod_0_l; auto; simpl.
          rewrite Nat.div_0_l; auto.
          unfold root_series_from_cγ_list; simpl.
          rewrite Nat.mod_0_l; auto; simpl.
          rewrite Hc₁; reflexivity.

          rewrite <- Hc.
          destruct (zerop (i mod Pos.to_nat dd₁)) as [H₃| H₃].
           apply Nat.mod_divides in H₃; auto.
           destruct H₃ as (d, Hd).
           rewrite Nat.mul_comm in Hd; rewrite Hd.
           rewrite Nat.div_mul; auto.
           unfold root_series_from_cγ_list.
           destruct (zerop (d mod Pos.to_nat (Qden (γ ns)))) as [H₃| H₃].
            remember O as z; simpl; subst z.
            apply Nat.mod_divides in H₃; auto.
            destruct H₃ as (e, He).
            destruct (eq_nat_dec 0 d) as [H₃| H₃].
             move H₃ at top; subst d.
             simpl in Hd.
             move Hd at top; subst i.
             symmetry in Hc.
             apply Nat.eq_mul_0_l in Hc; auto.
             move Hc at top; subst c.
             exfalso; revert H₂; apply Nat.lt_irrefl.

             destruct (lt_dec 0 d) as [H₄| ]; [ idtac | reflexivity ].
             rewrite find_coeff_le; reflexivity.

            reflexivity.

           reflexivity.

         apply Nat.nlt_ge in H₁.
         rewrite <- Hc.
         destruct (zerop c) as [H₂| H₂].
          move H₂ at top; subst c.
          apply Nat.le_0_r in H₁.
          rewrite Heqnd₁ in H₁.
          rewrite Z2Nat.inj_mul in H₁.
           simpl in H₁.
           apply Nat.mul_eq_0_l in H₁; auto.
           rewrite <- Z2Nat.inj_0 in H₁.
           apply Z2Nat.inj in H₁.
            rewrite H₁ in Hαj₁.
            exfalso; revert Hαj₁; apply Z.lt_irrefl.

            apply Z.lt_le_incl; assumption.

            reflexivity.

           apply Z.lt_le_incl; assumption.

           apply Pos2Z.is_nonneg.

          destruct (zerop (i mod Pos.to_nat dd₁)) as [H₃| H₃].
           apply Nat.mod_divides in H₃; auto.
           destruct H₃ as (d, H₃).
           rewrite Nat.mul_comm in H₃; rewrite H₃.
           rewrite Nat.div_mul; auto.
           rewrite rng_add_0_r.
           unfold root_series_from_cγ_list.
           remember (c - Z.to_nat nd₁)%nat as e.
           destruct (zerop (e mod Pos.to_nat (Qden (γ ns₁)))) as [H₄| H₄].
            destruct (zerop (d mod Pos.to_nat (Qden (γ ns)))) as [H₅| H₅].
             remember O as z; simpl; subst z.
             rewrite Hini, Hfin, Hini₁, Hfin₁.
             remember O as z; simpl; subst z.
             rewrite find_coeff_le; [ idtac | reflexivity ].
             rewrite find_coeff_le; [ idtac | reflexivity ].
             destruct (eq_nat_dec 0 e) as [H₆| H₆].
              move H₆ at top; subst e.
              destruct (eq_nat_dec 0 d) as [H₆| H₆].
               move H₆ at top; subst d.
               simpl in H₃.
               move H₃ at top; subst i.
               symmetry in Hc.
               apply Nat.mul_eq_0_l in Hc; auto.
               move Hc at top; subst c.
               exfalso; revert H₂; apply Nat.lt_irrefl.

               clear H₄.
               assert (c = Z.to_nat nd₁) as Hcc by fast_omega H₁ Heqe.
               clear H₁ Heqe.
               move Hcc at top; subst c.
               clear H₂.
               subst i.
               subst dd₁ nd₁ dd.
bbb.

intros pol ns n Hns.
revert pol ns Hns.
induction n; intros.
 unfold root_head, γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 unfold root_tail; simpl.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
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
   unfold Qeq in Hαk₁; simpl in Hαk₁.
   rewrite Z.mul_1_r in Hαk₁.
   unfold Qlt in Hαj₁; simpl in Hαj₁.
   rewrite Z.mul_1_r in Hαj₁.
   unfold root_from_cγ_list; simpl.
   rewrite Hini, Hfin, Hini₁, Hfin₁; simpl.
   rewrite Hαk₁.
   rewrite Z.mul_0_l, Z.add_0_r.
   rewrite Z.mul_1_r, Pos.mul_1_r.
   unfold ps_mul; simpl.
   unfold cm; simpl.
   rewrite Hini, Hfin; simpl.
   unfold ps_add; simpl.
   unfold cm; simpl.
   rewrite Hini, Hfin.
   simpl.
   remember (Qden αj * Qden αk * Qden (/ (Qnat k - Qnat j)))%positive as dd.
   remember (Qnum αj * ' Qden αk + - Qnum αk * ' Qden αj)%Z as nd.
   remember (nd * Qnum (/ (Qnat k - Qnat j)))%Z as ndn.
   unfold ps_ordnum_add; simpl.
   rewrite Hini, Hfin; simpl.
   rewrite <- Heqdd.
   rewrite <- Heqnd.
   rewrite <- Heqndn.
   rewrite Z.min_l.
    unfold ps_terms_add; simpl.
    rewrite Hini, Hfin; simpl.
    rewrite <- Heqdd.
    rewrite <- Heqnd.
    rewrite <- Heqndn.
    rewrite Z.min_l.
     rewrite Z.min_r.
      rewrite Z.sub_diag.
      simpl.
      unfold adjust_series.
      rewrite series_shift_0.
      remember (dd * (Qden αj₁ * Qden αk₁))%positive as dddd.
      rewrite ps_adjust_eq with (n := O) (k := dddd).
      unfold adjust_ps; simpl.
      rewrite Z.sub_0_r.
      rewrite series_shift_0.
      apply mkps_morphism; try reflexivity.
      subst dddd.
      rewrite Z.mul_add_distr_r.
      rewrite Z.mul_shuffle0.
      rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
      rewrite Z.add_simpl_l.
      rewrite Z2Nat.inj_mul.
       simpl.
       rewrite <- stretch_shift_series_distr.
       rewrite fold_series_const.
       rewrite fold_series_const.
       rewrite stretch_series_const.
       rewrite stretch_series_const.
       rewrite series_mul_1_l.
       rewrite Z2Nat.inj_mul.
        simpl.
        rewrite <- stretch_shift_series_distr.
        rewrite <- series_stretch_stretch.
        unfold series_add; simpl.
        unfold series_stretch; simpl.
        constructor; intros i; simpl.
(**)
        Focus 1.
        remember (dd * (Qden αj₁ * Qden αk₁))%positive as ddd.
        destruct (zerop (i mod Pos.to_nat ddd)) as [H₁| H₁].
         Focus 1.
         apply Nat.mod_divides in H₁; auto.
         destruct H₁ as (c, Hc).
         rewrite Nat.mul_comm in Hc.
         rewrite Hc.
         rewrite Nat.div_mul; auto.
         rewrite <- Hc.
         destruct (zerop i) as [H₁| H₁].
          Focus 1.
          move H₁ at top; subst i.
          rewrite Nat.mod_0_l; auto; simpl.
          rewrite Nat.div_0_l; auto; simpl.
          symmetry in Hc.
          apply Nat.eq_mul_0_l in Hc; auto.
          subst c; simpl.
          destruct (lt_dec 0 (Z.to_nat (Qnum αj₁ * ' Qden αk₁))) as [H₁| H₁].
           rewrite rng_add_0_r.
           unfold root_series_from_cγ_list; simpl.
           rewrite Nat.mod_0_l; auto; simpl.
bbb.
        remember (dd * (Qden αj₁ * Qden αk₁))%positive as ddd.
        destruct (zerop (i mod Pos.to_nat ddd)) as [H₁| H₁].
         apply Nat.mod_divides in H₁; auto.
         destruct H₁ as (c, Hc).
         rewrite Nat.mul_comm in Hc.
         rewrite Hc.
         rewrite Nat.div_mul; auto.
         rewrite <- Hc.
         destruct (zerop i) as [H₁| H₁].
          move H₁ at top; subst i.
          rewrite Nat.mod_0_l; auto; simpl.
          rewrite Nat.div_0_l; auto; simpl.
          symmetry in Hc.
          apply Nat.eq_mul_0_l in Hc; auto.
          subst c; simpl.
          destruct (lt_dec 0 (Z.to_nat (Qnum αj₁ * ' Qden αk₁))) as [H₁| H₁].
           rewrite rng_add_0_r.
           unfold root_series_from_cγ_list; simpl.
           rewrite Nat.mod_0_l; auto; simpl.
           rewrite Hc₁; reflexivity.

           exfalso; apply H₁.
           rewrite <- Z2Nat.inj_0.
           apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
            apply Z.mul_nonneg_nonneg.
             apply Z.lt_le_incl; assumption.

             apply Pos2Z.is_nonneg.

            apply Z.mul_pos_pos; [ assumption | idtac ].
            apply Pos2Z.is_pos.

          rewrite rng_add_0_l.
          destruct (zerop (i mod Pos.to_nat (dd * dd))) as [H₂| H₂].
           apply Nat.mod_divides in H₂; auto; simpl.
           destruct H₂ as (d, Hd).
           rewrite Nat.mul_comm in Hd.
           rewrite Hd.
           rewrite Nat.div_mul; auto; simpl.
           destruct (lt_dec d (Z.to_nat (Qnum αj₁ * ' Qden αk₁))) as [H₂| H₂].
            subst ddd.
            unfold root_series_from_cγ_list.
            destruct (zerop (c mod Pos.to_nat (Qden (γ ns)))) as [H₃| H₃].
             remember O as z; simpl; subst z.
             rewrite Hini, Hfin, <- Hc₁, <- Hpol₁, <- Hns₁.
             remember O as z; simpl; subst z.
             rewrite <- Heqdd.
             destruct (eq_nat_dec 0 c) as [H₄| H₄].
              rewrite <- H₄ in Hc; simpl in Hc.
              rewrite Hc in H₁.
              exfalso; revert H₁; apply Nat.lt_irrefl.

              destruct (lt_dec 0 c) as [H₅| H₅]; [ idtac | reflexivity ].
              rewrite find_coeff_le; reflexivity.

             reflexivity.

            apply Nat.nlt_ge in H₂.
            remember (d - Z.to_nat (Qnum αj₁ * ' Qden αk₁))%nat as m eqn:Hm .
            unfold root_series_from_cγ_list.
            destruct (zerop (c mod Pos.to_nat (Qden (γ ns)))) as [H₃| H₃].
             apply Nat.mod_divides in H₃; auto.
             destruct H₃ as (e, He).
             destruct (zerop (m mod Pos.to_nat (Qden (γ ns₁)))) as [H₃| H₃].
              apply Nat.mod_divides in H₃; auto.
              destruct H₃ as (p, Hp).
              remember O as z; simpl; subst z.
              destruct (eq_nat_dec 0 c) as [H₃| H₃].
               rewrite <- H₃ in Hc.
               simpl in Hc.
               rewrite Hc in H₁.
               exfalso; revert H₁; apply Nat.lt_irrefl.

               destruct (lt_dec 0 c) as [H₄| H₄].
                rewrite find_coeff_le; [ idtac | reflexivity ].
                destruct (eq_nat_dec 0 m) as [H₅| H₅].
                 move H₅ at top; subst m.
bbb.

(* not required if previous lemma works *)
Lemma ttt : ∀ pol ns n,
  ns ∈ newton_segments pol
  → (root_tail n pol ns =
     ps_monom 1%K (nth_γ n pol ns) *
       (ps_monom (nth_c n pol ns) 0 + root_tail (S n) pol ns))%ps.
Proof.
intros pol ns n Hns.
revert pol ns Hns.
induction n; intros.
 unfold root_tail; simpl.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
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
   unfold Qeq in Hαk₁; simpl in Hαk₁.
   rewrite Z.mul_1_r in Hαk₁.
   unfold Qlt in Hαj₁; simpl in Hαj₁.
   rewrite Z.mul_1_r in Hαj₁.
   unfold root_from_cγ_list; simpl.
   rewrite Hini, Hfin, Hini₁, Hfin₁; simpl.
   rewrite Hαk₁.
   rewrite Z.mul_0_l, Z.add_0_r.
   rewrite Z.mul_1_r, Pos.mul_1_r.
   unfold ps_mul; simpl.
   unfold cm; simpl.
   unfold cm; simpl.
   rewrite Hini, Hfin; simpl.
   unfold ps_ordnum_add; simpl.
   rewrite Z.mul_1_r.
   remember (Qden αj * Qden αk * Qden (/ (Qnat k - Qnat j)))%positive as dd.
   remember (Qnum αj * ' Qden αk + - Qnum αk * ' Qden αj)%Z as nd.
   remember (nd * Qnum (/ (Qnat k - Qnat j)))%Z as ndn.
   rewrite ps_adjust_eq with (n := O) (k := (Qden αj₁ * Qden αk₁)%positive).
   unfold adjust_ps; simpl.
   rewrite series_shift_0, Z.sub_0_r.
   rewrite Z.min_l.
    rewrite Z.mul_0_l, Z.add_0_r.
    apply mkps_morphism; try reflexivity.
    rewrite stretch_series_1.
    rewrite series_mul_1_l.
    unfold ps_terms_add; simpl.
    rewrite Z.mul_1_r.
    rewrite Z.min_l.
     rewrite Z.min_r.
      simpl.
      rewrite Z.sub_0_r.
      unfold adjust_series; simpl.
      rewrite series_shift_0.
      rewrite series_stretch_1.
      unfold series_add; simpl.
      remember (Qnum αj₁ * ' Qden αk₁)%Z as nd₁.
      remember (Qden αj₁ * Qden αk₁)%positive as dn₁.
      unfold series_stretch; simpl.
      constructor; intros i; simpl.
      destruct (zerop (i mod Pos.to_nat dn₁)) as [H₁| H₁].
       apply Nat.mod_divides in H₁; auto.
       destruct H₁ as (c, Hc).
       rewrite Nat.mul_comm in Hc; rewrite Hc.
       rewrite Nat.div_mul; auto.
       rewrite <- Hc.
       destruct (zerop (i mod Pos.to_nat dd)) as [H| H].
        apply Nat.mod_divides in H; auto.
        destruct H as (d, Hd).
        rewrite Nat.mul_comm in Hd; rewrite Hd.
        rewrite Nat.div_mul; auto.
        destruct (zerop (d mod Pos.to_nat dn₁)) as [H| H].
         apply Nat.mod_divides in H; auto.
         destruct H as (e, He).
         rewrite Nat.mul_comm in He; rewrite He.
         rewrite Nat.div_mul; auto.
         destruct (zerop e) as [Hez| Henz].
          subst e; simpl.
          simpl in He; subst d.
          simpl in Hd; subst i.
          apply Nat.mul_eq_0_l in Hd; auto.
          subst c.
          unfold root_series_from_cγ_list at 1; simpl.
          rewrite Hini, Hfin; simpl.
          rewrite <- Heqdd.
          rewrite Nat.mod_0_l; auto; simpl.
          destruct (lt_dec 0 (Z.to_nat nd₁)) as [H| H].
           rewrite Hc₁, rng_add_0_r; reflexivity.

           destruct (Z_zerop nd₁) as [Hz| Hnz].
            symmetry in Heqnd₁.
            rewrite Hz in Heqnd₁.
            apply Z.eq_mul_0 in Heqnd₁.
            clear H.
            destruct Heqnd₁ as [H| H].
             unfold Qlt in Hαj₁; simpl in Hαj₁.
             rewrite H in Hαj₁.
             exfalso; revert Hαj₁; apply Z.lt_irrefl.

             exfalso; revert H; apply Pos2Z_ne_0.

            rewrite Heqnd₁ in H.
            exfalso; apply H.
            rewrite <- Z2Nat.inj_0.
            apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
             apply Z.mul_nonneg_nonneg.
              apply Z.lt_le_incl; assumption.

              apply Pos2Z.is_nonneg.

             apply Z.mul_pos_pos; [ assumption | idtac ].
             apply Pos2Z.is_pos.

          rewrite rng_add_0_l.
          rewrite <- He.
          destruct (lt_dec d (Z.to_nat nd₁)) as [H| H].
           rewrite He, Heqnd₁, Heqdn₁ in H.
           unfold root_series_from_cγ_list.
           destruct (zerop (c mod Pos.to_nat (Qden (γ ns)))) as [H₁| H₁];
            [ idtac | reflexivity ].
           remember 0%nat as z.
           simpl.
           subst z.
           destruct (eq_nat_dec 0 c) as [Hcz| Hcnz].
            subst c.
            simpl in Hc.
            subst i.
            apply Nat.eq_mul_0 in Hc.
            destruct Hc as [Hc| Hc].
             subst d.
             apply Nat.eq_mul_0 in Hc.
             destruct Hc as [Hc| Hc].
              subst e; exfalso; revert Henz; apply Nat.lt_irrefl.

              exfalso; revert Hc; apply Pos2Nat_ne_0.

             exfalso; revert Hc; apply Pos2Nat_ne_0.

            destruct (lt_dec 0 c) as [Hcp| ]; [ idtac | reflexivity ].
            rewrite Hini, Hfin; simpl.
            rewrite <- Hc₁, <- Hpol₁, <- Hns₁, <- Heqdd.
            clear.
            remember c as d.
            rewrite Heqd in |- * at 2.
            assert (d ≤ c)%nat as Hd by (subst c; reflexivity).
            clear Heqd.
            revert c pol₁ ns₁ Hd.
            induction d; intros; [ reflexivity | idtac ].
            remember 0%nat as x; simpl; subst x.
            destruct (eq_nat_dec 0 c) as [Hc| Hc].
             subst c.
             exfalso; revert Hd; apply Nat.nle_succ_0.

             destruct (lt_dec 0 c) as [Hcp| Hcnp]; [ idtac | reflexivity ].
             apply IHd, le_Sn_le; assumption.

           apply Nat.nlt_ge in H.
           subst nd₁ dn₁ dd.
           subst i; rewrite He in Hd.
           rewrite Nat.mul_shuffle0 in Hd.
           apply Nat.mul_cancel_r in Hd; auto.
           rewrite <- Z2Nat.inj_pos in Hd.
           rewrite Pos2Z.inj_mul in Hd.
           rewrite Qden_inv in Hd.
            rewrite Z2Nat.inj_mul in Hd.
             simpl in Hd.
             do 2 rewrite Z.mul_1_r in Hd.
             rewrite Z.add_opp_r in Hd.
             rewrite Z2Nat.inj_sub in Hd.
              do 2 rewrite Nat2Z.id in Hd.
              remember (d - Z.to_nat (Qnum αj₁ * ' Qden αk₁))%nat as m eqn:Hm .
Focus 1.
bbb.
              unfold root_term_when_r_1.
              destruct (zerop (c mod Pos.to_nat (Qden (γ ns)))) as [H₁| H₁].
               apply Nat.mod_divides in H₁.
                destruct H₁ as (p, Hp).
                destruct (zerop (m mod Pos.to_nat (Qden (γ ns₁))))
                 as [H₂| H₂].
                 apply Nat.mod_divides in H₂; auto.
                 destruct H₂ as (q, Hq).
                 remember 0%nat as z; simpl; subst z.
                 remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
                 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₂) as pol₂
                  eqn:Hpol₂ .
                 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂
                  eqn:Hns₂ .
                 rewrite <- Hc₁, <- Hpol₁, <- Hns₁, Hini, Hfin, Hini₁, Hfin₁.
                 remember 0%nat as z; simpl; subst z.
                 destruct (eq_nat_dec 0 c) as [H₁| H₁].
                  move H₁ at top; subst c.
                  symmetry in Hd.
                  apply Nat.eq_mul_0_l in Hd; auto.
                   exfalso; subst e; revert Henz; apply Nat.lt_irrefl.

                   intros HH.
                   apply Nat.eq_mul_0_l in HH; [ idtac | fast_omega Hjk ].
                   revert HH; apply Pos2Nat_ne_0.

                  Focus 1.
                  destruct (lt_dec 0 c) as [H₂| H₂].
                   destruct (eq_nat_dec 0 m) as [H₃| H₃].
                    move H₃ at top; subst m.
bbb.

             Focus 2.
             apply Nat2Z.is_nonneg.

             Focus 2.
             apply Pos2Z.is_nonneg.

            Focus 2.
            simpl.
            do 2 rewrite Z.mul_1_r.
            rewrite Z.add_opp_r.
            rewrite <- Nat2Z.inj_sub; [ apply Nat2Z.is_nonneg | idtac ].
            apply Nat.lt_le_incl.
            eapply j_lt_k; [ eassumption | idtac | idtac ].
             rewrite Hini; simpl.
             rewrite nat_num_Qnat; reflexivity.

             rewrite Hfin; simpl.
             rewrite nat_num_Qnat; reflexivity.

            Focus 2.
            simpl.
            do 2 rewrite Z.mul_1_r.
            rewrite Z.add_opp_r.
            rewrite <- Nat2Z.inj_sub.
             rewrite <- Nat2Z.inj_0.
             apply Nat2Z.inj_lt.
             apply Nat.le_lt_add_lt with (n := j) (m := j);
              [ reflexivity | idtac ].
             simpl.
             rewrite Nat.sub_add.
              eapply j_lt_k; [ eassumption | idtac | idtac ].
               rewrite Hini; simpl.
               rewrite nat_num_Qnat; reflexivity.

               rewrite Hfin; simpl.
               rewrite nat_num_Qnat; reflexivity.

              apply Nat.lt_le_incl.
              eapply j_lt_k; [ eassumption | idtac | idtac ].
               rewrite Hini; simpl.
               rewrite nat_num_Qnat; reflexivity.

               rewrite Hfin; simpl.
               rewrite nat_num_Qnat; reflexivity.

             apply Nat.lt_le_incl.
             eapply j_lt_k; [ eassumption | idtac | idtac ].
              rewrite Hini; simpl.
              rewrite nat_num_Qnat; reflexivity.

              rewrite Hfin; simpl.
              rewrite nat_num_Qnat; reflexivity.

           Focus 2.
           rewrite rng_add_0_l.
           destruct (lt_dec d (Z.to_nat nd₁)) as [Hdn| Hdn].
bbb.
*)

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
Lemma xxx : ∀ pol ns c₁ pol₁ ns₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ns₁ ∈ newton_segments pol₁.
Proof.
intros pol ns c₁ pol₁ ns₁ Hns Hc₁ Hpol₁ Hns₁.
remember Hns as H; clear HeqH.
remember (root_multiplicity acf c₁ (Φq pol ns)) as r eqn:Hr .
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
unfold next_pol in Hpol₁.
unfold ps_poly_nth in Hnneg, Hz, Hpos.
unfold newton_segments in Hns₁; simpl in Hns₁.
unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
remember (al pol₁) as la₁ eqn:Hla₁ .
rewrite Hpol₁ in Hla₁; simpl in Hla₁.
unfold ps_lap_nth in Hnneg, Hpos, Hz.
symmetry in Hla₁, Hr.
destruct la₁ as [| a₀].
 simpl in Hz.
 rewrite match_id in Hz.
 rewrite order_0 in Hz; inversion Hz.

 simpl in Hz, Hpos.
 unfold points_of_ps_lap in Hns₁.
 unfold points_of_ps_lap_gen in Hns₁.
 simpl in Hns₁.
 destruct r.
  exfalso; revert Hr.
  apply root_multiplicity_ne_0; assumption.

  destruct la₁ as [| a₁].
   simpl in Hz.
   rewrite match_id in Hz.
   rewrite order_0 in Hz; inversion Hz.

   simpl in Hns₁.
   remember (order a₀) as v₀ eqn:Hv₀ .
   symmetry in Hv₀.
   destruct v₀ as [v₀| ].
    remember (order a₁) as v₁ eqn:Hv₁ .
    symmetry in Hv₁.
    destruct v₁ as [v₁| ].
     unfold newton_segments.
     rewrite Hpol₁.
     unfold points_of_ps_polynom; simpl.
     rewrite Hla₁.
     unfold points_of_ps_lap.
     unfold points_of_ps_lap_gen; simpl.
     rewrite Hv₀, Hv₁, Hns₁; left; reflexivity.

     destruct r.
      simpl in Hz.
      rewrite Hv₁ in Hz; inversion Hz.
bbb.
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
