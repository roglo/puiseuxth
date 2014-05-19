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

Lemma yyy : ∀ pt₁ pt₂ pts ms,
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
 destruct c; subst ms; [ simpl | reflexivity | simpl ].
  apply Q_div_lt_mono with (c := fst pt₂ - fst pt₁) in Hpt₁.
   unfold Qdiv at 2 in Hpt₁.
   rewrite Qmult_0_l in Hpt₁.
   apply Q_div_le_mono with (c := fst pte - fst pt₂) in Hsnde.
    unfold Qdiv at 1 in Hsnde.
    rewrite Qmult_0_l in Hsnde.
    apply Qlt_not_le in Hpt₁.
    apply Qeq_alt in Hc.
    eapply slope_expr_eq in Hc; try eassumption.
    unfold slope_expr in Hc.
    rewrite Hc in Hpt₁; contradiction.

    apply Qlt_minus.
    apply Sorted_inv_1 in Hsort.
    eapply Sorted_hd; eassumption.

   apply Qlt_minus.
   apply Sorted_inv in Hsort.
   destruct Hsort as (_, Hrel).
   apply HdRel_inv in Hrel.
   assumption.

  apply Q_div_lt_mono with (c := fst pt₂ - fst pt₁) in Hpt₁.
   unfold Qdiv at 2 in Hpt₁.
   rewrite Qmult_0_l in Hpt₁.
   apply Q_div_le_mono with (c := fst pte - fst pt₂) in Hsnde.
    unfold Qdiv at 1 in Hsnde.
    rewrite Qmult_0_l in Hsnde.
    apply Qgt_alt in Hc.
    remember Hc as Hd; clear HeqHd.
    apply slope_lt_1312_2313 in Hc.
     eapply Qlt_trans in Hd; [ idtac | eassumption ].
     eapply Qlt_trans in Hpt₁; [ idtac | eassumption ].
     apply Qlt_not_le in Hpt₁.
     contradiction.
bbb.

Lemma zzz : ∀ pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
  → r = root_multiplicity acf c₁ (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → r = 1%nat
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → (order (ps_poly_nth 0 pol₁) ≠ ∞)%Qbar
  → j₁ = 0%nat ∧ k₁ = 1%nat ∧ αj₁ > 0 ∧ αk₁ == 0.
Proof.
intros pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁.
intros Hns Hc₁ Hr Hpol₁ Hr₁1 Hns₁ Hini₁ Hfin₁ Hps₀.
remember Hns as H; clear HeqH.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
move Hr₁1 at top; subst r.
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
 remember (rem_pts ms) as rms.
 symmetry in Heqrms.
 destruct rms as [| pt₂].
  simpl in Hns.
  unfold newton_segment_of_pair in Hns; simpl in Hns.
  subst ns; simpl in Hini, Hfin.
bbb.
  apply yyy in Heqms.
   rewrite Heqms in Hfin.
bbb.

  subst ffo.
  induction la as [| a₂].
   simpl in Heqms.
   rewrite Heqms in Hfin; simpl in Hfin.
   injection Hini; clear Hini; intros; subst.
   injection Hfin; clear Hfin; intros; subst.
   apply Z2Nat.inj_iff in H0; [ idtac | reflexivity | apply Nat2Z.is_nonneg ].
   apply Z2Nat.inj_iff in H1; [ idtac | idtac | apply Nat2Z.is_nonneg ].
    rewrite Nat2Z.id in H0, H1.
    simpl in H0, H1.
    rewrite Pos2Nat.inj_1 in H1.
    subst j k.
    split; [ reflexivity | idtac ].
    split; [ reflexivity | idtac ].
    split; assumption.

    apply Z.le_0_1.

   simpl in Heqms.
   rewrite Heqf in Heqms; simpl in Heqms.
   rewrite <- Heqf in Heqms.
   remember (order a₂) as v₂.
   symmetry in Heqv₂.
   destruct v₂ as [v₂| ].
    simpl in Heqms.
    remember (filter_finite_ord R (List.map f (power_list 3 la))) as ffo.
    remember (minimise_slope (Qnat 0, v₀) (Qnat 2, v₂) ffo) as ms₁.
    remember (slope_expr (Qnat 0, v₀) (Qnat 1, v₁) ?= slope ms₁) as c.
    symmetry in Heqc.
    destruct c.
     subst ffo.
bbb.

intros pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁.
intros Hns Hc₁ Hr Hpol₁ Hr₁1 Hns₁ Hini₁ Hfin₁ Hps₀.
remember Hns as H; clear HeqH.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
move Hr₁1 at top; subst r.
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
 remember (List.map f (power_list 2 la)) as l.
 remember (filter_finite_ord R l) as ffo.
 destruct la as [| a₂].
  simpl in Heql; subst l.
  simpl in Heqffo; subst ffo.
  simpl in Hns.
  unfold newton_segment_of_pair in Hns; simpl in Hns.
  subst ns; simpl in Hini, Hfin.
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
   split; assumption.

   apply Z.le_0_1.

  simpl in Heql.
  pose proof (Hnneg 2%nat) as H₂nneg.
  simpl in H₂nneg.
  simpl in Hns.
  remember (minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo) as ms₁.
  remember (rem_pts ms₁) as rp₁.
  symmetry in Heqrp₁.
  destruct rp₁ as [| pt₂].
   simpl in Hns.
   unfold newton_segment_of_pair in Hns; simpl in Hns.
   subst ns; simpl in Hini, Hfin.
   remember (f (2, a₂)) as x.
   rewrite Heqf in Heqx.
   unfold pair_rec in Heqx; simpl in Heqx.
   subst x.
   subst l; simpl in Heqffo.
   remember (order a₂) as v₂.
   symmetry in Heqv₂.
   remember (filter_finite_ord R (List.map f (power_list 3 la))) as l.
   destruct v₂ as [v₂| ].
    apply Qbar.qfin_le_mono in H₂nneg.
    subst ffo; simpl in Heqms₁.
    remember (minimise_slope (Qnat 0, v₀) (Qnat 2, v₂) l) as ms₂.
    remember (slope_expr (Qnat 0, v₀) (Qnat 1, v₁) ?= slope ms₂) as c.
    symmetry in Heqc.
    destruct c.
     subst ms₁; simpl in Hfin, Heqrp₁.
     apply Qeq_alt in Heqc.
bbb.
     symmetry in Heqms₂, Hfin.
     eapply minimised_slope in Heqms₂; [ idtac | eassumption ].
     rewrite Heqms₂ in Heqc.
     unfold slope_expr in Heqc; simpl in Heqc.
     apply Qbar.qfin_inj in Hz.
     rewrite Hz in Heqc.
     unfold Qnat in Heqc.
     simpl in Heqc.
bbb.
