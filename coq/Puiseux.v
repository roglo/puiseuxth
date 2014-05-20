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
 remember (rem_pts ms) as rms.
 symmetry in Heqrms.
 destruct rms as [| pt₂].
  simpl in Hns.
  unfold newton_segment_of_pair in Hns; simpl in Hns.
  subst ns; simpl in Hini, Hfin.
  eapply pouet; eassumption.

  simpl in Hns.
  unfold newton_segment_of_pair in Hns; simpl in Hns.
  subst ns; simpl in Hini, Hfin.
  eapply pouet; eassumption.
Qed.

Lemma zzz : ∀ pol ns c₁ c₂ pol₁ ns₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
(*
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
*)
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
unfold root_multiplicity; simpl.
(*
rewrite Hini₁, Hfin₁; simpl.
*)
rewrite Nat.sub_diag; simpl.
rewrite skipn_pad; simpl.

assert (ns₁ ∈ newton_segments pol₁) as Hns₁in.
 rewrite Hns₁.
 remember (newton_segments pol₁) as nsl.
 symmetry in Heqnsl.
 destruct nsl as [| ns₂].
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
