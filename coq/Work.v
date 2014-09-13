(* Work.v *)

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
Require Import RootHeadTail.
Require Import RootWhenR1.
Require Import RootAnyR.

Set Implicit Arguments.

Axiom exists_or_not_forall : ∀ P : nat → Prop, { ∃ n, P n } + { ∀ n, ¬P n }.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition multiplicity_decreases pol ns n :=
  let c := ac_root (Φq pol ns) in
  let r := root_multiplicity acf c (Φq pol ns) in
  let poln := nth_pol n pol ns in
  let nsn := nth_ns n pol ns in
  let cn := nth_c n pol ns in
  let rn := root_multiplicity acf cn (Φq poln nsn) in
  (rn < r)%nat.

Theorem β_lower_bound_r_const : ∀ pol ns pol₁ ns₁ m r η,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → (0 < r)%nat
  → (1 ≠ 0)%K
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, r ≤ nth_r i pol ns)
  → η = 1 # (2 * m * q_of_m m (γ ns))
  → ∀ n nsn,
    zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → (∀ i, i ≤ S n → nth_r i pol ns = r)
    → nsn = nth_ns n pol₁ ns₁
    → η < β nsn.
Proof.
intros pol ns pol₁ ns₁ m r η.
intros Hns Hm Hr H₀ Hpol₁ Hns₁ Hrle Hη n nsn Hnz Hri Hnsn.
remember Hns as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
eapply r_n_nth_ns in H; try eassumption; eauto .
destruct H as (αjn, (αkn, H)).
destruct H as (Hinin, (Hfinn, (Hαjn, Hαkn))).
unfold β.
rewrite Hinin; simpl.
unfold Qnat; simpl.
rewrite rng_mul_0_l, rng_add_0_r.
remember Hpol₁ as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; try eassumption; eauto .
rename H into HK₁.
pose proof (Hnz O (Nat.le_0_l n)) as Hnz₀.
simpl in Hnz₀.
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
apply Hri in H; simpl in H.
rename H into Hr₀.
assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
apply Hri in H; simpl in H.
rewrite <- Hpol₁, <- Hns₁ in H.
rename H into Hr₁.
remember Hns₁ as H; clear HeqH.
eapply r_n_next_ns in H; try eassumption; auto.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember Hns₁ as H; clear HeqH.
eapply hd_newton_segments in H; try eassumption.
rename H into Hns₁i.
remember HK₁ as H; clear HeqH.
eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁) in H; eauto .
 rename H into HKn.
 remember (nth_pol n pol₁ ns₁) as poln eqn:Hpoln .
 remember Hns₁i as H; clear HeqH.
 eapply nth_in_newton_segments_any_r with (n := n) in H; eauto .
 rename H into Hnsni.
 remember HKn as H; clear HeqH.
 eapply pol_ord_of_ini_pt in H; try eassumption; eauto .
 rewrite Hη, H.
 rewrite <- Pos.mul_assoc.
 remember (m * q_of_m m (γ ns))%positive as m₁ eqn:Hm₁ .
 unfold mh_of_m.
 erewrite <- qden_αj_is_ps_polord; try eassumption; eauto .
 remember (2 * m₁)%positive as m₂.
 unfold Qlt; simpl; subst m₂.
 clear H.
 assert (0 < Qnum αjn * ' m₁ / ' Qden αjn)%Z as H.
  apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
   apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.lt_le_incl; assumption.

   eapply num_m_den_is_pos with (ns := nsn); try eassumption.

  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  replace (' m₁)%Z with (1 * ' m₁)%Z at 1 by reflexivity.
  apply Z.mul_lt_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
  fast_omega H.

 eapply q_eq_1_any_r with (ns := ns₁); try eassumption; eauto .

 intros i.
 rewrite Hns₁, Hpol₁.
 erewrite <- nth_pol_succ with (n := O); try eassumption; try reflexivity.
 erewrite <- nth_ns_succ with (n := O); try eassumption; try reflexivity.
 rewrite <- nth_r_add.
 apply Hrle.
Qed.

Theorem r₁_le_r₀ : ∀ pol ns pol₁,
  ns ∈ newton_segments pol
  → pol₁ = nth_pol 1 pol ns
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → nth_r 1 pol ns ≤ nth_r 0 pol ns.
Proof.
intros pol ns pol₁ Hns Hpol₁ Hnz₀; simpl.
simpl in Hpol₁; rewrite <- Hpol₁.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ in H; try eassumption; eauto.
do 2 rewrite Nat.add_0_r in H.
destruct H as (Hj₁, (Hr₁, (Hr, _))).
transitivity k₁; auto.
Qed.

Theorem r_le_eq_incl : ∀ pol ns r n,
  ns ∈ newton_segments pol
  → nth_r 0 pol ns = r
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ n → r ≤ nth_r i pol ns)
  → (∀ i, i ≤ n → r = nth_r i pol ns).
Proof.
intros pol ns r n Hns Hr₀ Hnz Hri i Hin.
remember Hin as H; clear HeqH.
apply Hri in H.
apply Nat.le_antisymm; auto.
clear H.
revert pol ns r n Hns Hr₀ Hnz Hri Hin.
induction i; intros; [ rewrite <- Hr₀; reflexivity | idtac ].
destruct n; [ exfalso; revert Hin; apply Nat.nle_succ_0 | idtac ].
remember Hin as H; clear HeqH.
apply Hri in H.
simpl in H; simpl.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
eapply IHi; try eassumption; eauto.
 eapply List_hd_in; try eassumption .
 clear H.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; try eassumption; eauto.
 destruct H as [H₁| H₁].
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hnz in H; contradiction.

  simpl in H₁.
  rewrite <- Hc, <- Hpol₁ in H₁; auto.

 apply Nat.le_antisymm.
  clear H.
  remember Hns as H; clear HeqH.
  eapply r₁_le_r₀ in H; try eassumption; eauto.
   rewrite Hr₀ in H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

   clear H.
   assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
   apply Hnz in H; auto.

  clear H.
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption .
 apply Hnz in Hin; simpl in Hin.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; auto.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption .
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; auto.
Qed.

Theorem order_root_tail_nonneg_any_r : ∀ pol ns c pol₁ ns₁ m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, i ≤ S n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ S n → nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (0 ≤ order (root_tail (m * q₀) n pol₁ ns₁))%Qbar.
Proof.
intros pol ns c pol₁ ns₁ m q₀ n r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi Hri H₀.
unfold root_tail.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁; [ rewrite order_0; constructor | idtac ].
revert m q₀ c pol ns pol₁ ns₁ Hns Hc Hm Hq₀ Hpol₁ Hns₁ Hz₁ Hpsi Hri.
induction n; intros.
 simpl.
 unfold order; simpl.
 pose proof (Hpsi 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rewrite <- Hc, <- Hpol₁ in H.
 rename H into Hnz₁; move Hnz₁ before Hns₁.
 pose proof (Hri 0%nat Nat.le_0_1) as H.
 simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 pose proof (Hri 1%nat (Nat.le_refl 1)) as H.
 simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 move Hc₁ before Hns₁.
 move c₁ before ns₁.
 rename H into Hr₁; move Hr₁ before Hc₁.
 remember Hc as H; clear HeqH.
 eapply multiplicity_is_pos in H; try eassumption .
 rename H into Hrpos; move Hrpos before Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 move H before Hnz₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as H; clear HeqH.
 eapply hd_newton_segments in H; try eassumption .
 rename H into Hns₁i; move Hns₁i before Hns₁.
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; try eassumption .
 remember (m * q₀)%positive as m₁ eqn:Hm₁.
 rename H into HK₁; move HK₁ before Hnz₁.
 move Hm₁ before Hq₀.
 rewrite Hini₁, Hfin₁; simpl.
 rewrite Hαk₁; simpl.
 rewrite Qnum_inv_Qnat_sub; auto.
 rewrite Qden_inv_Qnat_sub; auto.
 rewrite Z.add_0_r, Z.mul_1_r.
 remember (root_tail_series_from_cγ_list m₁ pol₁ ns₁) as t.
 remember (null_coeff_range_length R {| terms := t |} 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | constructor ].
 apply Qbar.qfin_le_mono.
 rewrite Nat.sub_0_r.
 rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
 rewrite Pos2Z.inj_mul; auto.
 rewrite Z.div_mul_cancel_r; auto.
 erewrite αj_m_eq_p_r with (ns₁ := ns₁); try eassumption; eauto.
 rewrite Z.mul_shuffle0.
 rewrite <- Zposnat2Znat; auto.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite Z.div_mul; auto.
 unfold Qle; simpl.
 rewrite Z.mul_1_r.
 apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
 apply Z.lt_le_incl.
 eapply p_is_pos; try eassumption .

 simpl in Hz₁; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hz₁.

  remember (m * q₀)%positive as m₁ eqn:Hm₁ .
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  pose proof (Hri 0%nat (Nat.le_0_l (S (S n)))) as H.
  simpl in H; rewrite <- Hc in H.
  rename H into Hr₀; move Hr₀ before Hc.
  assert (1 ≤ S (S n)) as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
  rename H into Hr₁; move Hr₁ before Hc₁.
  remember Hc as H; clear HeqH.
  eapply multiplicity_is_pos in H; try eassumption .
  rename H into Hrpos; move Hrpos before Hns₁.
  remember Hns₁ as H; clear HeqH.
  eapply r_n_next_ns in H; try eassumption .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  remember Hns₁ as H; clear HeqH.
  eapply hd_newton_segments in H; try eassumption .
  rename H into Hns₁i; move Hns₁i before Hns₁.
  remember Hns as H; clear HeqH.
  eapply next_pol_in_K_1_mq in H; try eassumption .
  rewrite <- Hm₁ in H.
  rename H into HK₁; move HK₁ before Hns₁i.
  eapply IHn with (ns := ns₁) (pol := pol₁); try eassumption .
   symmetry in Hr₁; symmetry.
   eapply q_eq_1_any_r with (pol := pol₁); try eassumption; auto.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hpsi in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
   assumption.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hri in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
   assumption.
Qed.

Theorem zzz : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns c pol₁ Hns Hnz₀ Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hnz₀ Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 destruct (exists_or_not_forall (multiplicity_decreases pol ns)) as [Hn| Hn].
  destruct Hn as (n, Hn).
  unfold multiplicity_decreases in Hn.
  rewrite <- Hc, Hr in Hn.
  remember (nth_pol n pol ns) as poln eqn:Hpoln .
  remember (nth_ns n pol ns) as nsn eqn:Hnsn .
  remember (nth_c n pol ns) as cn eqn:Hcn .
  remember (root_multiplicity acf cn (Φq poln nsn)) as rn eqn:Hrn .
  symmetry in Hrn.
  destruct n.
   simpl in Hpoln, Hnsn, Hcn.
   subst poln nsn cn.
   rewrite <- Hc in Hrn.
   rewrite Hrn in Hr; subst rn.
   exfalso; revert Hn; apply Nat.lt_irrefl.

   remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
   erewrite <- nth_r_n in Hrn; try eassumption ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn; [ idtac | subst; auto ].
   destruct Hn as (i, (Hin, (Hir, Hri))).
   destruct Hir as [Hir| Hir].
    subst i.
    exfalso; revert Hri; rewrite <- Hr; subst.
    apply Nat.lt_irrefl.

    destruct i.
     exfalso; revert Hri; rewrite <- Hr; subst.
     apply Nat.lt_irrefl.

     remember (nth_pol i pol ns) as poli eqn:Hpoli .
     remember (nth_ns i pol ns) as nsi eqn:Hnsi .
     remember (nth_pol (S i) pol ns) as polsi eqn:Hpolsi .
     remember (nth_ns (S i) pol ns) as nssi eqn:Hnssi .
     remember (newton_segments polsi) as nsl eqn:Hnsl .
     symmetry in Hnsl.
     destruct nsl as [| ns₂].
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       apply a₀_0_root_0 in H₁.
       exists 0%ps; assumption.

       remember Hnsl as H; clear HeqH.
       rewrite Hpolsi in H.
       simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
       apply nth_newton_segments_nil in H; auto.
        destruct H as (j, (Hjn, (Hjz, Hjnz))).
        destruct Hjz as [Hjz| Hjz].
         subst j.
         simpl in Hjnz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)).
          contradiction.

          discriminate Hjnz.

         eapply root_when_fin; try eassumption .

        eapply List_hd_in; try eassumption .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; eauto.
        simpl in H.
        rewrite <- Hc, <- Hpol₁ in H.
        destruct H; auto.

      remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (m, (Hmi, (Hle, Heq))).
       destruct Hle as [Hle| Hle].
        subst m.
        simpl in Heq.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         exists 0%ps.
         apply a₀_0_root_0; assumption.

         discriminate Heq.

        eapply root_when_fin; try eassumption .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; try eassumption; eauto.
        erewrite <- nth_c_n; try eassumption .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; try eassumption; eauto.
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; try eassumption; eauto.
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        eauto.

        erewrite nth_c_n; try eassumption; reflexivity.

        symmetry.
        apply nth_r_n; try eassumption .
        erewrite nth_c_n; try eassumption; reflexivity.

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  destruct (ac_zerop 1%K) as [H₀| H₀].
   exists 0%ps.
   unfold ps_pol_apply, apply_poly, apply_lap; simpl.
   remember (al pol₁) as la; clear Heqla.
   destruct la as [| a]; [ reflexivity | simpl ].
   rewrite rng_mul_0_r, rng_add_0_l.
   apply eq_1_0_ps_0; assumption.

   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
    exists 0%ps.
    apply a₀_0_root_0; assumption.

    remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
    remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
    remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
     remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
     symmetry in Hz.
     destruct z.
      unfold root_tail in Hofs.
      destruct N.
       exists 0%ps.
       simpl in Hz.
       destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
       discriminate Hz.

       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (i, (Hin, (Hji, Hz))).
       destruct Hji as [Hi| Hpi].
        subst i.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
        discriminate Hz.

        eapply root_when_fin; try eassumption .

      unfold multiplicity_decreases in Hn; simpl in Hn.
      rewrite <- Hc, Hr in Hn.
      rewrite root_tail_when_r_r with (n := N) in Hofs; try eassumption.
       Focus 3.
       intros j.
       pose proof (Hn j) as H.
       apply Nat.nlt_ge in H.
       erewrite nth_r_n; eauto .

       Focus 2.
       apply non_decr_imp_eq; auto.
        apply zerop_1st_n_const_coeff_false_iff.
        intros j Hj.
        destruct j; [ assumption | idtac ].
        apply le_S_n in Hj.
        apply Nat.le_0_r in Hj; subst j; simpl.
        rewrite <- Hc, <- Hpol₁; assumption.

        simpl; rewrite <- Hc; assumption.

        intros j.
        pose proof (Hn j) as H.
        apply Nat.nlt_ge in H.
        erewrite nth_r_n; eauto .

       remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
       exists s.
       apply order_inf.
       rewrite apply_nth_pol in Hofs; auto.
       rewrite order_mul in Hofs; auto.
       rewrite ps_monom_order in Hofs; auto.
       remember Σ (i = 0, N), β (nth_ns i pol₁ ns₁) as u eqn:Hu .
       assert (ofs < u) as H.
        subst u.
        assert (∀ i, i ≤ N → η < β (nth_ns i pol₁ ns₁)).
         intros i Hi.
         subst c q₀.
         assert (zerop_1st_n_const_coeff i pol₁ ns₁ = false) as Hz₁.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          apply zerop_1st_n_const_coeff_false_iff.
          intros j Hj.
          apply Hz.
          transitivity i; assumption.

          eapply β_lower_bound_r_const with (n := i) (r := S r); eauto .
           apply Nat.lt_0_succ.

           intros j.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; try eassumption; eauto .

           apply non_decr_imp_eq; try assumption.
            apply zerop_1st_n_const_coeff_false_succ; auto; simpl.
            rewrite <- Hpol₁, <- Hns₁; assumption.

            intros j.
            pose proof (Hn j) as H.
            apply Nat.nlt_ge in H.
            erewrite <- nth_r_n in H; try eassumption; eauto .

         apply summation_all_lt in H.
         eapply Qle_lt_trans; try eassumption.
         rewrite Hη, HN.
         rewrite <- Pos2Z.inj_mul.
         rewrite <- Pos2Z.inj_mul.
         remember (2 * m * q₀)%positive as mq eqn:Hmq .
         rewrite Z.mul_comm.
         rewrite Z2Nat_inj_mul_pos_r.
         unfold Qle; simpl.
         rewrite Pos.mul_1_r.
         rewrite Pos2Z.inj_mul.
         rewrite Zpos_P_of_succ_nat.
         rewrite Nat2Z.inj_mul.
         remember (Qnum ofs) as nofs eqn:Hnofs .
         symmetry in Hnofs.
         destruct nofs as [| nofs| nofs]; simpl; auto.
          rewrite positive_nat_Z.
          rewrite Z.mul_succ_l.
          rewrite positive_nat_Z.
          rewrite <- Pos2Z.inj_mul.
          rewrite <- Z.mul_1_r in |- * at 1.
          eapply Z.le_trans.
           apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.
           rewrite Z.one_succ.
           apply Zlt_le_succ.
           apply Pos2Z.is_pos.

           apply Z.le_sub_le_add_l.
           rewrite Z.sub_diag; auto.

          apply Zle_neg_pos.

        apply Qlt_not_le in H.
        exfalso; apply H.
        apply Qbar.qfin_le_mono.
        rewrite <- Hofs.
        apply Qbar.le_sub_le_add_l.
        rewrite Qbar.sub_diag.
        apply order_pol_apply_nonneg; auto.
         intros a Ha.
         remember (nth_pol N pol₁ ns₁) as polN eqn:HpolN .
         remember (nth_ns N pol₁ ns₁) as nsN eqn:HnsN .
         assert (List.In nsN (newton_segments polN)) as HnsNi.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          remember (m * q₀)%positive as m₁.
          eapply nth_in_newton_segments_any_r with (ns₁ := ns₁); eauto.
           clear H.
           remember Hns₁ as H; clear HeqH.
           eapply r_n_next_ns in H; try eassumption; eauto.
            destruct H as (αj₁, (αk₁, H)).
            destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
            eapply List_hd_in; try eassumption .
            intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns).
             symmetry.
             eapply r_le_eq_incl; try eassumption; auto.
              simpl.
              rewrite <- Hc; auto.

              intros i Hi.
              destruct i; auto; simpl.
              rewrite <- Hc, <- Hpol₁, <- Hns₁.
              apply Hz.
              apply Nat.succ_le_mono in Hi.
              apply Nat.le_0_r in Hi; subst i.
              apply Nat.le_0_l.

              intros i Hi.
              clear H.
              pose proof (Hn i) as H.
              apply Nat.nlt_ge in H.
              erewrite nth_r_n; try eassumption; eauto.

             simpl; rewrite <- Hc; assumption.

             simpl; rewrite <- Hc, <- Hpol₁; assumption.

             symmetry.
             apply nth_c_n.
              simpl; rewrite <- Hc; assumption.

              simpl; rewrite <- Hc, <- Hpol₁; assumption.

          rename H into Huofs.
          remember HnsNi as H; clear HeqH.
          eapply f₁_orders in H; try eassumption; eauto .
          erewrite <- nth_pol_succ in H; try eassumption.
           destruct H as (H, _).
           apply List_In_nth with (d := 0%ps) in Ha.
           destruct Ha as (n, Hn₁).
           rewrite Hn₁.
           apply H.

           symmetry.
           apply nth_c_n; try eassumption.

         eapply order_root_tail_nonneg_any_r; try eassumption.
          intros i HiN.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          destruct i; auto.
          destruct i; [ simpl; rewrite <- Hc, <- Hpol₁; auto | idtac ].
          remember (S i) as si in |- *; simpl.
          rewrite <- Hc, <- Hpol₁, <- Hns₁.
          subst si.
          do 2 apply le_S_n in HiN.
bbb.
          rename H into Huofs.
           intros i HiN.
           symmetry.
           eapply r_le_eq_incl; try eassumption .
            eapply List_hd_in; try eassumption .
            remember Hns as H; clear HeqH.
            eapply next_has_root_0_or_newton_segments in H; try eassumption .
            destruct H as [H| H].
             simpl in H.
             rewrite <- Hc, <- Hpol₁ in H; contradiction.

             simpl in H.
             rewrite <- Hc, <- Hpol₁ in H; assumption.

            intros j HjN.
            rewrite Nat.add_0_r.
            unfold multiplicity_decreases in Hn.
            rewrite <- Hc, Hr in Hn.
            pose proof (Hn (S j)) as H.
            erewrite <- nth_r_n in H; try eassumption .
            apply Nat.nlt_ge in H.
            simpl in H.
            rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
            transitivity (S r); auto.
            rewrite <- Hr; simpl.
            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns);
             auto.
             rewrite <- nth_r_n with (n := O) (pol := pol) (ns := ns); auto.
             eapply r₁_le_r₀; try eassumption .
             simpl; rewrite <- Hc, <- Hpol₁.
             clear H.
             pose proof (Hz O (Nat.le_0_l N)) as H.
             assumption.

             simpl; rewrite <- Hc; assumption.

             simpl; rewrite <- Hc, <- Hpol₁; assumption.

             symmetry.
             apply nth_c_n.
              simpl; rewrite <- Hc; assumption.

              simpl; rewrite <- Hc, <- Hpol₁; assumption.

          rename H into Huofs.
          remember HnsNi as H; clear HeqH.
          eapply f₁_orders in H; try eassumption .
          erewrite <- nth_pol_succ in H; try eassumption .
           destruct H as (H, _).
           apply List_In_nth with (d := 0%ps) in Ha.
           destruct Ha as (n, Hn₁).
           rewrite Hn₁.
           apply H.

           symmetry.
           apply nth_c_n; try eassumption .

         eapply order_root_tail_nonneg_any_r; try eassumption .
          intros i HiN.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          destruct i; auto.
          destruct i.
           simpl; rewrite <- Hc, <- Hpol₁; auto.

           remember (S i) as si in |- *; simpl.
           rewrite <- Hc, <- Hpol₁, <- Hns₁.
           subst si.
           do 2 apply le_S_n in HiN.
bbb.

      intros i.
      unfold multiplicity_decreases in Hn.
      rewrite <- Hc, Hr in Hn.
      pose proof (Hn i) as H.
      erewrite <- nth_r_n in H; try eassumption .
      apply Nat.nlt_ge in H.
      symmetry.
      eapply r_le_eq_incl; try eassumption .
       intros j HjN.
bbb.
Check order_root_tail_nonneg.

intros pol ns c pol₁ Hns Hnz₀ Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hnz₀ Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 destruct (exists_or_not_forall (multiplicity_decreases pol ns)) as [Hn| Hn].
  destruct Hn as (n, Hn).
  unfold multiplicity_decreases in Hn.
  rewrite <- Hc, Hr in Hn.
  remember (nth_pol n pol ns) as poln eqn:Hpoln .
  remember (nth_ns n pol ns) as nsn eqn:Hnsn .
  remember (nth_c n pol ns) as cn eqn:Hcn .
  remember (root_multiplicity acf cn (Φq poln nsn)) as rn eqn:Hrn .
  symmetry in Hrn.
  destruct n.
   simpl in Hpoln, Hnsn, Hcn.
   subst poln nsn cn.
   rewrite <- Hc in Hrn.
   rewrite Hrn in Hr; subst rn.
   exfalso; revert Hn; apply Nat.lt_irrefl.

   remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
   erewrite <- nth_r_n in Hrn; try eassumption ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn; [ idtac | subst; auto ].
   destruct Hn as (i, (Hin, (Hir, Hri))).
   destruct Hir as [Hir| Hir].
    subst i.
    exfalso; revert Hri; rewrite <- Hr; subst.
    apply Nat.lt_irrefl.

    destruct i.
     exfalso; revert Hri; rewrite <- Hr; subst.
     apply Nat.lt_irrefl.

     remember (nth_pol i pol ns) as poli eqn:Hpoli .
     remember (nth_ns i pol ns) as nsi eqn:Hnsi .
     remember (nth_pol (S i) pol ns) as polsi eqn:Hpolsi .
     remember (nth_ns (S i) pol ns) as nssi eqn:Hnssi .
     remember (newton_segments polsi) as nsl eqn:Hnsl .
     symmetry in Hnsl.
     destruct nsl as [| ns₂].
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       apply a₀_0_root_0 in H₁.
       exists 0%ps; assumption.

       remember Hnsl as H; clear HeqH.
       rewrite Hpolsi in H.
       simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
       apply nth_newton_segments_nil in H; auto.
        destruct H as (j, (Hjn, (Hjz, Hjnz))).
        destruct Hjz as [Hjz| Hjz].
         subst j.
         simpl in Hjnz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)).
          contradiction.

          discriminate Hjnz.

         eapply root_when_fin; try eassumption .

        eapply List_hd_in; try eassumption .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; try eassumption .
        simpl in H.
        rewrite <- Hc, <- Hpol₁ in H.
        destruct H; auto.

      remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (m, (Hmi, (Hle, Heq))).
       destruct Hle as [Hle| Hle].
        subst m.
        simpl in Heq.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         exists 0%ps.
         apply a₀_0_root_0; assumption.

         discriminate Heq.

        eapply root_when_fin; try eassumption .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; try eassumption .
        erewrite <- nth_c_n; try eassumption .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; try eassumption .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; try eassumption .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        try eassumption .

        erewrite nth_c_n; try eassumption .

        symmetry.
        apply nth_r_n; try eassumption .
        erewrite nth_c_n; try eassumption .

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  destruct (ac_zerop 1%K) as [H₀| H₀].
   exists 0%ps.
   unfold ps_pol_apply, apply_poly, apply_lap; simpl.
   remember (al pol₁) as la; clear Heqla.
   destruct la as [| a]; [ reflexivity | simpl ].
   rewrite rng_mul_0_r, rng_add_0_l.
   apply eq_1_0_ps_0; assumption.

   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
    exists 0%ps.
    apply a₀_0_root_0; assumption.

    remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
    remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
    remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
     rewrite root_tail_when_r_r with (n := N) in Hofs; try eassumption .
      rewrite Nat.add_0_l in Hofs.
      remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       unfold root_tail in Hofs.
       rewrite <- Nat.add_1_r in Hofs.
       rewrite zerop_1st_n_const_coeff_true_if in Hofs; auto.
       rewrite rng_mul_0_r, rng_add_0_r in Hofs.
       destruct N.
        exists 0%ps.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
        discriminate Hz.

        apply lowest_zerop_1st_n_const_coeff in Hz.
        destruct Hz as (i, (Hin, (Hji, Hz))).
        destruct Hji as [Hi| Hpi].
         subst i.
         simpl in Hz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁));
          [ contradiction | idtac ].
         discriminate Hz.

         eapply root_when_fin; try eassumption .

       remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
       exists s.
       apply order_inf.
       rewrite apply_nth_pol in Hofs; auto.
       rewrite order_mul in Hofs; auto.
       rewrite ps_monom_order in Hofs; auto.
       remember Σ (i = 0, N), β (nth_ns i pol₁ ns₁) as u eqn:Hu .
       assert (ofs < u) as H.
        subst u.
        assert (∀ i, i ≤ N → η < β (nth_ns i pol₁ ns₁)).
         intros i Hi.
         subst c q₀.
         assert (zerop_1st_n_const_coeff i pol₁ ns₁ = false) as Hz₁.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          apply zerop_1st_n_const_coeff_false_iff.
          intros j Hj.
          apply Hz.
          transitivity i; assumption.

          eapply β_lower_bound_r_const with (n := i) (r := S r); try eassumption .
           apply Nat.lt_0_succ.

           intros j Hji.
           unfold multiplicity_decreases in Hn.
           rewrite Hr in Hn.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; try eassumption .
           rename H into Hrj.
           symmetry.
           eapply r_le_eq_incl; try eassumption .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
            destruct k; try eassumption .
            apply Nat.succ_le_mono in Hki.
            apply Hz₁ in Hki; simpl.
            rewrite <- Hpol₁, <- Hns₁; auto.

            intros k Hki.
            pose proof (Hn k) as H.
            apply Nat.nlt_ge in H.
            erewrite nth_r_n; try eassumption .
bbb.
           Focus 1.
           eapply yyy; try eassumption .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz.
            destruct k.
             simpl.
             Focus 2.
             assert (k ≤ N) as H.
              transitivity i; auto.
              apply Nat.succ_le_mono; auto.

              apply Hz in H.
              simpl.
              rewrite <- Hpol₁, <- Hns₁; auto.

             Focus 2.
             intros k Hki.
bbb.

           2: apply Nat.lt_0_succ.

           Focus 2.
           apply summation_all_lt in H.
           eapply Qle_lt_trans; try eassumption .
           rewrite Hη, HN.
           rewrite <- Pos2Z.inj_mul.
           rewrite <- Pos2Z.inj_mul.
           remember (2 * m * q₀)%positive as mq eqn:Hmq .
           rewrite Z.mul_comm.
           rewrite Z2Nat_inj_mul_pos_r.
           unfold Qle; simpl.
           rewrite Pos.mul_1_r.
           rewrite Pos2Z.inj_mul.
           rewrite Zpos_P_of_succ_nat.
           rewrite Nat2Z.inj_mul.
           remember (Qnum ofs) as nofs eqn:Hnofs .
           symmetry in Hnofs.
           destruct nofs as [| nofs| nofs]; simpl; auto.
            rewrite positive_nat_Z.
            rewrite Z.mul_succ_l.
            rewrite positive_nat_Z.
            rewrite <- Pos2Z.inj_mul.
            rewrite <- Z.mul_1_r in |- * at 1.
            eapply Z.le_trans.
             apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.
             rewrite Z.one_succ.
             apply Zlt_le_succ.
             apply Pos2Z.is_pos.

             apply Z.le_sub_le_add_l.
             rewrite Z.sub_diag; auto.

            apply Zle_neg_pos.

         Focus 2.
         apply Qlt_not_le in H.
         exfalso; apply H.
         apply Qbar.qfin_le_mono.
         rewrite <- Hofs.
         apply Qbar.le_sub_le_add_l.
         rewrite Qbar.sub_diag.
         apply order_pol_apply_nonneg.
          auto.

          Focus 2.
bbb.

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.
  remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs.
  exists s.
  apply order_inf.
  unfold order; simpl.
  remember (ps_pol_apply pol₁ s) as ps₀ eqn:Hps₀ .
  remember (null_coeff_range_length R (ps_terms ps₀) 0) as ofs eqn:Hofs .
  symmetry in Hofs.
  destruct ofs as [ofs| ]; auto; exfalso.
  apply null_coeff_range_length_iff in Hofs.
  unfold null_coeff_range_length_prop in Hofs; simpl in Hofs.
  destruct Hofs as (Hofsi, Hofs).
bbb.


Theorem k_lt_pol_length : ∀ pol ns k αk,
  ns ∈ newton_segments pol
  → fin_pt ns = (Qnat k, αk)
  → (k < length (al pol))%nat.
Proof.
intros pol ns k αk Hns Hfin.
remember Hns as H; clear HeqH.
unfold newton_segments, points_of_ps_polynom in H.
unfold points_of_ps_lap, points_of_ps_lap_gen in H.
remember (qpower_list 0 (al pol)) as ppl eqn:Hppl .
remember (filter_finite_ord R ppl) as pts.
rename H into Hlch.
remember Hppl as H; clear HeqH.
remember (List.nth k (al pol) 0%ps) as kps eqn:Hkps .
eapply in_pts_in_ppl with (h := Qnat k) (hv := αk) (def := 0%ps) in H; try eassumption .
 simpl in H.
 rewrite Nat2Z.id, Nat.sub_0_r in H.
 rewrite <- Hkps in H.
 destruct H as (Hkppl, Hkord).
 remember Hkppl as H; clear HeqH.
 rewrite Hppl in H.
 apply in_power_list_lt in H.
 rewrite nat_num_Qnat in H; auto.

 eapply in_ppl_in_pts; try eassumption; [ apply Nat.le_0_l | idtac ].
 rewrite Nat.sub_0_r.
 eapply order_in_newton_segment; try eassumption .
 right; apply List.in_or_app.
 right; left; auto.
Qed.

Theorem pol_length_const : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → length (al pol₁) = length (al pol).
Proof.
intros pol ns c pol₁ Hns Hpol₁.
subst pol₁.
unfold next_pol; simpl.
unfold next_lap; simpl.
rewrite length_lap_mul; simpl.
rewrite length_lap_compose_deg_1; reflexivity.
Qed.

End theorems.
