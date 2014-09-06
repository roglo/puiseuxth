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

Theorem a₀_neq_0 : ∀ pol ns αj,
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat 0, αj)
  → (ps_poly_nth 0 pol ≠ 0)%ps.
Proof.
intros pol ns αj Hns Hini.
intros H₁.
unfold ps_poly_nth, ps_lap_nth in H₁.
remember Hns as H; clear HeqH.
remember (List.nth 0 (al pol) 0%ps) as jps eqn:Hjps .
eapply ord_coeff_non_zero_in_newt_segm with (hps := jps) in H; eauto .
 apply order_inf in H₁.
 unfold order in H₁; simpl in H₁.
 unfold order_coeff in H; simpl in H.
 remember (null_coeff_range_length R (ps_terms jps) 0) as v eqn:Hv .
 destruct v as [v| ].
  discriminate H₁.

  exfalso; apply H; reflexivity.

 left; symmetry; eauto .
Qed.

Theorem nth_pol_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_pol (S n) pol ns = nth_pol n pol₁ ns₁.
Proof. intros; subst; reflexivity. Qed.

Theorem zerop_1st_n_const_coeff_more : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_poly_nth 0 (nth_pol (S n) pol ns) ≠ 0)%ps
  → zerop_1st_n_const_coeff (S n) pol ns = false.
Proof.
intros pol ns n Hz Hn.
rewrite zerop_1st_n_const_coeff_succ2.
rewrite Hz, Bool.orb_false_l.
remember (S n) as sn; simpl; subst sn.
destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (S n) pol ns))); auto.
contradiction.
Qed.

Theorem root_tail_sep_1st_monom_any_r : ∀ pol ns pol₁ ns₁ c m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) n pol₁ ns₁ =
       ps_monom (nth_c n pol₁ ns₁) (nth_γ n pol₁ ns₁) +
       ps_monom 1%K (nth_γ n pol₁ ns₁) *
       root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ n r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi Hri H₀.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz₁.
 discriminate Hz₁.

 remember (m * q₀)%positive as m₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 move Hc₁ before Hns₁.
 move c₁ before c.
 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁.
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; eauto ).
 pose proof (Hpsi O (Nat.le_0_l n)) as H; simpl in H.
 rename H into Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as Hns₁i; clear HeqHns₁i.
 eapply hd_newton_segments₉ in Hns₁i; eauto .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
 remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
 remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
 remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
 remember (nth_ns n pol₂ ns₂) as nsn₂ eqn:Hnsn₂ .
 remember Hns as H; clear HeqH.
 eapply r_n_nth_ns with (poln := poln₁) in H; eauto .
 destruct H as (αjn₁, (αkn₁, H)).
 destruct H as (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁))).
 remember Hnsn₁ as H; clear HeqH.
 erewrite nth_ns_n with (c := c) in H; eauto .
 erewrite <- nth_pol_n with (c := c) in H; eauto .
 rewrite <- Hpoln₁ in H.
 rename H into Hnsn₁h.
 remember Hnsn₁h as H; clear HeqH.
 eapply newton_segments_not_nil in H; eauto .
 rename H into Hns₁nz.
 remember Hnsn₁h as H; clear HeqH.
 apply List_hd_in in H; auto.
 rename H into Hnsn₁i.
 pose proof (Hri (S n)) as Hrn₁; simpl in Hrn₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrn₁.
 erewrite nth_r_n in Hrn₁; eauto .
 erewrite nth_c_n in Hrn₁; eauto .
 rewrite <- Hcn₁ in Hrn₁.
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; eauto .
 rewrite <- Heqm₁ in H.
 rename H into HK₁.
 move HK₁ before Hns₁i.
 assert (∀ i, nth_r i pol₁ ns₁ = r) as Hri₁.
  intros i.
  pose proof (Hri (S i)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

  move Hri₁ before HK₁.
  remember Hns₁i as H; clear HeqH.
  eapply nth_pol_in_K_1_m in H; eauto .
  rename H into HKn₁.
  remember (S n) as sn.
  unfold root_tail, ps_monom; simpl.
  do 2 rewrite fold_series_const.
  subst sn.
  rewrite zerop_1st_n_const_coeff_succ2.
  rewrite Hz₁.
  rewrite Bool.orb_false_l.
  simpl.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
  rewrite <- Hpoln₂, <- Hnsn₂.
  rewrite <- Hpoln₁, <- Hnsn₁.
  erewrite nth_c_n; eauto .
  rewrite <- Hcn₁.
  destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
   rewrite ps_mul_0_r, ps_add_0_r.
   unfold root_tail_from_cγ_list; simpl.
   rewrite Hinin₁, Hfinn₁; simpl.
   rewrite Hαkn₁; simpl.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   rewrite Z.mul_1_r, Z.add_0_r, Nat.sub_0_r.
   rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_r; simpl; auto.
   erewrite αj_m_eq_p_r with (ns₁ := nsn₁); eauto .
   rewrite Pos2Z.inj_mul.
   rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
   rewrite <- Zposnat2Znat; auto.
   rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
   remember (Qden (nth_γ n pol₁ ns₁)) as d₁ eqn:Hd₁ .
   rewrite ps_adjust_eq with (n := O) (k := d₁); symmetry.
   rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
   unfold adjust_ps; simpl.
   do 2 rewrite series_shift_0.
   rewrite series_stretch_const.
   do 2 rewrite Z.sub_0_r.
   rewrite Pos.mul_comm.
   apply mkps_morphism; auto.
    rewrite <- series_stretch_const with (k := d₁).
    apply stretch_morph; auto.
    constructor; intros i; simpl.
    unfold root_tail_series_from_cγ_list; simpl.
    destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₁| H₁].
     exfalso; revert H₁.
     eapply a₀_neq_0; eauto .

     rewrite <- Hcn₁.
     erewrite <- nth_ns_n with (c := c₁); eauto .
     erewrite <- nth_pol_n with (c := c₁); eauto .
     rewrite <- Hpoln₂, <- Hnsn₂.
     destruct i; simpl; [ rewrite Hcn₁; eauto  | idtac ].
     destruct (ps_zerop R (ps_poly_nth 0 poln₂)); auto; contradiction.

    subst d₁.
    erewrite nth_γ_n; eauto ; simpl.
    rewrite Hαkn₁; simpl.
    rewrite Qnum_inv_Qnat_sub; auto.
    rewrite Qden_inv_Qnat_sub; auto.
    rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
    rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
    do 2 rewrite Pos2Z.inj_mul.
    rewrite Z.mul_assoc.
    apply Z.mul_cancel_r; auto.
    erewrite αj_m_eq_p_r; eauto .
    rewrite Zposnat2Znat; auto.
    rewrite Z.mul_assoc, Z.mul_shuffle0.
    reflexivity.

   rename H₂ into Hnzn₂.
   move Hnzn₂ before Hnsn₂.
   remember Hpoln₂ as H; clear HeqH.
   erewrite <- nth_pol_succ2 with (c := c₁) in H; eauto .
   rename H into Hpoln₂₁.
   move Hpoln₂₁ before Hpoln₂.
   remember Hpsi as H; clear HeqH.
   apply zerop_1st_n_const_coeff_false_iff in H.
   remember Hnzn₂ as HH; clear HeqHH.
   rewrite Hpoln₂₁ in HH.
   apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
   rewrite zerop_1st_n_const_coeff_false_iff in H.
   clear Hpsi; rename H into Hpsi; move Hpsi after Hri.
   remember Hns as H; clear HeqH.
   eapply r_n_nth_ns with (poln := poln₂) (n := S n) in H; eauto .
bbb.

cf RootHeadTail.v around line 3122
*)

Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → ∀ n,
    (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b n pol₁ ns₁ +
       ps_monom 1%K (γ_sum b n pol₁ ns₁) *
       root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri H₀ n.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri.
revert b c m q₀ m₁ Heqm₁.
induction n; intros.
 unfold root_head; simpl.
 remember (zerop_1st_n_const_coeff b pol₁ ns₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  rewrite rng_add_0_l.
  unfold root_tail.
  rewrite Hz₁, Nat.add_1_r.
  rewrite zerop_1st_n_const_coeff_succ2.
  rewrite Hz₁, Bool.orb_true_l.
  rewrite rng_mul_0_r; reflexivity.

  rewrite Nat.add_0_r, rng_add_0_r, Heqm₁.
  rewrite root_tail_from_0_const_r; eauto .
  unfold root_head.
  rewrite Hz₁.
  unfold root_head_from_cγ_list.
  rewrite Nat.add_0_r, rng_add_0_r.
  reflexivity.

 remember (zerop_1st_n_const_coeff b pol₁ ns₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  unfold root_head, root_tail.
  rewrite Hz₁.
  rewrite zerop_1st_n_const_coeff_true_if; auto.
  rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

  rewrite root_head_succ; auto.
  remember (zerop_1st_n_const_coeff (b + S n) pol₁ ns₁) as z eqn:Hz .
  symmetry in Hz.
  destruct z.
   rewrite rng_add_0_r, Nat.add_succ_r.
   rewrite IHn; eauto .
   apply rng_add_compat_l.
   unfold γ_sum at 2; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite fold_γ_sum, ps_monom_add_r.
   rewrite <- rng_mul_assoc.
   apply rng_mul_compat_l.
   unfold root_tail.
   rewrite Hz.
   remember (b + S n)%nat as x; rewrite <- Nat.add_1_r; subst x.
   rewrite zerop_1st_n_const_coeff_true_if; auto.
   rewrite rng_mul_0_r; reflexivity.

   rewrite IHn; eauto .
   rewrite <- rng_add_assoc.
   apply rng_add_compat_l; simpl.
   symmetry.
   rewrite ps_monom_split_mul.
   rewrite rng_mul_comm, <- rng_mul_add_distr_l.
   unfold γ_sum at 1; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite fold_γ_sum, ps_monom_add_r.
   rewrite <- rng_mul_assoc.
   apply rng_mul_compat_l.
   rewrite rng_mul_add_distr_l.
   rewrite rng_mul_comm; simpl.
   rewrite <- ps_monom_split_mul.
   symmetry.
   do 3 rewrite Nat.add_succ_r.
   rewrite Heqm₁.
   eapply root_tail_sep_1st_monom_any_r; eauto .
   rewrite <- Nat.add_succ_r.
   apply zerop_1st_n_const_coeff_false_iff.
   assumption.
Qed.

Theorem zzz : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns c pol₁ Hns Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 destruct (exists_or_not_forall (multiplicity_decreases pol ns)) as [Hn|Hn].
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
   erewrite <- nth_r_n in Hrn; eauto ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn.
    2: subst; auto.

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
      remember (nth_pol (S i) pol ns) as polsi eqn:Hpolsi.
      remember (nth_ns (S i) pol ns) as nssi eqn:Hnssi.
      remember (newton_segments polsi) as nsl eqn:Hnsl .
      symmetry in Hnsl.
      destruct nsl as [| ns₂].
       Focus 2.
       eapply IHm in Hri.
        Focus 5.
        symmetry.
        apply nth_r_n; eauto .

        Focus 3.
        erewrite nth_c_n; eauto .

        3: eauto .

        Focus 2.
        eapply List_hd_in.
         subst nssi.
         simpl.
         eapply nth_ns_n; eauto .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          symmetry.
          eapply <- nth_pol_n; eauto .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        destruct Hri as (s₁, Hs₁).
        remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
        symmetry in Hz.
        destruct z.
         Focus 2.
         remember (root_head 0 i pol₁ ns₁) as rh.
         remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
         exists (rh + mo * s₁)%ps; subst rh mo.
         rewrite apply_nth_pol; auto.
         erewrite nth_pol_n; eauto .
         erewrite <- nth_c_n; eauto .
         rewrite Hs₁, rng_mul_0_r; reflexivity.

         apply lowest_zerop_1st_n_const_coeff in Hz.
         destruct Hz as (m, (Hmi, (Hle, Heq))).
         destruct Hle as [Hle| Hle].
          subst m.
          simpl in Heq.
          destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
           2: discriminate Heq.

           exists 0%ps.
           apply a₀_0_root_0; assumption.

          eapply root_when_fin; eauto .

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

          eapply root_when_fin; eauto .

         eapply List_hd_in; eauto .
         clear H.
         remember Hns as H; clear HeqH.
         eapply next_has_root_0_or_newton_segments in H; eauto .
         simpl in H.
         rewrite <- Hc, <- Hpol₁ in H.
         destruct H; auto.
bbb.

End theorems.
