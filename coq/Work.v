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
Require Import Puiseux.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

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
remember (m * q₀)%positive as m₁.
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
 destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [Hps₀| Hps₀].
  pose proof (Hpsi 0%nat (Nat.le_0_l 0)) as H.
  contradiction.

  remember Hns as HinK1m₁; clear HeqHinK1m₁.
  eapply next_pol_in_K_1_mq in HinK1m₁; eauto .
  remember Hns as H; clear HeqH.
  eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
  subst j₁ k₁; simpl.
  unfold Qlt in Hαj₁; simpl in Hαj₁.
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαj₁, Hαk₁.
  remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
  eapply hd_newton_segments in Hns₁₁; eauto .
  remember Hns₁₁ as HK₂; clear HeqHK₂.
  eapply next_pol_in_K_1_mq in HK₂; eauto .
  erewrite q_eq_1 with (q₀ := q₀) (ns := ns) in HK₂; eauto .
  rewrite Pos.mul_1_r, <- Heqm₁ in HK₂.
  unfold γ_sum; simpl.
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
  destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [Hps₁| Hps₁].
   rewrite ps_mul_0_r, ps_add_0_r.
   unfold root_from_cγ_list, ps_monom; simpl.
   rewrite Hini₁, Hfin₁; simpl.
   rewrite Hαk₁; simpl.
   rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
   rewrite Z.mul_shuffle0.
   rewrite Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_r; auto.
   rewrite ps_adjust_eq with (n := O) (k := (Qden αj₁ * Qden αk₁)%positive).
   symmetry.
   rewrite ps_adjust_eq with (n := O) (k := m₁).
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

        simpl.
        destruct (ps_zerop R (ps_poly_nth 0 pol₂)); auto; contradiction.

      destruct (zerop i); [ subst i | reflexivity ].
      rewrite Nat.mod_0_l in H₁; auto.
      exfalso; revert H₁; apply Nat.lt_irrefl.

     rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0.
     rewrite <- Z.mul_assoc, Z.mul_comm; reflexivity.

     rewrite Pos.mul_comm; reflexivity.

    eapply den_αj_divides_num_αj_m; eauto .
    rewrite Heqm₁.
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
   rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
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
     remember Hns₂₁ as HH; clear HeqHH.
     eapply num_m_den_is_pos in HH; eauto .
     destruct H as (d, Hd).
     rewrite Hd in HH.
     rewrite Z.div_mul in HH; auto.
     rewrite Hd.
     rewrite Z.div_mul; auto.
     destruct d as [| d| d].
      exfalso; revert HH; apply Nat.lt_irrefl.

      clear HH; simpl.
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

        remember (next_pow 0 ns₂ m₁) as g₂.
        rewrite <- Hnpow.
        destruct (lt_dec i g₂) as [H₂| H₂].
         unfold root_series_from_cγ_list; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [| H₃]; auto.
         destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
         clear H₁.
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [| H₅]; auto.
         rewrite <- Heqg₂.
         remember (Nat.compare g₂ (S i)) as cmp; symmetry in Heqcmp.
         destruct cmp as [H₄| H₄| H₄]; auto.
          apply nat_compare_eq in Heqcmp.
          rewrite Heqcmp in H₂.
          exfalso; revert H₂; apply Nat.lt_irrefl.

          apply nat_compare_lt in Heqcmp.
          apply Nat.lt_le_incl, Nat.nlt_ge in Heqcmp.
          contradiction.

         remember (i - g₂)%nat as id.
         unfold root_series_from_cγ_list.
         remember (S id) as x; simpl; subst x.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
          contradiction.

          rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
          rewrite <- Heqg₂, Heqid.
          destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
          apply Nat.nlt_ge in H₂.
          symmetry.
          rewrite <- find_coeff_add with (dp := g₂).
          rewrite Nat.add_0_l, Nat.sub_add; auto.
          symmetry.
          rewrite <- Heqid; simpl.
          destruct (ps_zerop R (ps_poly_nth 0 pol₂)); try contradiction.
          clear n.
          remember (Nat.compare g₂ (S i)) as cmp eqn:Hcmp .
          symmetry in Hcmp.
          destruct cmp; auto.
          remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
          remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
          remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
          remember (next_pow g₂ ns₃ m₁) as g₂₃ eqn:Hg₂₃ .
          apply nat_compare_lt in Hcmp.
          clear H₁ H₂.
          assert (q_of_m m₁ (γ ns₂) = 1%positive) as Hq₂.
           replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
           rewrite <- Heqm₁ in HinK1m₁.
           eapply q_eq_1 with (pol := pol₁) (pol₁ := pol₂); eauto .
           rewrite Pos.mul_1_r; assumption.

           remember Hns₁₁ as Hr₂; clear HeqHr₂.
           eapply multiplicity_1_remains in Hr₂; eauto .
           rename g₂ into g₁.
           remember (S i) as j.
           rewrite <- Nat.add_1_r in Heqj.
           remember 1%nat as di eqn:Hdi  in Heqj.
           subst j.
           assert (0 < g₁)%nat as Hg₁ by (rewrite Hnpow; auto).
           clear Hnpow Heqg₂.
           revert g₁ id i di Hg₁ Hg₂₃ Heqid Hcmp Hdi Hr₂ Hpol₃ Hns₃ Hns₂₁ Hc₂
            Hq₂ HK₂; clear; intros.
           revert pol₂ ns₂ c₂ pol₃ ns₃ g₁ g₂₃ i di id Hns₂₁ HK₂ Hq₂ Hc₂ Hr₂
            Hpol₃ Hns₃ Hdi Hg₁ Hcmp Hg₂₃ Heqid.
           clear; intros.
(*1*)
           destruct i.
            destruct g₁; [ exfalso; revert Hg₁; apply Nat.lt_irrefl | idtac ].
            replace id with O by omega; reflexivity.

            destruct id; [ exfalso; fast_omega Hcmp Heqid Hdi | simpl ].
            destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₁| H₁]; auto.
            unfold next_pow in Hg₂₃; simpl in Hg₂₃.
            remember Hr₂ as H; clear HeqH.
            eapply r_1_next_ns in H; eauto .
            destruct H as (αj₃, (αk₃, H)).
            destruct H as (Hoth₃, (Hini₃, (Hfin₃, (Hαj₃, Hαk₃)))).
            rewrite Hini₃, Hfin₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Hαk₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Z.add_0_r, Z.mul_1_r in Hg₂₃.
            do 2 rewrite Pos.mul_1_r in Hg₂₃.
            rewrite Z.mul_shuffle0 in Hg₂₃.
            rewrite Pos2Z.inj_mul in Hg₂₃.
            rewrite Z.div_mul_cancel_r in Hg₂₃; auto.
            remember Hns₃ as Hns₃₁; clear HeqHns₃₁.
            eapply hd_newton_segments in Hns₃₁; eauto .
            remember (Nat.compare g₂₃ (S (i + di))) as cmp₁ eqn:Hcmp₁ .
            symmetry in Hcmp₁.
            destruct cmp₁; auto.
            remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
            remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄ eqn:Hpol₄ .
            remember (List.hd phony_ns (newton_segments pol₄)) as ns₄
             eqn:Hns₄ .
            remember (next_pow g₂₃ ns₄ m₁) as g₂₃₄ eqn:Hg₂₃₄ .
            apply nat_compare_lt in Hcmp₁.
            assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₃)) as HK₃.
             replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
             eapply next_pol_in_K_1_mq with (pol := pol₂); eauto .

             remember Hns₃₁ as H; clear HeqH.
             eapply num_m_den_is_pos with (m := m₁) in H; eauto .
(**)
             clear Hcmp.
             assert (g₁ < i + di)%nat as Hcmp by fast_omega H Hg₂₃ Hcmp₁.
             assert (q_of_m m₁ (γ ns₃) = 1%positive) as Hq₃.
              replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
              eapply q_eq_1 with (pol := pol₂) (pol₁ := pol₃); eauto .
              rewrite Pos.mul_1_r; assumption.

              remember Hns₂₁ as Hr₃; clear HeqHr₃.
              eapply multiplicity_1_remains in Hr₃; eauto .
              clear H₁ Hcmp₁.
              rename Hg₂₃ into Hggg.
              remember (Z.to_nat (Qnum αj₃ * ' m₁ / ' Qden αj₃)) as g₀.
              clear Heqg₀.
              rename H into Hgnz.
              rename Hg₂₃₄ into Hg₂₃.
              rename g₂₃ into g₂.
              rename g₂₃₄ into g₂₃.
              clear pol₂ HK₂ Hns₂₁ Hc₂ Hpol₃ Hr₂.
              clear ns₂ Hq₂.
              rename pol₃ into pol₂.
              rename pol₄ into pol₃.
              rename Hpol₄ into Hpol₃.
              rename Hr₃ into Hr₂.
              clear αj₃ αk₃ Hoth₃ Hini₃ Hfin₃ Hαj₃ Hαk₃.
              rename ns₃ into ns₂.
              rename ns₄ into ns₃.
              rename Hns₃ into Hns₂.
              rename Hns₃₁ into Hns₂₁.
              rename Hns₄ into Hns₃.
              clear c₂.
              rename c₃ into c₂.
              rename Hc₃ into Hc₂.
              rewrite Nat.add_succ_l, <- Nat.add_succ_r in Heqid.
              remember (S di) as dj.
              subst di.
              rename dj into di.
              rename Heqdj into Hdi.
              replace (S (i + 1)) with (i + di)%nat by omega.
              rename HK₃ into HK₂.
(*2*)
           destruct i.
            destruct g₁; [ exfalso; revert Hg₁; apply Nat.lt_irrefl | idtac ].
            replace id with O by omega; reflexivity.

            destruct id; [ exfalso; fast_omega Hcmp Heqid Hdi | simpl ].
            destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₁| H₁]; auto.
            unfold next_pow in Hg₂₃; simpl in Hg₂₃.
            remember Hr₂ as H; clear HeqH.
            eapply r_1_next_ns in H; eauto .
            destruct H as (αj₃, (αk₃, H)).
            destruct H as (Hoth₃, (Hini₃, (Hfin₃, (Hαj₃, Hαk₃)))).
            rewrite Hini₃, Hfin₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Hαk₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Z.add_0_r, Z.mul_1_r in Hg₂₃.
            do 2 rewrite Pos.mul_1_r in Hg₂₃.
            rewrite Z.mul_shuffle0 in Hg₂₃.
            rewrite Pos2Z.inj_mul in Hg₂₃.
            rewrite Z.div_mul_cancel_r in Hg₂₃; auto.
            remember Hns₃ as Hns₃₁; clear HeqHns₃₁.
            eapply hd_newton_segments in Hns₃₁; eauto .
            remember (Nat.compare g₂₃ (S (i + di))) as cmp₁ eqn:Hcmp₁ .
            symmetry in Hcmp₁.
            destruct cmp₁; auto.
            remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
            remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄ eqn:Hpol₄ .
            remember (List.hd phony_ns (newton_segments pol₄)) as ns₄
             eqn:Hns₄ .
            remember (next_pow g₂₃ ns₄ m₁) as g₂₃₄ eqn:Hg₂₃₄ .
            apply nat_compare_lt in Hcmp₁.
            assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₃)) as HK₃.
             replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
             eapply next_pol_in_K_1_mq with (pol := pol₂); eauto .

             remember Hns₃₁ as H; clear HeqH.
             eapply num_m_den_is_pos with (m := m₁) in H; eauto .
(**)
             clear Hq₃.
             subst g₂.
             clear Hcmp.
             assert (g₁ < i + di)%nat as Hcmp by fast_omega H Hg₂₃ Hcmp₁.
             assert (q_of_m m₁ (γ ns₃) = 1%positive) as Hq₃.
              replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
              eapply q_eq_1 with (pol := pol₂) (pol₁ := pol₃); eauto .
              rewrite Pos.mul_1_r; assumption.

              remember Hns₂₁ as Hr₃; clear HeqHr₃.
              eapply multiplicity_1_remains in Hr₃; eauto .
              clear H₁.
              rename Hcmp₁ into Hcmp₂.
              rename Hg₂₃ into Hggg.
              remember (Z.to_nat (Qnum αj₃ * ' m₁ / ' Qden αj₃)) as g.
              rewrite <- Nat.add_assoc in Hggg.
              assert (1 < g₀ + g)%nat as Hg' by fast_omega Hgnz H.
              remember (g₀ + g)%nat as g'.
              clear Heqg' g g₀ Hgnz H Heqg.
              rename g' into g₀.
              rename Hg' into Hgnz.
              rename Hg₂₃₄ into Hg₂₃.
              rename g₂₃ into g₂.
              rename g₂₃₄ into g₂₃.
              clear pol₂ HK₂ Hns₂ Hns₂₁ Hc₂ Hpol₃ Hr₂.
              clear ns₂.
              rename pol₃ into pol₂.
              rename pol₄ into pol₃.
              rename Hpol₄ into Hpol₃.
              rename Hr₃ into Hr₂.
              clear αj₃ αk₃ Hoth₃ Hini₃ Hfin₃ Hαj₃ Hαk₃.
              rename ns₃ into ns₂.
              rename ns₄ into ns₃.
              rename Hns₃ into Hns₂.
              rename Hns₃₁ into Hns₂₁.
              rename Hns₄ into Hns₃.
              clear c₂.
              rename c₃ into c₂.
              rename Hc₃ into Hc₂.
              rewrite Nat.add_succ_l, <- Nat.add_succ_r in Heqid.
              remember (S di) as dj.
              subst di.
              rename dj into di.
              rename Heqdj into Hdi.
              replace (S (i + 2)) with (i + di)%nat by omega.
              rename HK₃ into HK₂.
(*3*)
           destruct i.
            destruct g₁; [ exfalso; revert Hg₁; apply Nat.lt_irrefl | idtac ].
            replace id with O by omega; reflexivity.

            destruct id; [ fast_omega Hcmp₂ Heqid Hdi Hggg Hgnz | simpl ].
            destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₁| H₁]; auto.
            unfold next_pow in Hg₂₃; simpl in Hg₂₃.
            remember Hr₂ as H; clear HeqH.
            eapply r_1_next_ns in H; eauto .
            destruct H as (αj₃, (αk₃, H)).
            destruct H as (Hoth₃, (Hini₃, (Hfin₃, (Hαj₃, Hαk₃)))).
            rewrite Hini₃, Hfin₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Hαk₃ in Hg₂₃; simpl in Hg₂₃.
            rewrite Z.add_0_r, Z.mul_1_r in Hg₂₃.
            do 2 rewrite Pos.mul_1_r in Hg₂₃.
            rewrite Z.mul_shuffle0 in Hg₂₃.
            rewrite Pos2Z.inj_mul in Hg₂₃.
            rewrite Z.div_mul_cancel_r in Hg₂₃; auto.
            remember Hns₃ as Hns₃₁; clear HeqHns₃₁.
            eapply hd_newton_segments in Hns₃₁; eauto .
            remember (Nat.compare g₂₃ (S (i + di))) as cmp₁ eqn:Hcmp₁ .
            symmetry in Hcmp₁.
            destruct cmp₁; auto.
            remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
            remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄ eqn:Hpol₄ .
            remember (List.hd phony_ns (newton_segments pol₄)) as ns₄
             eqn:Hns₄ .
            remember (next_pow g₂₃ ns₄ m₁) as g₂₃₄ eqn:Hg₂₃₄ .
            apply nat_compare_lt in Hcmp₁.
            assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₃)) as HK₃.
             replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
             eapply next_pol_in_K_1_mq with (pol := pol₂); eauto .

             remember Hns₃₁ as H; clear HeqH.
             eapply num_m_den_is_pos with (m := m₁) in H; eauto .
(**)
             clear Hq₃.
             subst g₂.
             clear Hcmp.
             assert (g₁ < i + di)%nat as Hcmp by fast_omega H Hg₂₃ Hcmp₁.
             assert (q_of_m m₁ (γ ns₃) = 1%positive) as Hq₃.
              replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
              eapply q_eq_1 with (pol := pol₂) (pol₁ := pol₃); eauto .
              rewrite Pos.mul_1_r; assumption.

              remember Hns₂₁ as Hr₃; clear HeqHr₃.
              eapply multiplicity_1_remains in Hr₃; eauto .
              clear H₁.
              rename Hcmp₁ into Hcmp₃.
              rename Hg₂₃ into Hggg.
              remember (Z.to_nat (Qnum αj₃ * ' m₁ / ' Qden αj₃)) as g.
              rewrite <- Nat.add_assoc in Hggg.
              assert (1 < g₀ + g)%nat as Hg' by fast_omega Hgnz H.
              remember (g₀ + g)%nat as g'.
              rename Heqg' into Heqg''.
              rename Hgnz into Hgnz'.
              rename H into Hgnz''.
              clear Heqg.
              rename g₀ into g'₀.
              rename g' into g₀.
              rename Hg' into Hgnz.
              rename Hg₂₃₄ into Hg₂₃.
              rename g₂₃ into g₂.
              rename g₂₃₄ into g₂₃.
              clear pol₂ HK₂ Hns₂ Hns₂₁ Hc₂ Hpol₃ Hr₂.
              clear ns₂.
              rename pol₃ into pol₂.
              rename pol₄ into pol₃.
              rename Hpol₄ into Hpol₃.
              rename Hr₃ into Hr₂.
              clear αj₃ αk₃ Hoth₃ Hini₃ Hfin₃ Hαj₃ Hαk₃.
              rename ns₃ into ns₂.
              rename ns₄ into ns₃.
              rename Hns₃ into Hns₂.
              rename Hns₃₁ into Hns₂₁.
              rename Hns₄ into Hns₃.
              clear c₂.
              rename c₃ into c₂.
              rename Hc₃ into Hc₂.
              rewrite Nat.add_succ_l, <- Nat.add_succ_r in Heqid.
              remember (S di) as dj.
              subst di.
              rename dj into di.
              rename Heqdj into Hdi.
              replace (S (i + 3)) with (i + di)%nat by omega.
              rename HK₃ into HK₂.
(*4*)
           destruct i.
            destruct g₁; [ exfalso; revert Hg₁; apply Nat.lt_irrefl | idtac ].
            replace id with O by omega; reflexivity.

            destruct id; [ exfalso; omega | simpl ].
bbb.

          rewrite qqq with (d := (g₂ - 1)%nat).
           rewrite Nat_sub_sub_distr.
            rewrite Nat.add_1_r.
            rewrite <- Nat.sub_succ_l; auto.

            rewrite Hnpow.
            apply Pos2Nat.is_pos.

           apply Nat.le_sub_le_add_l.
           apply Nat.le_le_succ_r; reflexivity.
bbb.
         unfold root_series_from_cγ_list; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
          contradiction.

          destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₄| H₄].
           contradiction.

           rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
           remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
           remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
           remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
           destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
           simpl.
           clear H₁.
           destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₁| H₁].
            contradiction.

            rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
            rewrite <- Heqg₂.
            remember (Nat.compare g₂ (S i)) as cmp₁ eqn:Hcmp₁ .
            symmetry in Hcmp₁.
            destruct cmp₁.
             apply nat_compare_eq in Hcmp₁.
             destruct id; auto.
             rewrite Hcmp₁ in Heqid.
             rewrite Nat.sub_diag in Heqid.
             discriminate Heqid.

             Focus 2.
             apply nat_compare_gt in Hcmp₁.
             contradiction.

             apply nat_compare_lt in Hcmp₁.
             destruct id; [ exfalso; fast_omega Heqid Hcmp₁ | idtac ].
             rewrite Heqid.
             remember (next_pow g₂ ns₃ m₁) as g₂₃ eqn:Hg₂₃ .
             remember (next_pow 0 ns₃ m₁) as g₃ eqn:Hg₃ .
             eapply next_next_pow in Hg₂₃; eauto .
             simpl in Hg₂₃.
             subst g₂₃.
             destruct g₂.
              symmetry in Hnpow.
              exfalso; revert Hnpow; apply Pos2Nat_ne_0.

              simpl.
              apply lt_S_n in Hcmp₁.
              apply Nat.nlt_ge in H₂.
              apply le_S_n in H₂.
              destruct i; [ reflexivity | idtac ].
bbb.
              simpl.
              destruct g₂.
               Focus 2.
               simpl in Heqid.
               rewrite <- Heqid.
               simpl.
               destruct (ps_zerop R (ps_poly_nth 0 pol₃)); auto.
               assert (i = g₂ + S id)%nat as Hig by omega.
               rewrite Hig.
               remember (g₃ + S (S g₂))%nat as x.
               rewrite Nat.add_comm.
               rewrite Nat.add_succ_l, <- Nat.add_succ_r.
               rewrite <- Nat.add_succ_r.
               rewrite <- Nat.add_succ_l.
               subst x.
               rewrite <- nat_compare_add.
               remember (Nat.compare g₃ (S id)) as cmp eqn:Hcmp .
               symmetry in Hcmp.
               destruct cmp; auto.
               apply nat_compare_lt in Hcmp.
               rewrite next_pow_add.
               remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
               remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄ eqn:Hpol₄ .
               remember (List.hd phony_ns (newton_segments pol₄)) as ns₄
                eqn:Hns₄ .
               remember (next_pow g₃ ns₄ m₁) as g₃₄.
               destruct id.
                simpl.
                destruct (ps_zerop R (ps_poly_nth 0 pol₄)); auto.
                remember (g₃₄ + S (S g₂))%nat as x.
                rewrite <- Nat.add_1_l.
                subst x.
                rewrite <- nat_compare_add.
                remember (Nat.compare g₃₄ 1).
                symmetry in Heqc0.
                destruct c0; auto.
                 apply nat_compare_eq in Heqc0.
                 move Heqc0 at top; subst g₃₄.
                 apply Nat.lt_1_r in Hcmp.
                 move Hcmp at top; subst g₃.
                 unfold next_pow in Hg₃; simpl in Hg₃.
bbb.
              apply rrr; assumption.
bbb.
              revert g₂ Hcmp₁.
              induction i; intros; [ reflexivity | idtac ].
              destruct g₂.
               rewrite Nat.sub_0_r.
               simpl.
               destruct (ps_zerop R (ps_poly_nth 0 pol₃)) as [H₂| H₂]; auto.
               remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
               remember (next_pol pol₃ (β ns₃) (γ ns₃) c₃) as pol₄ eqn:Hpol₄ .
               remember (List.hd phony_ns (newton_segments pol₄)) as ns₅
                eqn:Hns₅ .
               remember (Nat.compare (g₃ + 1) (S (S i))) as cmp₂ eqn:Hcmp₂ .
               remember (Nat.compare g₃ (S i)) as cmp₃ eqn:Hcmp₃ .
               symmetry in Hcmp₂, Hcmp₃.
               destruct cmp₂.
                apply nat_compare_eq in Hcmp₂.
                destruct cmp₃; auto.
                 apply nat_compare_lt in Hcmp₃.
                 exfalso; fast_omega Hcmp₂ Hcmp₃.

                 apply nat_compare_gt in Hcmp₃.
                 exfalso; fast_omega Hcmp₂ Hcmp₃.

                apply nat_compare_lt in Hcmp₂.
                destruct cmp₃.
                 apply nat_compare_eq in Hcmp₃.
                 exfalso; fast_omega Hcmp₂ Hcmp₃.
bbb.

(* mmm... faut voir... *)
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
