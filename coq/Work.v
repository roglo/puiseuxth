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

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

(* cf root_tail_from_0 *)
Theorem root_tail_from_0₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri H₀.
remember (m * q₀)%positive as m₁.
destruct b; [ subst m₁; eapply root_tail_split_1st_any_r; eauto  | idtac ].
remember (S b) as b₁ eqn:Hb₁ .
unfold root_tail, root_head; simpl.
rewrite Nat.add_0_r.
remember (zerop_1st_n_const_coeff b₁ pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 rewrite Nat.add_1_r.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁; simpl.
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 rewrite rng_add_0_r.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 rewrite Nat.add_0_r, rng_add_0_r.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 rewrite <- Heqm₁ in HK₁.
 rewrite Hb₁ in Hz₁.
 rewrite zerop_1st_n_const_coeff_succ in Hz₁.
 apply Bool.orb_false_iff in Hz₁.
 destruct Hz₁ as (Hz₁, Hpsi).
 simpl in Hz₁.
 rewrite Nat.add_1_r.
 rewrite zerop_1st_n_const_coeff_succ.
 remember (zerop_1st_n_const_coeff 0 pol₁ ns₁) as x.
 simpl in Heqx.
 remember (ps_poly_nth 0 pol₁) as y.
 destruct (ps_zerop R y) as [| Hnz₁]; [ discriminate Hz₁ | subst y ].
 clear Hz₁; subst x.
 rewrite Bool.orb_false_l, Hb₁.
 rewrite zerop_1st_n_const_coeff_succ2, Hpsi.
 rewrite Bool.orb_false_l.
 rewrite <- Hb₁.
 remember (S b₁) as sb₁; simpl; subst sb₁.
 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 assert (0 < r)%nat as Hrpos.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀.
  apply multiplicity_neq_0; auto.

  remember Hns₁ as H; clear HeqH.
  eapply r_n_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  assert (∀ i : nat, i ≤ b₁ → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
   apply zerop_1st_n_const_coeff_false_iff; subst b₁.
   rewrite zerop_1st_n_const_coeff_succ.
   rewrite Hpsi, Bool.orb_false_r; simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.
   contradiction.

   clear Hpsi; rename H into Hpsi.
   remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
   eapply List_hd_in in Hns₁₁; eauto .
    remember Hns₁₁ as H; clear HeqH.
    eapply nth_in_newton_segments_any_r with (n := b₁) in H; eauto .
     remember (nth_pol b₁ pol₁ ns₁) as polb eqn:Hpolb .
     remember (nth_ns b₁ pol₁ ns₁) as nsb eqn:Hnsb .
     rename H into Hbns.
     pose proof (Hri (S b₁)) as Hrb; simpl in Hrb.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb.
     erewrite nth_r_n in Hrb; eauto .
     erewrite nth_c_root in Hrb; eauto .
     remember Hbns as H; clear HeqH.
     apply exists_ini_pt_nat in H.
     destruct H as (jb, (αjb, Hinib)).
     remember Hbns as H; clear HeqH.
     apply exists_fin_pt_nat in H.
     destruct H as (kb, (αkb, Hfinb)).
     remember (ac_root (Φq polb nsb)) as cb eqn:Hcb .
     remember (nth_pol (b₁ + 1) pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
     subst b₁.
     simpl in Hpolb, Hnsb, Hpolb₂.
     rewrite <- Hc₁, <- Hpol₂ in Hpolb, Hnsb, Hpolb₂.
     rewrite <- Hns₂ in Hpolb, Hnsb, Hpolb₂.
     rewrite <- Nat.add_1_r, <- Hpolb₂.
     remember Hns₁₁ as H; clear HeqH.
     eapply nth_in_newton_segments_any_r with (n := b) in H; eauto .
      remember (nth_ns b pol₁ ns₁) as nsb₁ eqn:Hnsb₁ .
      remember (nth_pol b pol₁ ns₁) as polb₁ eqn:Hpolb₁ .
      remember (ac_root (Φq polb₁ nsb₁)) as cb₁ eqn:Hcb₁ .
      pose proof (Hpsi (S b) (Nat.le_refl (S b))) as Hpsb.
      simpl in Hpsb.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpsb.
      erewrite <- nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
      erewrite nth_ns_n with (c := c₁) in Hnsb; eauto .
      eapply r_n_j_0_k_n with (ns₁ := nsb) (m := (m * q₀)%positive) in H;
       eauto .
       Focus 2.
       eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁) (n := b); eauto .
        eapply next_pol_in_K_1_mq with (ns := ns); eauto .

        rewrite <- Heqm₁.
        eapply q_eq_1_any_r with (ns := ns₁); eauto .
        rewrite Hr₁; assumption.

        intros i.
        clear H.
        pose proof (Hri (S i)) as H; simpl in H.
        rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

       erewrite <- nth_ns_n with (c := c₁) in Hnsb; eauto .
       erewrite nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
       rewrite <- Hpolb in Hpsb.
       destruct H as (Hjb, (Hkb, (Hαjb, Hαkb))).
       subst jb kb.
       unfold Qlt in Hαjb; simpl in Hαjb.
       unfold Qeq in Hαkb; simpl in Hαkb.
       rewrite Z.mul_1_r in Hαjb, Hαkb.
       rewrite Nat.add_0_r in Hfinb.
       erewrite <- nth_r_n in Hfinb; eauto ;
        [ idtac | erewrite nth_c_root; eauto  ].
       pose proof (Hri (S b)%nat) as Hrsb₁; simpl in Hrsb₁.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrsb₁.
       rewrite Hrsb₁ in Hfinb.
       destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
        rewrite rng_mul_0_r, rng_add_0_r, Nat.add_1_r.
        unfold root_tail_from_cγ_list, ps_monom; simpl.
        rewrite Hinib, Hfinb; simpl.
        rewrite Hαkb; simpl.
        rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
        rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
        rewrite Qnum_inv_Qnat_sub; auto.
        rewrite Qden_inv_Qnat_sub; auto.
        rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
        rewrite <- Pos2Z.inj_mul.
        rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
        do 2 rewrite Pos2Z.inj_mul.
        rewrite Z.div_mul_cancel_r; auto.
         erewrite αj_m_eq_p_r; eauto .
          rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
          rewrite <- Z.mul_assoc.
          rewrite Z.div_mul.
           rewrite ps_adjust_eq with (n := O) (k := Qden (nth_γ b pol₂ ns₂)).
           symmetry.
           rewrite ps_adjust_eq with (n := O) (k := m₁).
           symmetry.
           unfold adjust_ps; simpl.
           rewrite Pos.mul_comm.
           do 2 rewrite Z.sub_0_r.
           rewrite fold_series_const.
           do 2 rewrite series_shift_0.
           rewrite series_stretch_const.
           apply mkps_morphism; auto.
            unfold series_stretch.
            constructor; intros i; simpl.
            remember (nth_γ b pol₂ ns₂) as γb eqn:Hγb .
            subst polb₂.
            rename H₁ into Hpolb₂.
            destruct (zerop (i mod Pos.to_nat (Qden γb))) as [H₁| H₁].
             apply Nat.mod_divides in H₁; auto.
             destruct H₁ as (d, Hd).
             rewrite Nat.mul_comm in Hd; rewrite Hd.
             rewrite Nat.div_mul; auto.
             unfold root_tail_series_from_cγ_list.
             rewrite <- Hd.
             destruct (zerop i) as [H₁| H₁].
              subst i.
              apply Nat.eq_mul_0_l in H₁; auto.
              subst d; simpl.
              destruct (ps_zerop R (ps_poly_nth 0 polb));
               [ contradiction | idtac ].
              symmetry.
              erewrite nth_c_root; eauto .

              simpl.
              rewrite <- Hcb.
              rewrite Nat.add_comm in Hpolb₂; simpl in Hpolb₂.
              remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
              remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
              remember (List.hd phony_ns (newton_segments pol₃)) as ns₃
               eqn:Hns₃ .
              remember (next_pol polb (β nsb) (γ nsb) cb) as polb' eqn:Hpolb' .
              remember (List.hd phony_ns (newton_segments polb')) as nsb'.
              rename Heqnsb' into Hnsb'.
              destruct d.
               rewrite Hd in H₁.
               exfalso; revert H₁; apply Nat.lt_irrefl.

               destruct (ps_zerop R (ps_poly_nth 0 polb)); auto; simpl.
               erewrite nth_pol_n with (c₁ := c₂) in Hpolb'; eauto .
               rewrite <- Hpolb' in Hpolb₂.
               destruct (ps_zerop R (ps_poly_nth 0 polb')) as [H₃| H₃]; auto.
               contradiction.

             destruct (zerop i); [ subst i | reflexivity ].
             rewrite Nat.mod_0_l in H₁; auto.
             exfalso; revert H₁; apply Nat.lt_irrefl.

            erewrite nth_γ_n; eauto ; simpl.
            rewrite Hαkb; simpl.
            rewrite Qnum_inv_Qnat_sub; auto.
            rewrite Qden_inv_Qnat_sub; auto.
            rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
            rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
            do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
            apply Z.mul_cancel_r; auto.
            symmetry.
            rewrite Z.mul_shuffle0.
            rewrite Zposnat2Znat; auto.
            eapply αj_m_eq_p_r; eauto .
            eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁); eauto .
             eapply q_eq_1_any_r with (ns := ns₁) (αk := αk₁); eauto .
             rewrite Hr₁; assumption.

             intros i.
             pose proof (Hri (S i)%nat) as H; simpl in H.
             rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

             simpl.
             rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

           rewrite <- Zposnat2Znat; auto.
           apply Pos2Z_ne_0.

          eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁); eauto .
           eapply q_eq_1_any_r with (ns := ns₁) (αk := αk₁); eauto .
           rewrite Hr₁; assumption.

           intros i.
           pose proof (Hri (S i)%nat) as H; simpl in H.
           rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

           simpl.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

         apply Pos2Z_ne_0.

        assert (1 ≤ S b)%nat as H by fast_omega .
        apply Hpsi in H; simpl in H.
        rewrite <- Hc₁, <- Hpol₂ in H.
        rename H into Hps₂.
        remember Hns₂ as H; clear HeqH.
        eapply r_n_next_ns with (pol := pol₁) in H; eauto .
         destruct H as (αj₂, (αk₂, H)).
         destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
         rewrite Nat.add_1_r; simpl.
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
         remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
         remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
         remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
         rewrite Nat.add_comm in Hpolb₂; simpl in Hpolb₂.
         rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₂.
         rewrite <- Hpolb₂.
         remember (nth_ns b pol₃ ns₃) as nsb₂ eqn:Hnsb₂ .
         remember Hns₃ as H; clear HeqH.
         eapply nth_ns_n with (c := c₂) in H; eauto .
         rewrite <- Hnsb₂ in H.
         erewrite nth_pol_n with (c₁ := c₂) in H; eauto .
         rewrite <- Hpolb₂ in H.
         rename H into Hbns₂.
         remember Hbns₂ as H; clear HeqH.
         erewrite <- nth_pol_n with (c₁ := c₂) in Hpolb₂; eauto .
         eapply r_n_next_ns in H; eauto .
          Focus 2.
          eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁); eauto .
           eapply q_eq_1_any_r with (ns := ns₁) (αk := αk₁); eauto .
           rewrite Hr₁; assumption.

           intros i.
           clear H.
           pose proof (Hri (S i)%nat) as H; simpl in H.
           rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

           simpl.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

          destruct H as (αjb₂, (αkb₂, H)).
          destruct H as (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂))).
          unfold root_tail_from_cγ_list; simpl.
          rewrite Hinib, Hfinb, Hinib₂, Hfinb₂; simpl.
          rewrite Hαkb, Hαkb₂; simpl.
          rewrite Qnum_inv_Qnat_sub; auto.
          rewrite Qden_inv_Qnat_sub; auto.
          rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
          rewrite Z.add_0_r, Z.mul_1_r.
          rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
          do 2 rewrite Pos2Z.inj_mul.
          rewrite Z.div_mul_cancel_r; auto.
           rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
           do 2 rewrite Pos2Z.inj_mul.
           rewrite Z.div_mul_cancel_r; auto.
            erewrite αj_m_eq_p_r; eauto .
             erewrite αj_m_eq_p_r with (ns₁ := nsb₂) (pol₁ := polb₂); eauto .
              rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
              rewrite <- Z.mul_assoc, Z.div_mul.
               rewrite Z.mul_shuffle0.
               rewrite <- Z.mul_assoc, Z.div_mul.
                unfold ps_add, ps_mul; simpl.
                unfold cm; simpl.
                rewrite fold_series_const.
                unfold ps_terms_add; simpl.
                rewrite fold_series_const.
                unfold ps_ordnum_add; simpl.
                erewrite nth_γ_n; eauto ; simpl.
                rewrite Hαkb; simpl.
                erewrite Qnum_inv_Qnat_sub; eauto .
                erewrite Qden_inv_Qnat_sub; eauto ; simpl.
                rewrite Nat.sub_0_r.
                rewrite Z.mul_1_r.
                rewrite Z.add_0_r.
                remember (Qden αjb * Qden αkb)%positive as dd.
                remember (Qnum αjb * ' Qden αkb)%Z as nd.
                remember (p_of_m m₁ (γ nsb₂)) as pb₂ eqn:Hpb₂ .
                remember (Pos.of_nat r) as rq eqn:Hrq .
                rewrite series_stretch_const.
                rewrite series_mul_1_l.
                do 2 rewrite Z2Nat_sub_min.
                rewrite Z.mul_add_distr_r.
                rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
                rewrite Z.sub_add_distr, Z.sub_diag; simpl.
                rewrite Z.add_simpl_l.
                rewrite Z.min_l.
                 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
                 unfold adjust_series.
                 rewrite series_stretch_const.
                 rewrite <- series_stretch_stretch.
bbb.
                 rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
                 unfold adjust_ps; simpl.
                 rewrite series_shift_0.
                 rewrite Z.sub_0_r.
bbb.
  continue with root_tail_from_0 around line 2633
*)

(*
Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n,
    (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b n pol₁ ns₁ +
       ps_monom 1%K (γ_sum b n pol₁ ns₁) *
       root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
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
bbb.
  rewrite root_tail_from_0; eauto .
*)

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
 pose proof (exists_or_not_forall (multiplicity_decreases pol ns)) as H.
 destruct H as [Hn| Hn].
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
        erewrite nth_c_root; eauto .

        3: eauto .

        Focus 2.
        eapply List_hd_in.
         subst nssi.
         simpl.
         eapply nth_ns_n; eauto .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          symmetry.
          eapply nth_pol_n; eauto .
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
         erewrite <- nth_pol_n; eauto .
         erewrite <- nth_c_root; eauto .
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
