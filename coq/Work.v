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

Theorem multiplicity_is_pos : ∀ pol ns c r,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → (0 < r)%nat.
Proof.
intros pol ns c r Hns Hc Hr.
remember Hns as H; clear HeqH.
eapply multiplicity_neq_0 in H; auto.
apply Nat.neq_sym, neq_0_lt in H.
rewrite <- Hc, Hr in H.
assumption.
Qed.

Theorem next_has_ns : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → newton_segments pol₁ ≠ [].
Proof.
intros pol ns c pol₁ Hns Hc Hpol₁ Hnz₁.
eapply next_has_root_0_or_newton_segments in Hns; eauto .
simpl in Hns; rewrite <- Hc, <- Hpol₁ in Hns.
destruct Hns; auto; contradiction.
Qed.

(* more general version of r_n_j_0_k_n where r and r₁ are possibly
   different perhaps r_n_j_0_k_n should be rewritten using this theorem *)
Theorem j_0_k_betw_r₀_r₁ : ∀ pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ r r₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r₁
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ r₁ ≤ k₁ ∧ k₁ ≤ r ∧ αj₁ > 0 ∧ αk₁ >= 0 ∧
    ((r₁ < r)%nat ∨ αk₁ == 0).
Proof.
intros pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ r r₁.
intros Hns Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
destruct r.
 symmetry in Hr.
 exfalso; revert Hr.
 apply multiplicity_neq_0; eauto .

 assert (0 < S r)%nat as H by apply Nat.lt_0_succ.
 apply Hpos in H; rename H into Hpos₀.
 remember Hns₁ as Hns₁v; clear HeqHns₁v.
 unfold newton_segments in Hns₁; simpl in Hns₁.
 unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
 unfold ps_poly_nth in Hnneg, Hz, Hpos.
 remember (al pol₁) as la.
 destruct la as [| a₀].
  unfold ps_lap_nth in Hz; simpl in Hz.
  rewrite order_0 in Hz; inversion Hz.

  assert (ns₁ ∈ newton_segments pol₁) as Hns₁i.
   eapply List_hd_in; eauto .
   intros H.
   apply no_newton_segments with (i := S r) in H.
    unfold ps_poly_nth, ps_lap_nth in H; simpl in H.
    rewrite <- Heqla in H; simpl in H.
    rewrite H in Hz.
    rewrite order_0 in Hz; inversion Hz.

    clear H; intros H.
    apply Hps₀.
    apply eq_Qbar_qinf.
    rewrite H.
    rewrite order_0; reflexivity.

    apply Nat.lt_0_succ.

   remember [ini_pt ns₁ … oth_pts ns₁ ++ [fin_pt ns₁]] as pl eqn:Hpl .
   assert (ini_pt ns₁ ∈ pl) as H by (subst pl; left; reflexivity).
   rewrite Hini₁ in H.
   eapply order_in_newton_segment in H; eauto .
   rename H into Hαj₁.
   unfold ps_lap_nth in Hnneg, Hz, Hpos₀.
   unfold points_of_ps_lap in Hns₁.
   unfold points_of_ps_lap_gen in Hns₁.
   simpl in Hns₁.
   remember (order a₀) as v₀.
   symmetry in Heqv₀.
   destruct v₀ as [v₀| ].
    Focus 2.
    unfold ps_poly_nth, ps_lap_nth in Hps₀.
    rewrite <- Heqla in Hps₀; simpl in Hps₀.
    contradiction.

    assert (al (Φq pol₁ ns₁) ≠ [])%lap as Hnz.
     rewrite al_Φq; simpl.
     rewrite Nat.sub_diag; simpl.
     intros H.
     apply lap_eq_cons_nil_inv in H.
     destruct H as (H₁, H₂).
     revert H₁.
     rewrite Hini₁; simpl.
     rewrite nat_num_Qnat.
     eapply ord_coeff_non_zero_in_newt_segm with (ns := ns₁); eauto .
     left; rewrite Hini₁; reflexivity.

     remember Hnz as H; clear HeqH.
     apply multiplicity_lt_length with (acf := acf) (c := c₁) in H.
     rewrite Hr₁ in H.
     rewrite al_Φq in H.
     rewrite <- Hpl in H.
     erewrite length_char_pol with (ns := ns₁) in H; eauto .
      Focus 2.
      rewrite Hini₁; simpl.
      rewrite nat_num_Qnat; reflexivity.

      rewrite Hini₁ in H; simpl in H.
      rewrite nat_num_Qnat in H.
      unfold lower_convex_hull_points in Hns₁.
      simpl in Hns₁.
      remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
      remember (filter_finite_ord R (List.map f (power_list 1 la))) as pts.
      symmetry in Heqpts.
      destruct pts as [| pt].
       rewrite Hns₁ in Hini₁, Hfin₁; simpl in Hini₁, Hfin₁.
       injection Hini₁; intros H₁ H₂.
       injection Hfin₁; intros H₃ H₄.
       rewrite <- Nat2Z.inj_0 in H₂, H₄.
       apply Nat2Z.inj in H₂.
       apply Nat2Z.inj in H₄.
       subst j₁ k₁.
       rewrite Nat.sub_diag in H.
       apply Nat.lt_1_r in H.
       exfalso; revert H; rewrite <- Hr₁.
       apply multiplicity_neq_0; auto.

       simpl in Hns₁.
       rewrite Hns₁ in Hini₁, Hfin₁; simpl in Hini₁, Hfin₁.
       rewrite minimised_slope_beg_pt in Hini₁.
       injection Hini₁; clear Hini₁; intros H₁ H₂.
       subst v₀.
       rewrite <- Nat2Z.inj_0 in H₂.
       apply Nat2Z.inj in H₂.
       subst j₁.
       rewrite Nat.sub_0_r in H.
       split; [ reflexivity | idtac ].
       apply le_S_n in H.
       split; [ assumption | idtac ].
       unfold ps_poly_nth, ps_lap_nth in Hpos₀.
       rewrite <- Heqla in Hpos₀; simpl in Hpos₀.
       rewrite Heqv₀ in Hpos₀.
       apply Qbar.qfin_lt_mono in Hpos₀.
       rewrite and_comm, and_assoc.
       split; [ assumption | idtac ].
       rename H into Hrk.
       remember Hns₁i as H; clear HeqH.
       eapply order_in_newton_segment with (h := k₁) (αh := αk₁) in H; eauto .
        2: rewrite Hpl, <- Hfin₁, Hns₁; simpl; right.
        2: apply List.in_or_app; right; left; reflexivity.

        rename H into Hαk₁.
        pose proof (Hnneg k₁) as H.
        unfold ps_poly_nth, ps_lap_nth in Hαk₁.
        rewrite <- Heqla in Hαk₁.
        rewrite Hαk₁ in H.
        apply Qbar.qfin_le_mono in H.
        rewrite and_assoc.
        split; [ assumption | idtac ].
        rename H into Hnnegk.
        rewrite minimised_slope_beg_pt in Hns₁.
        rewrite Hfin₁ in Hns₁.
        remember (minimise_slope (Qnat 0, αj₁) pt pts) as ms.
        remember Heqms as H; clear HeqH.
        symmetry in H.
        apply end_pt_in in H.
        apply List.in_split in H.
        destruct H as (pts₁, (pts₂, Hpts)).
        simpl in Hz.
        remember (order (List.nth r la 0%ps)) as v.
        unfold Qbar.qeq in Hz.
        destruct v as [v| ]; [ idtac | contradiction ].
        symmetry in Heqv.
        remember Heqpts as H; clear HeqH.
        symmetry in H.
        rewrite Heqf, fold_qpower_list in H.
        eapply in_ppl_in_pts with (h := S r) (hv := v) in H; eauto .
         2: apply le_n_S, Nat.le_0_l.

         2: rewrite Nat_sub_succ_1; assumption.

         rename H into Hsr.
         remember Hns₁i as H; clear HeqH.
         unfold newton_segments in H.
         unfold points_of_ps_polynom in H.
         unfold points_of_ps_lap in H.
         remember (points_of_ps_lap_gen 0 (al pol₁)) as ptsi.
         rename H into Hlch.
         remember Heqptsi as H; clear HeqH.
         apply points_of_polyn_sorted in H.
         rewrite <- Heqla in Heqptsi.
         unfold points_of_ps_lap_gen in Heqptsi.
         unfold qpower_list in Heqptsi.
         rewrite <- Heqf in Heqptsi.
         simpl in Heqptsi.
         remember (f (O, a₀)) as x.
         rewrite Heqf in Heqx.
         unfold pair_rec in Heqx; simpl in Heqx.
         subst x.
         rewrite Heqv₀ in Heqptsi.
         rewrite Heqpts in Heqptsi.
         subst ptsi.
         rename H into Hsort.
         rewrite Hpts in Hsr.
         apply List.in_app_or in Hsr.
         destruct Hsr as [Hsr| Hsr].
          Focus 2.
          rewrite Hpts in Hsort.
          remember Hsort as H; clear HeqH.
          apply Sorted_inv_1 in H.
          simpl in Hsr.
          destruct Hsr as [Hsr| Hsr].
           rewrite Hfin₁ in Hsr.
           injection Hsr; intros H₁ H₂.
           rewrite <- positive_nat_Z in H₂.
           apply Nat2Z.inj in H₂.
           rewrite SuccNat2Pos.id_succ in H₂.
           rewrite H₂; split; [ idtac | reflexivity ].
           rewrite <- H₁ in Hz.
           right; assumption.

           apply Sorted_app in H.
           destruct H as (_, H).
           rewrite Hfin₁ in H.
           revert Hrk Hsr H; clear; intros.
           induction pts₂ as [| pt]; [ contradiction | idtac ].
           destruct Hsr as [Hsr| Hsr].
            subst pt.
            apply Sorted_inv in H.
            destruct H as (_, H).
            apply HdRel_inv in H.
            unfold fst_lt in H; simpl in H.
            apply Qnat_lt in H.
            split; [ idtac | apply Nat.lt_le_incl; auto ].
            left; eapply Nat.le_lt_trans; eauto .

            apply IHpts₂; auto.
            eapply Sorted_minus_2nd; eauto .
            intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

          destruct pts₁ as [| pt₁]; [ contradiction | idtac ].
          simpl in Hpts.
          injection Hpts; clear Hpts; intros Hpts H₁.
          subst pt₁.
          assert (k₁ ≤ S r) as H by (eapply k_le_r; eauto ).
          split; auto.
          destruct (eq_nat_dec r₁ (S r)) as [H₁| H₁].
           move H₁ at top; subst r₁.
           right.
           apply Nat.le_antisymm in H; auto.
           move H at top; subst k₁.
           clear Hrk.
           rewrite <- Hz.
           rewrite Hfin₁ in Hpts.
           apply Sorted_inv_1 in Hsort.
           rewrite Hpts in Hsort.
           rewrite List.app_comm_cons in Hsort.
           remember [pt … pts₁] as pts₃ eqn:Hpts₃ .
           exfalso; revert Hsort Hsr; clear; intros.
           induction pts₃ as [| pt]; [ contradiction | idtac ].
           simpl in Hsr.
           destruct Hsr as [Hsr| Hsr].
            subst pt.
            clear IHpts₃.
            induction pts₃ as [| pt].
             simpl in Hsort.
             apply Sorted_inv in Hsort.
             destruct Hsort as (_, Hrel).
             apply HdRel_inv in Hrel.
             unfold fst_lt in Hrel; simpl in Hrel.
             revert Hrel; apply Qlt_irrefl.

             simpl in Hsort.
             apply Sorted_minus_2nd in Hsort.
              apply IHpts₃; auto.

              intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

            apply IHpts₃; auto.
            simpl in Hsort.
            apply Sorted_inv_1 in Hsort; auto.

           left.
           apply le_neq_lt; auto.
           eapply Nat.le_trans; eauto .
Qed.

Theorem next_ns_r_non_decr : ∀ pol ns c pol₁ ns₁ c₁ r r₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r₁
  → r ≤ r₁
  → ∃ αj₁ αk₁,
    ini_pt ns₁ = (Qnat 0, αj₁) ∧
    fin_pt ns₁ = (Qnat r, αk₁) ∧
    (0 < Qnum αj₁)%Z ∧
    Qnum αk₁ = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ c₁ r r₁.
intros Hns Hc Hpol₁ Hns₁ Hc₁ Hnz₁ Hr Hr₁ Hrle.
remember Hns as H; clear HeqH.
eapply next_has_ns in H; eauto .
rename H into Hns₁nz.
remember Hns₁ as H; clear HeqH.
eapply List_hd_in in H; eauto .
rename H into Hns₁i.
remember Hns₁i as H; clear HeqH.
apply exists_ini_pt_nat in H.
destruct H as (j₁, (αj₁, Hini₂)).
remember Hns₁i as H; clear HeqH.
apply exists_fin_pt_nat in H.
destruct H as (k₁, (αk₁, Hfin₂)).
remember Hns as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ with (c := c) in H; eauto .
destruct H as (Hj₁, (Hrk₁, (Hk₁r, (Hαj₁, (Hαk₁, Hαk₁z))))).
remember Hrle as H; clear HeqH.
eapply Nat.le_trans in H; eauto .
eapply Nat.le_antisymm in H; eauto .
move H at top; subst r₁.
apply Nat.le_antisymm in Hrle; eauto .
move Hrle at top; subst k₁.
destruct Hαk₁z; [ exfalso; revert H; apply Nat.lt_irrefl | idtac ].
subst j₁.
exists αj₁, αk₁.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in H; simpl in H.
rewrite Z.mul_1_r in Hαj₁, H.
split; assumption.
Qed.

(* cf root_tail_split_1st *)
Theorem root_tail_split_1st_any_r : ∀ pol ns c pol₁ ns₁ c₁ m q₀ r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (∀ i, i ≤ 1%nat → nth_r i pol ns = r)
  → (∀ n, r ≤ nth_r n pol ns)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) 0 pol₁ ns₁ =
     root_head 0 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum 0 0 pol₁ ns₁) *
       root_tail (m * q₀) 1 pol₁ ns₁)%ps.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hri Hric H₀.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 assert (0 ≤ 1)%nat as H by apply Nat.le_0_l.
 apply Hri in H; simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 assert (1 ≤ 1)%nat as H by apply Nat.le_refl.
 apply Hri in H; simpl in H; rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
 rename H into Hr₁; move Hr₁ before Hc₁.
 rename H₁ into Hnz₁.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 rewrite <- Heqm₁ in HK₁.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns as H; clear HeqH.
 eapply multiplicity_is_pos in H; eauto .
 rename H into Hrpos.
 remember Hrpos as H; clear HeqH.
 apply Nat2Z.inj_lt in H; simpl in H.
 rename H into Hrpos₁.
 remember Hrpos as H; clear HeqH.
 apply Nat.sub_gt in H.
 rewrite Nat.sub_0_r in H.
 rename H into Hrpos₃.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto .
 simpl in H; rewrite <- Hc, <- Hpol₁ in H.
 destruct H as [| H]; [ contradiction | idtac ].
 rename H into Hns₁nz; move Hns₁nz before HK₁.
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply List_hd_in in Hns₁₁; eauto .
 remember Hns₁₁ as HK₂; clear HeqHK₂.
 eapply next_pol_in_K_1_mq in HK₂; eauto .
 remember Hns₁₁ as H; clear HeqH.
 symmetry in Hr₁.
 eapply q_eq_1_any_r in H; eauto .
 rewrite H in HK₂; clear H.
 rewrite Pos.mul_1_r in HK₂.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 rewrite <- Hc₁.
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [H₁| H₁].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list, ps_monom; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Qnum_inv_Qnat_sub; auto.
  rewrite Qden_inv_Qnat_sub; auto.
  rewrite Z.mul_1_r, Nat.sub_0_r.
  rewrite Z.add_0_r.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
  rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  rewrite fold_series_const.
  erewrite αj_m_eq_p_r; eauto .
  rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
  rewrite <- Z.mul_assoc.
  rewrite <- Zposnat2Znat; simpl; eauto .
  rewrite Z.div_mul; eauto .
  remember (Pos.of_nat r) as pr.
  remember (Qden αj₁ * pr * Qden αk₁)%positive as x.
  rewrite ps_adjust_eq with (n := O) (k := x); symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
  unfold adjust_ps; simpl.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  do 2 rewrite Z.sub_0_r.
  rewrite Pos.mul_comm.
  apply mkps_morphism; auto.
   symmetry.
   rewrite <- series_stretch_const with (k := x); subst x.
   apply stretch_morph; auto.
   constructor; intros i; simpl.
   unfold root_tail_series_from_cγ_list; simpl.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    contradiction.

    destruct i; [ reflexivity | simpl ].
    destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₃| H₃]; auto.
    contradiction.

   subst x.
   rewrite Z.mul_shuffle0.
   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   apply Z.mul_cancel_r; auto.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc; symmetry.
   subst pr.
   rewrite Zposnat2Znat; auto.
   eapply αj_m_eq_p_r; eauto .

  rename H₁ into Hnz₂.
  pose proof (Hric 2%nat) as H.
  remember (S 0) as one in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
  subst one; simpl in H.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
  rename H into Hrle₂.
  remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
  remember (root_multiplicity acf c₂ (Φq pol₂ ns₂)) as r₂ eqn:Hr₂ .
  symmetry in Hr₁, Hr₂.
  remember Hns₁₁ as H; clear HeqH.
  eapply next_ns_r_non_decr in H; eauto .
  destruct H as (αj₂, (αk₂, H)).
  destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).

bbb.
  remember Hns₂i as H; clear HeqH.
  eapply multiplicity_is_pos in H; eauto .
  rewrite <- Hr₂ in H.
  rewrite Nat.add_0_r in H.
  rename H into Hr₂pos.
  unfold root_tail_from_cγ_list; simpl.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  unfold ps_terms_add; simpl.
  unfold ps_ordnum_add; simpl.
  rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
  rewrite Hαk₁; simpl.
  rewrite Qnum_inv_Qnat_sub; auto.
  rewrite Qden_inv_Qnat_sub; auto.
  rewrite Nat.sub_0_r, Z.add_0_r.
  do 2 rewrite Z.mul_1_r.
  remember (Pos.of_nat r) as rq eqn:Hrq .
  remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
  remember (Qden αj₁ * Qden αk₁ * rq)%positive as dd.
  remember (dd * m₁)%positive as x eqn:Hx .
  rewrite Z.mul_opp_l.
  rewrite Z.add_opp_r.
  remember (Qnum αj₂ * ' Qden αk₂ - Qnum αk₂ * ' Qden αj₂)%Z as y eqn:Hy .
  subst x.
  rewrite Z.mul_add_distr_r.
  do 3 rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  rewrite Z.mul_shuffle0.
  rewrite Z.min_l.
   rewrite Z.min_r.
bbb.

  rewrite Z.min_l.
   rewrite Z.min_r.
    Focus 1.
    rewrite Z.sub_diag.
    rewrite Z.mul_add_distr_r.
    rewrite Pos.mul_comm.
    rewrite Pos2Z.inj_mul.
    rewrite Pos2Z.inj_mul.
    rewrite Pos2Z.inj_mul.
    rewrite Z.mul_assoc.
    rewrite Z.add_simpl_l; simpl.
    rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
    unfold adjust_ps; simpl.
    rewrite series_shift_0.
    rewrite Z.sub_0_r.
    apply mkps_morphism.
bbb.
intros pol ns c pol₁ ns₁ c₁ m q₀ r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hri H₀.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

(*
 assert (0 ≤ 2)%nat as H by apply Nat.le_0_l.
 apply Hri in H; simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 assert (1 ≤ 2)%nat as H by apply le_n_S, Nat.le_0_l.
 apply Hri in H; simpl in H; rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
 rename H into Hr₁; move Hr₁ before Hc₁.
 rename H₁ into Hnz₁.
*)
 assert (0 ≤ 1)%nat as H by apply Nat.le_0_l.
 apply Hri in H; simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 assert (1 ≤ 1)%nat as H by apply Nat.le_refl.
 apply Hri in H; simpl in H; rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
 rename H into Hr₁; move Hr₁ before Hc₁.
 rename H₁ into Hnz₁.
(**)
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 rewrite <- Heqm₁ in HK₁.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns as H; clear HeqH.
 eapply multiplicity_is_pos in H; eauto .
 rename H into Hrpos.
 remember Hrpos as H; clear HeqH.
 apply Nat2Z.inj_lt in H; simpl in H.
 rename H into Hrpos₁.
 remember Hrpos as H; clear HeqH.
 apply Nat.sub_gt in H.
 rewrite Nat.sub_0_r in H.
 rename H into Hrpos₃.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto .
 simpl in H; rewrite <- Hc, <- Hpol₁ in H.
 destruct H as [| H]; [ contradiction | idtac ].
 rename H into Hns₁nz; move Hns₁nz before HK₁.
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply List_hd_in in Hns₁₁; eauto .
 remember Hns₁₁ as HK₂; clear HeqHK₂.
 eapply next_pol_in_K_1_mq in HK₂; eauto .
 remember Hns₁₁ as H; clear HeqH.
 symmetry in Hr₁.
 eapply q_eq_1_any_r in H; eauto .
 rewrite H in HK₂; clear H.
 rewrite Pos.mul_1_r in HK₂.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 rewrite <- Hc₁.
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
(*
 assert (2 ≤ 2)%nat as H by reflexivity.
 apply Hri in H.
 remember (S 0) as one in H; simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
 subst one; simpl in H.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
 rename H into Hr₂.
*)
 destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [H₁| H₁].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list, ps_monom; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Qnum_inv_Qnat_sub; auto.
  rewrite Qden_inv_Qnat_sub; auto.
  rewrite Z.mul_1_r, Nat.sub_0_r.
  rewrite Z.add_0_r.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
  rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  rewrite fold_series_const.
  erewrite αj_m_eq_p_r; eauto .
  rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
  rewrite <- Z.mul_assoc.
  rewrite <- Zposnat2Znat; simpl; eauto .
  rewrite Z.div_mul; eauto .
  remember (Pos.of_nat r) as pr.
  remember (Qden αj₁ * pr * Qden αk₁)%positive as x.
  rewrite ps_adjust_eq with (n := O) (k := x); symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
  unfold adjust_ps; simpl.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  do 2 rewrite Z.sub_0_r.
  rewrite Pos.mul_comm.
  apply mkps_morphism; auto.
   symmetry.
   rewrite <- series_stretch_const with (k := x); subst x.
   apply stretch_morph; auto.
   constructor; intros i; simpl.
   unfold root_tail_series_from_cγ_list; simpl.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    contradiction.

    destruct i; [ reflexivity | simpl ].
    destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₃| H₃]; auto.
    contradiction.

   subst x.
   rewrite Z.mul_shuffle0.
   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   apply Z.mul_cancel_r; auto.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc; symmetry.
   subst pr.
   rewrite Zposnat2Znat; auto.
   eapply αj_m_eq_p_r; eauto .

  rename H₁ into Hnz₂.
  remember Hns₁₁ as H; clear HeqH.
  symmetry in Hr₁.
  eapply r_n_next_ns in H; eauto .
  destruct H as (αj₂, (αk₂, H)).
  destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
  unfold root_tail_from_cγ_list; simpl.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  unfold ps_terms_add; simpl.
  unfold ps_ordnum_add; simpl.
  rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
  rewrite Hαk₁, Hαk₂; simpl.
  rewrite Qnum_inv_Qnat_sub; auto.
  rewrite Qden_inv_Qnat_sub; auto.
  rewrite Nat.sub_0_r.
  do 2 rewrite Z.add_0_r, Z.mul_1_r.
  remember (Pos.of_nat r) as rq eqn:Hrq .
  remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
  remember (Qden αj₁ * Qden αk₁ * rq)%positive as dd.
  remember (dd * m₁)%positive as x eqn:Hx.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  subst x.
  do 2 rewrite fold_series_const.
  rewrite series_stretch_const.
  rewrite series_mul_1_l.
  rewrite Z.mul_add_distr_r.
  rewrite Pos.mul_comm.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  remember (nd * ' m₁ * ' dd)%Z as x eqn:Hx.
  remember (Qnum αj₂ * ' m₁ / ' (Qden αj₂ * rq))%Z as y eqn:Hy.
  assert (x <= x + y * ' dd * ' dd)%Z as Hle.
   apply Z.le_sub_le_add_l.
   rewrite Z.sub_diag.
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.mul_nonneg_nonneg; auto.
   subst y.
   destruct (Qnum αj₂); simpl.
    rewrite Z.div_0_l; auto; reflexivity.

    apply Z_div_pos_is_nonneg.

    apply Z.nle_gt in Hαj₂.
    exfalso; apply Hαj₂, Pos2Z.neg_is_nonpos.

   rewrite Z.min_l; auto.
   rewrite Z.min_r; auto.
   clear Hle.
   rewrite Z.sub_diag, Z.add_simpl_l; simpl.
   rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
   unfold adjust_ps; simpl.
   rewrite series_shift_0.
   rewrite Z.sub_0_r.
   apply mkps_morphism.
    remember Hns₁₁ as H; clear HeqH.
    eapply next_has_root_0_or_newton_segments in H; eauto .
    simpl in H; rewrite <- Hc₁, <- Hpol₂ in H.
    destruct H as [| H]; [ contradiction | idtac ].
    rename H into Hns₂nz; move Hns₂nz before Hnz₂.
    remember Hns₂ as H; clear HeqH.
    eapply List_hd_in in H; eauto .
    rename H into Hns₂i; move Hns₂i before ns₂.
    erewrite αj_m_eq_p_r in Hy; eauto; subst rq.
    rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat in Hy; auto.
    rewrite <- Z.mul_assoc in Hy.
    rewrite <- Zposnat2Znat in Hy; auto; simpl in Hy.
    rewrite Z.div_mul in Hy; eauto .
    subst y.
    unfold adjust_series; simpl.
    rewrite series_shift_0.
    rewrite series_stretch_const.
    rewrite <- series_stretch_stretch.
    rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
    remember Hini₂ as H; clear HeqH.
    eapply p_is_pos with (m := m₁) in H; eauto .
    rename H into Hppos.
    remember Hppos as H; clear HeqH.
    apply Z.lt_le_incl in H.
    rename H into Hpnn.
    rewrite Z2Nat.inj_mul; auto; simpl.
    rewrite <- stretch_shift_series_distr.
    rewrite <- series_stretch_const with (k := (dd * dd)%positive).
    rewrite <- series_stretch_add_distr.
    apply stretch_morph; [ reflexivity | idtac ].
    unfold series_add; simpl.
    constructor; intros i; simpl.
    destruct (lt_dec i (Z.to_nat (p_of_m m₁ (γ ns₂)))) as [H₁| H₁].
     destruct (zerop i) as [H₂| H₂].
      subst i; simpl.
      rewrite rng_add_0_r.
      unfold root_tail_series_from_cγ_list; simpl.
      rewrite <- Hc₁.
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
      contradiction.

      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list; simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      erewrite <- next_pow_eq_p in H₁; eauto .
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [| H₃]; auto.
      destruct i; [ exfalso; revert H₂; apply Nat.lt_irrefl | idtac ].
      clear H₂; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [| H₅]; auto.
      remember (next_pow 0 ns₂ m₁) as p₂ eqn:Hp₂ .
      remember (Nat.compare p₂ (S i)) as cmp; symmetry in Heqcmp.
      destruct cmp as [H₄| H₄| H₄]; auto.
       apply nat_compare_eq in Heqcmp.
       rewrite Heqcmp in H₁.
       exfalso; revert H₁; apply Nat.lt_irrefl.

       apply nat_compare_lt in Heqcmp.
       apply Nat.lt_le_incl, Nat.nlt_ge in Heqcmp.
       contradiction.

     clear x Hx.
     apply Nat.nlt_ge in H₁.
     destruct (zerop i) as [H₂| H₂].
      subst i; simpl.
      apply Nat.le_0_r in H₁.
      rewrite <- Z2Nat.inj_0 in H₁.
      apply Z2Nat.inj in H₁; auto; [ idtac | reflexivity ].
      rewrite H₁ in Hppos.
      exfalso; revert Hppos; apply Z.lt_irrefl.

      rewrite rng_add_0_l.
      remember (Z.to_nat (p_of_m m₁ (γ ns₂))) as n₂.
      remember (i - n₂)%nat as id.
      unfold root_tail_series_from_cγ_list.
(*
      rewrite find_coeff_iter_succ.
*)
bbb.
      remember (S id) as x; simpl; subst x.
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₄| H₄].
       contradiction.

       destruct i; [ fast_omega H₂ | clear H₂ H₄ ].
       rewrite <- Hc₁, <- Hpol₂, <- Hns₂; symmetry.
       rewrite <- find_coeff_add with (dp := n₂).
       rewrite Heqid.
       rewrite Nat.add_0_l, Nat.sub_add; auto.
       rewrite <- Heqid; simpl.
       destruct (ps_zerop R (ps_poly_nth 0 pol₂)); auto; clear n.
       erewrite <- next_pow_eq_p in Heqn₂; eauto .
       rewrite <- Heqn₂.
       remember (Nat.compare n₂ (S i)) as cmp eqn:Hcmp .
       symmetry in Hcmp.
       destruct cmp; auto.
       remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
       remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃.
       remember (List.hd phony_ns (newton_segments pol₃)) as ns₃.
       rename Heqpol₃ into Hpol₃.
       rename Heqns₃ into Hns₃.
       remember (next_pow n₂ ns₃ m₁) as p₂₃ eqn:Hp₂₃ .
       apply nat_compare_lt in Hcmp.
       rewrite <- Nat.add_1_r.
       replace n₂ with (n₂ + 0)%nat in Hp₂₃ by fast_omega .
       subst id; symmetry.
       eapply find_coeff_step_any_r₉ with (r := r); eauto .
bbb.
        symmetry in Hr₂.
        eapply q_eq_1_any_r; eauto .

        intros j.

bbb.
                  eapply find_coeff_step_any_r₉ with (r := r); eauto .
                   intros j.
                   pose proof (Hri (S (S j))) as H.
                   remember (S j) as sj; simpl in H.
                   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
                   subst sj; simpl in H.
                   rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                   assumption.

                   apply le_S_n in Hcmp.
                   split; auto.
                   rewrite Hn₂.
                   rewrite <- Z2Nat.inj_0.
                   apply Z2Nat.inj_lt; auto; [ reflexivity | idtac ].
                   apply Z.lt_le_incl; auto.

                   reflexivity.

         revert HH; apply Nat.lt_irrefl.

        intros H; rewrite H in Hns₂.
        rewrite Hns₂ in Hfin₂; simpl in Hfin₂.
        injection Hfin₂; intros H₂ H₃.
        rewrite <- Nat2Z.inj_0 in H₃.
        apply Nat2Z.inj in H₃.
        rewrite H₃ in Hrpos₂.
        apply Hrpos₂; reflexivity.

       rewrite Pos2Z.inj_mul, Z.mul_assoc.
       apply Z.mul_cancel_r; auto.
       rewrite Z.mul_comm.
       rewrite <- Z.divide_div_mul_exact; auto.
        rewrite Z.mul_comm.
        apply Z.div_mul; auto.

        rewrite Heqdd, Heqnd.
        rewrite Pos_mul_shuffle0, Z.mul_shuffle0, Pos2Z.inj_mul.
        apply Z.mul_divide_mono_r.
        rewrite <- Heqm₁ in HK₁.
        erewrite αj_m_eq_p_r; eauto .
        rewrite Pos.mul_comm, Hrq.
        rewrite Pos2Z.inj_mul, Zposnat2Znat; auto.
        exists (p_of_m m₁ (γ ns₁)).
        rewrite Z.mul_assoc; reflexivity.

       rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.

      apply Z.le_sub_le_add_l.
      rewrite Z.sub_diag.
      apply Z.mul_nonneg_nonneg; auto.
      apply Z.mul_nonneg_nonneg; auto.
      destruct (Qnum αj₂); simpl.
       rewrite Z.div_0_l; auto; reflexivity.

       apply Z_div_pos_is_nonneg.

       apply Z.nle_gt in Hαj₂.
       exfalso; apply Hαj₂, Pos2Z.neg_is_nonpos.

    rewrite Hr₁; assumption.

   intros H; rewrite H in Hns₁.
   rewrite Hns₁ in Hfin₁; simpl in Hfin₁.
   injection Hfin₁; intros H₁ H₂.
   rewrite <- Nat2Z.inj_0 in H₂.
   apply Nat2Z.inj in H₂.
   rewrite H₂ in Hrpos₂.
   apply Hrpos₂; reflexivity.
Qed.
*)

(* cf root_tail_from_0 *)
Theorem root_tail_from_0_const_r : ∀ pol ns c pol₁ ns₁ c₁ m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r
  → zerop_1st_n_const_coeff b pol₁ ns₁ = false
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ b r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hr₀ Hr₁ H₀ Hnz.
remember (m * q₀)%positive as m₁.
Abort. (*
bbb.
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
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; eauto ).
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 assert (∀ i : nat, i ≤ b₁ → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
  rewrite Hb₁; apply not_zero_1st_prop; auto.

  clear Hpsi; rename H into Hpsi.
  remember Hns₁ as H; clear HeqH.
  eapply newton_segments_not_nil in H; eauto .
  rename H into Hns₁nz.
  remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
  eapply List_hd_in in Hns₁₁; eauto .
  assert (∀ i, nth_r i pol₁ ns₁ = r) as Hri₁.
   eapply all_same_r_next with (ns := ns); eauto .

   remember Hns₁₁ as H; clear HeqH.
   eapply nth_in_newton_segments_any_r with (n := b₁) in H; eauto .
   rename H into Hbns.
   remember (nth_pol b₁ pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
   remember (nth_ns b₁ pol₁ ns₁) as nsb₂ eqn:Hnsb₂ .
   assert (pol_in_K_1_m polb₂ m₁) as HKb₂.
    eapply nth_pol_in_K_1_m with (ns := ns₁) (n := b₁); eauto .

    pose proof (Hri (S b₁)) as Hrb; simpl in Hrb.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb.
    erewrite nth_r_n in Hrb; eauto .
    erewrite nth_c_n in Hrb; eauto .
    remember Hbns as H; clear HeqH.
    apply exists_ini_pt_nat in H.
    destruct H as (jb, (αjb₂, Hinib₂)).
    remember Hbns as H; clear HeqH.
    apply exists_fin_pt_nat in H.
    destruct H as (kb, (αkb₂, Hfinb₂)).
    remember (ac_root (Φq polb₂ nsb₂)) as cb₂ eqn:Hcb₂ .
    remember (nth_pol (b₁ + 1) pol₁ ns₁) as polb₃ eqn:Hpolb₃ .
    subst b₁.
    simpl in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Hc₁, <- Hpol₂ in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Hns₂ in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Nat.add_1_r, <- Hpolb₃.
    remember Hns₁₁ as H; clear HeqH.
    eapply nth_in_newton_segments_any_r with (n := b) in H; eauto .
    remember (nth_ns b pol₁ ns₁) as nsb₁ eqn:Hnsb₁ .
    remember (nth_pol b pol₁ ns₁) as polb₁ eqn:Hpolb₁ .
    remember (ac_root (Φq polb₁ nsb₁)) as cb₁ eqn:Hcb₁ .
    pose proof (Hri (S b)) as Hrb₁; simpl in Hrb₁.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb₁.
    erewrite nth_r_n in Hrb₁; eauto .
    erewrite nth_c_n in Hrb₁; eauto .
    rewrite <- Hcb₁ in Hrb₁.
    pose proof (Hpsi (S b) (Nat.le_refl (S b))) as Hpsb₂.
    simpl in Hpsb₂.
    rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpsb₂.
    erewrite nth_pol_n with (c := c₁) in Hpsb₂; eauto .
    erewrite nth_ns_n with (c := c₁) in Hnsb₂; eauto .
    assert (pol_in_K_1_m polb₁ m₁) as HKb₁.
     eapply nth_pol_in_K_1_m with (ns := ns₁) (n := b); eauto .

     erewrite <- nth_pol_n with (c := c₁) in Hnsb₂; eauto .
     rewrite <- Hpolb₂ in Hnsb₂.
     erewrite nth_pol_n with (c := c₁) in Hpolb₂; eauto .
     rewrite <- Hpolb₂ in Hpsb₂.
     eapply r_n_j_0_k_n with (ns₁ := nsb₂) in H; eauto .
     erewrite <- nth_ns_n with (c := c₁) in Hnsb₂; eauto .
     destruct H as (Hjb, (Hkb, (Hαjb₂, Hαkb₂))).
     erewrite <- nth_pol_n with (c := c₁) in Hpolb₂; eauto .
     subst jb kb.
     unfold Qlt in Hαjb₂; simpl in Hαjb₂.
     unfold Qeq in Hαkb₂; simpl in Hαkb₂.
     rewrite Z.mul_1_r in Hαjb₂, Hαkb₂.
     remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
     remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
     remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
     pose proof (Hri 2%nat) as Hr₂.
     remember 1%nat as one; simpl in Hr₂.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₂.
     subst one; simpl in Hr₂.
     rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hr₂.
     rewrite <- Hc₂ in Hr₂.
     destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [H₁| H₁].
      rewrite rng_mul_0_r, rng_add_0_r, Nat.add_1_r.
      unfold root_tail_from_cγ_list, ps_monom; simpl.
      rewrite Hinib₂, Hfinb₂; simpl.
      rewrite Hαkb₂; simpl.
      rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite <- Pos2Z.inj_mul.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; simpl; auto.
      erewrite αj_m_eq_p_r; eauto .
      rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
      rewrite <- Z.mul_assoc.
      rewrite <- Zposnat2Znat; simpl; eauto .
      rewrite Z.div_mul; eauto .
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
       subst polb₃.
       rename H₁ into Hpolb₃.
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
         destruct (ps_zerop R (ps_poly_nth 0 polb₂));
          [ contradiction | idtac ].
         symmetry.
         erewrite nth_c_n; eauto .

         simpl.
         rewrite <- Hcb₂.
         rewrite Nat.add_comm in Hpolb₃; simpl in Hpolb₃.
         rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
         destruct d.
          rewrite Hd in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          destruct (ps_zerop R (ps_poly_nth 0 polb₂)); auto.
          erewrite <- nth_pol_n with (c := c₂); eauto .
          remember (nth_pol b pol₃ ns₃) as pol₄ eqn:Hpol₄ .
          remember (List.hd phony_ns (newton_segments pol₄)) as ns₄ eqn:Hns₄ .
          simpl.
          destruct (ps_zerop R (ps_poly_nth 0 pol₄)) as [H₃| H₃]; auto.
          contradiction.

        destruct (zerop i); [ subst i | reflexivity ].
        rewrite Nat.mod_0_l in H₁; auto.
        exfalso; revert H₁; apply Nat.lt_irrefl.

       erewrite nth_γ_n; eauto ; simpl.
       rewrite Hαkb₂; simpl.
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

      assert (1 ≤ S b)%nat as H by fast_omega .
      apply Hpsi in H; simpl in H.
      rewrite <- Hc₁, <- Hpol₂ in H.
      rename H into Hps₂.
      remember Hns₂ as H; clear HeqH.
      eapply r_n_next_ns with (pol := pol₁) in H; eauto .
      destruct H as (αj₂, (αk₂, H)).
      destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
      rewrite Nat.add_1_r; simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂, <- Hc₂, <- Hpol₃, <- Hns₃.
      rewrite Nat.add_comm in Hpolb₃; simpl in Hpolb₃.
      rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
      rewrite <- Hpolb₃.
      remember (nth_ns b pol₃ ns₃) as nsb₃ eqn:Hnsb₃ .
      remember Hns₃ as H; clear HeqH.
      eapply nth_ns_n with (c := c₂) in H; eauto .
      rewrite <- Hnsb₃ in H.
      erewrite <- nth_pol_n with (c := c₂) in H; eauto .
      rewrite <- Hpolb₃ in H.
      rename H into Hbns₂.
      remember Hbns₂ as H; clear HeqH.
      erewrite nth_pol_n with (c := c₂) in Hpolb₃; eauto .
      remember (ac_root (Φq polb₃ nsb₃)) as cb₃ eqn:Hcb₃ .
      remember (S b) as b₁.
      remember (S b₁) as b₂.
      pose proof (Hri (S b₂)) as Hrb₂; simpl in Hrb₂.
      rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb₂.
      subst b₂; simpl in Hrb₂.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hrb₂.
      subst b₁; simpl in Hrb₂.
      rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hrb₂.
      erewrite nth_r_n in Hrb₂; eauto .
      erewrite <- nth_pol_n with (c := c₂) in Hpolb₃; eauto .
      rewrite <- Hpolb₃ in Hrb₂.
      erewrite nth_c_n in Hrb₂; eauto .
      rewrite <- Hcb₃ in Hrb₂.
      erewrite nth_pol_n with (c := c₂) in Hpolb₃; eauto .
      eapply r_n_next_ns in H; eauto .
      destruct H as (αjb₃, (αkb₃, H)).
      destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
      remember Hbns₂ as Hnsb₃nz; clear HeqHnsb₃nz.
      eapply newton_segments_not_nil in Hnsb₃nz; eauto .
      remember Hbns₂ as Hnsb₃₁; clear HeqHnsb₃₁.
      apply List_hd_in in Hnsb₃₁; eauto .
      unfold root_tail_from_cγ_list; simpl.
      rewrite Hinib₂, Hfinb₂, Hinib₃, Hfinb₃; simpl.
      rewrite Hαkb₂, Hαkb₃; simpl.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite Z.add_0_r, Z.mul_1_r.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; simpl; auto.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; auto.
      remember Hns₂ as Hns₂nz; clear HeqHns₂nz.
      eapply newton_segments_not_nil in Hns₂nz; eauto .
      remember Hns₂ as Hns₂₁; clear HeqHns₂₁.
      apply List_hd_in in Hns₂₁; eauto .
      erewrite αj_m_eq_p_r with (ns₁ := nsb₂); eauto .
      assert (pol_in_K_1_m polb₃ m₁) as HKb₃.
       erewrite <- nth_pol_n with (c := c₁) (n := S b) in Hpolb₃; eauto .
        eapply nth_pol_in_K_1_m with (ns := ns₂); eauto .
         replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
         eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .
         symmetry.
         eapply q_eq_1_any_r with (ns := ns₁) (αk := αk₁); eauto .
         rewrite Hr₁; eauto .

         intros i.
         pose proof (Hri₁ (S i)) as H.
         simpl in H.
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
         assumption.

         intros i Hi.
         destruct (eq_nat_dec i (S b)) as [H₂| H₂].
          subst i; simpl.
          rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
          simpl in Hpolb₃.
          rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
          rewrite <- Hpolb₃.
          apply order_fin.
          erewrite order_in_newton_segment; eauto ; [ idtac | left; eauto  ].
          intros H; discriminate H.

          assert (S i ≤ S b) as H by fast_omega Hi H₂.
          apply Hpsi in H; simpl in H.
          rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
          assumption.

        simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

        simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

       erewrite αj_m_eq_p_r with (ns₁ := nsb₃) (pol₁ := polb₃); eauto .
       rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
       rewrite <- Zposnat2Znat; eauto .
       rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
       rewrite Z.mul_shuffle0.
       rewrite <- Z.mul_assoc, Z.div_mul; auto.
       unfold ps_add, ps_mul; simpl.
       unfold cm; simpl.
       rewrite fold_series_const.
       unfold ps_terms_add; simpl.
       rewrite fold_series_const.
       unfold ps_ordnum_add; simpl.
       erewrite nth_γ_n; eauto ; simpl.
       rewrite Hαkb₂; simpl.
       erewrite Qnum_inv_Qnat_sub; eauto .
       erewrite Qden_inv_Qnat_sub; eauto ; simpl.
       rewrite Nat.sub_0_r, Z.mul_1_r, Z.add_0_r.
       remember (p_of_m m₁ (γ nsb₃)) as pb₃ eqn:Hpb₃ .
       remember (Pos.of_nat r) as rq eqn:Hrq .
       remember (Qden αjb₂ * Qden αkb₂ * rq)%positive as dd.
       remember (Qnum αjb₂ * ' Qden αkb₂)%Z as nd.
       assert (0 < Z.to_nat pb₃)%nat as Hpb₃pos.
        subst pb₃.
        unfold p_of_m; simpl.
        rewrite Hinib₃, Hfinb₃; simpl.
        rewrite Hαkb₃; simpl.
        rewrite Qnum_inv_Qnat_sub; auto.
        rewrite Qden_inv_Qnat_sub; auto.
        rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
        do 2 rewrite Pos2Z.inj_mul.
        remember (Qnum αjb₃ * ' Qden αkb₃ * ' m₁)%Z as x.
        rewrite Z.mul_shuffle0 in Heqx.
        rewrite Z.mul_shuffle0; subst x.
        rewrite Z.gcd_mul_mono_r; simpl.
        rewrite Z.div_mul_cancel_r; auto.
         rewrite <- Z2Nat.inj_0.
         apply Z2Nat.inj_lt; auto; [ reflexivity | idtac | idtac ].
          apply Z.div_pos.
           apply Z.mul_nonneg_nonneg; auto.
           apply Z.lt_le_incl; auto.

           remember (Qnum αjb₃ * ' m₁)%Z as x.
           remember (Qden αjb₃ * Pos.of_nat r)%positive as y.
           pose proof (Z.gcd_nonneg x (' y)) as H.
           assert (Z.gcd x (' y) ≠ 0)%Z as HH; [ idtac | omega ].
           intros HH.
           apply Z.gcd_eq_0_r in HH.
           revert HH; apply Pos2Z_ne_0.

          rewrite Z.gcd_comm.
          apply Z_div_gcd_r_pos.
          apply Z.mul_pos_pos; auto.
          apply Pos2Z.is_pos.

         intros H.
         apply Z.gcd_eq_0_r in H.
         revert H; apply Pos2Z_ne_0.

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
         rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
         unfold adjust_ps; simpl.
         rewrite series_shift_0.
         rewrite Z.sub_0_r.
         apply mkps_morphism.
          rewrite <- series_stretch_const with (k := (dd * dd)%positive).
          rewrite <- Z.mul_opp_l.
          do 2 rewrite Z2Nat_inj_mul_pos_r.
          do 2 rewrite <- stretch_shift_series_distr.
          rewrite <- series_stretch_add_distr.
          apply stretch_morph; [ reflexivity | idtac ].
          rewrite Z2Nat_neg_eq_0.
           rewrite series_shift_0.
           unfold series_add; simpl.
           constructor; simpl; intros i.
           rename H₁ into Hpsb₃.
           destruct (zerop i) as [H₁| H₁].
            subst i; simpl.
            destruct (lt_dec 0 (Z.to_nat pb₃)) as [H₁| H₁].
             rewrite rng_add_0_r.
             unfold root_tail_series_from_cγ_list; simpl.
             destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₃| H₃].
              contradiction.

              clear H₃; symmetry.
              erewrite nth_c_n; eauto .

             contradiction.

            rewrite rng_add_0_l.
            destruct (lt_dec i (Z.to_nat pb₃)) as [H₂| H₂].
             unfold root_tail_series_from_cγ_list; simpl.
             rewrite <- Hcb₂, <- Hpolb₃, <- Hbns₂.
             destruct i; [ fast_omega H₁ | clear H₁ ].
             destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [| H₁]; auto.
             simpl.
             destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [| H₃]; auto.
             unfold next_pow at 1; simpl.
             rewrite Hinib₃, Hfinb₃; simpl.
             rewrite Hαkb₃; simpl.
             rewrite Qnum_inv_Qnat_sub; auto.
             rewrite Qden_inv_Qnat_sub; auto.
             rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r.
             rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
             rewrite Pos2Z.inj_mul.
             rewrite Z.div_mul_cancel_r; auto.
             erewrite αj_m_eq_p_r with (pol₁ := polb₃); eauto .
             rewrite Pos2Z.inj_mul.
             rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
             rewrite <- Zposnat2Znat; auto.
             rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
             remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁.
             rename Heqcmp₁ into Hcmp₁.
             symmetry in Hcmp₁.
             destruct cmp₁; auto.
              apply nat_compare_eq in Hcmp₁.
              rewrite Hcmp₁ in H₂.
              exfalso; revert H₂; apply Nat.lt_irrefl.

              apply nat_compare_lt in Hcmp₁.
              exfalso; fast_omega H₂ Hcmp₁.

             apply Nat.nlt_ge in H₂.
             remember (i - Z.to_nat pb₃)%nat as id.
             unfold root_tail_series_from_cγ_list.
             assert (∀ j, nth_r j polb₂ nsb₂ = r) as Hrib₂.
              eapply all_same_r_next with (ns := nsb₁); eauto .
               erewrite <- nth_pol_n with (c := c₁); eauto .

               erewrite <- nth_ns_n with (c := c₁); eauto .
               erewrite <- nth_pol_n with (c := c₁); eauto .

               intros j.
               rewrite Hpolb₁, Hnsb₁.
               pose proof (Hri (S j + b)%nat) as H; simpl in H.
               rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
               rewrite nth_r_add in H; auto.

              rewrite find_coeff_iter_succ with (r := r); auto.
               symmetry.
               pose proof (Hri (S (S (S b)))) as H.
               erewrite nth_r_n in H; eauto .
               remember (S (S b)) as b₂; simpl in H.
               rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
               subst b₂; remember (S b) as b₁; simpl in H.
               rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
               subst b₁; simpl in H.
               rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in H.
               rewrite <- Hnsb₃ in H.
               erewrite nth_c_n in H; eauto .
               erewrite nth_pol_n with (c := c₂) in H; eauto .
               rewrite <- Hpolb₃, <- Hcb₃ in H.
               rename H into Hrb₃.
               symmetry in Hrb₃.
               remember Hnsb₃₁ as H; clear HeqH.
               eapply q_eq_1_any_r in H; eauto .
               rename H into Hqb₃.
               assert (∀ j, nth_r j polb₃ nsb₃ = r) as Hrib₃.
                intros j.
                eapply all_same_r_next with (ns := nsb₂); eauto .

                rewrite find_coeff_iter_succ with (r := r); auto.
                symmetry.
                remember (S i) as si.
                remember (S (S id)) as ssid; simpl.
                rewrite <- Hcb₂, <- Hpolb₃.
                erewrite <- nth_ns_n with (ns := ns₂); eauto .
                rewrite <- Hnsb₃.
                destruct i;
                 [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
                clear H₁.
                destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
                 contradiction.

                 clear H₁.
                 erewrite next_pow_eq_p; eauto .
                 rewrite <- Hpb₃.
                 subst si ssid.
                 remember (S i) as si.
                 remember (S id) as sid; simpl.
                 destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [| H₁]; auto.
                 clear H₁.
                 subst si.
                 remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁
                  eqn:Hcmp₁ .
                 symmetry in Hcmp₁.
                 destruct cmp₁.
                  apply nat_compare_eq in Hcmp₁.
                  rewrite Hcmp₁, Nat.sub_diag in Heqid; subst id; reflexivity.

                  apply nat_compare_lt in Hcmp₁.
                  destruct id; [ exfalso; fast_omega Heqid Hcmp₁ | idtac ].
                  rewrite <- Hcb₃.
                  remember (next_pol polb₃ (β nsb₃) (γ nsb₃) cb₃) as polb₄.
                  remember (List.hd phony_ns (newton_segments polb₄)) as nsb₄.
                  rename Heqpolb₄ into Hpolb₄.
                  rename Heqnsb₄ into Hnsb₄.
                  assert (polb₄ = nth_pol (S (S (S b))) pol₁ ns₁)
                   as Hpolb₄pol₁.
                   rewrite Hpolb₄.
                   symmetry.
                   eapply nth_pol_n with (c := c); eauto .
                    rewrite Hpolb₃.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb.
                    symmetry.
                    eapply nth_pol_n with (c := c); eauto .
                     rewrite Hpolb₂.
                     remember (S b) as sb; simpl.
                     rewrite <- Hc, <- Hpol₁, <- Hns₁.
                     subst sb; simpl.
                     rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

                     rewrite Hnsb₂.
                     remember (S b) as sb; simpl.
                     rewrite <- Hc, <- Hpol₁, <- Hns₁.
                     subst sb; simpl.
                     rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

                    rewrite Hnsb₃.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb; remember (S b) as sb; simpl.
                    rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.
                    subst sb; simpl.
                    rewrite <- Hc₂, <- Hpol₃, <- Hns₃; auto.

                   assert (nsb₄ = nth_ns (S (S (S b))) pol₁ ns₁) as Hnsb₄ns₁.
                    rewrite Hnsb₄; symmetry.
                    eapply nth_ns_n with (c := c); eauto .
                    rewrite Hpolb₄.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb; remember (S b) as sb; simpl.
                    rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.
                    subst sb; simpl.
                    rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                    f_equal.
                     rewrite Hpolb₃.
                     symmetry.
                     eapply nth_pol_n with (c := c₂); eauto .

                     f_equal.
                     rewrite Hnsb₃; auto.

                     rewrite Hnsb₃; auto.

                     rewrite Hcb₃.
                     rewrite Hpolb₃, Hnsb₃.
                     f_equal; f_equal.
                     symmetry.
                     eapply nth_pol_n with (c := c₂); eauto .

                    subst sid.
                    remember (Z.to_nat pb₃) as x.
                    replace x with (0 + x)%nat by reflexivity.
                    rewrite next_pow_add.
                    replace (S i)%nat with (S i - x + x)%nat at 2
                     by fast_omega Hcmp₁.
                    rewrite find_coeff_add.
                    rewrite <- Heqid.
                    symmetry.
                    destruct (ps_zerop R (ps_poly_nth 0 polb₄)) as [H₁| H₁].
                     remember (S id) as sid; simpl.
                     destruct (ps_zerop R (ps_poly_nth 0 polb₄)) as [H₃| H₃].
                      reflexivity.

                      contradiction.

                     apply find_coeff_more_iter with (r := r); auto.
                      eapply List_hd_in; eauto .
                      remember Hnsb₃₁ as H; clear HeqH.
                      eapply next_has_root_0_or_newton_segments in H; eauto .
                      simpl in H.
                      rewrite <- Hcb₃, <- Hpolb₄ in H.
                      destruct H; [ contradiction | auto ].

                      eapply
                       first_n_pol_in_K_1_m_any_r
                        with (pol := polb₃) (n := 1%nat); 
                       eauto .
                       intros j Hj.
                       destruct j; auto.
                       destruct j; [ simpl | exfalso; fast_omega Hj ].
                       rewrite <- Hcb₃, <- Hpolb₄; auto.

                       simpl; rewrite <- Hcb₃; auto.

                      remember (ac_root (Φq polb₄ nsb₄)) as c₄ eqn:Hc₄ .
                      assert (root_multiplicity acf c₄ (Φq polb₄ nsb₄) = r)
                       as Hr₄.
                       rewrite <- Hri₁ with (i := S (S (S b))); symmetry.
                       apply nth_r_n; auto.
                       rewrite Hc₄.
                       symmetry.
                       apply nth_c_n; auto.

                       remember Hnsb₃₁ as H; clear HeqH.
                       eapply r_n_next_ns in H; eauto .
                       destruct H as (αjb₄, (αkb₄, H)).
                       destruct H as (Hinib₄, (Hfinb₄, (Hαjb₄, Hαkb₄))).
                       eapply q_eq_1_any_r with (pol := polb₄); eauto .
                        eapply List_hd_in; eauto .
                        eapply newton_segments_not_nil; eauto .

                        eapply
                         nth_pol_in_K_1_m with (ns := ns₁) (n := (3 + b)%nat);
                         eauto .
                        intros j Hj.
                        destruct (le_dec j (S b)) as [H₃| H₃].
                         apply Hpsi; auto.

                         apply Nat.nle_gt in H₃.
                         destruct (eq_nat_dec j (S (S b))) as [H₄| H₄].
                          subst j.
                          remember (S b) as sb; simpl.
                          rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                          subst sb; simpl.
                          rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                          erewrite nth_pol_n with (c := c₂); eauto .
                          rewrite <- Hpolb₃.
                          auto.

                          destruct (eq_nat_dec j (S (S (S b)))) as [H₅| H₅].
                           2: exfalso; fast_omega Hj H₃ H₄ H₅.

                           subst j.
                           remember (S (S b)) as sb; simpl.
                           rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                           subst sb; remember (S b) as sb; simpl.
                           rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                           subst sb; simpl.
                           remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
                           erewrite
                            nth_pol_n with (poln := polb₃) (c := c₃);
                            eauto .
                            rewrite <- Hpolb₄; auto.

                            erewrite nth_pol_n with (c := c₂); eauto .

                        rewrite Hr₄; auto.

                      intros j.
                      rewrite <- (Hri₁ (j + S (S (S b)))%nat).
                      rewrite nth_r_add; f_equal; auto.

                      fast_omega Heqid Hpb₃pos.

                  apply nat_compare_gt in Hcmp₁.
                  apply Nat.nle_gt in Hcmp₁.
                  contradiction.

               eapply q_eq_1_any_r with (pol := polb₂) (αk := αkb₂); eauto .
               pose proof (Hrib₂ O) as H; simpl in H.
               rewrite <- Hcb₂ in H.
               rewrite H; auto.

           apply Z.opp_le_mono.
           rewrite Z.opp_0.
           rewrite Z.opp_involutive.
           rewrite Hpb₃.
           apply Z.lt_le_incl.
           eapply p_is_pos; eauto .

          rewrite Pos2Z.inj_mul, Z.mul_assoc.
          apply Z.mul_cancel_r; auto.
          subst dd nd.
          rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
          do 2 rewrite Pos2Z.inj_mul.
          rewrite Z.mul_assoc.
          apply Z.mul_cancel_r; auto.
          symmetry.
          rewrite Z.mul_assoc, Z.mul_shuffle0.
          subst rq.
          rewrite Zposnat2Znat; auto.
          eapply αj_m_eq_p_r with (ns₁ := nsb₂); eauto .

          rewrite Pos.mul_comm, Pos.mul_assoc.
          reflexivity.

         apply Z.le_sub_le_add_l.
         rewrite Z.sub_diag.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.mul_nonneg_nonneg; auto.
         rewrite Hpb₃.
         apply Z.lt_le_incl.
         eapply p_is_pos; eauto .
Qed.
*)

Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (1 ≠ 0)%K
  → ∀ n,
    (∀ i, (i ≤ S n)%nat → (nth_r i pol ns = r))
    → zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → (root_tail (m * q₀) b pol₁ ns₁ =
       root_head b n pol₁ ns₁ +
         ps_monom 1%K (γ_sum b n pol₁ ns₁) *
         root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hpol₁ Hns₁ H₀ n Hri Hnz.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri Hnz.
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
Abort. (*
bbb.
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
*)

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
   erewrite <- nth_r_n in Hrn; eauto ; subst rn.
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

         eapply root_when_fin; eauto .

        eapply List_hd_in; eauto .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; eauto .
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

        eapply root_when_fin; eauto .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; eauto .
        erewrite <- nth_c_n; eauto .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; eauto .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; eauto .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        eauto .

        erewrite nth_c_n; eauto .

        symmetry.
        apply nth_r_n; eauto .
        erewrite nth_c_n; eauto .

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

        eapply root_when_fin; eauto .
bbb.
     rewrite root_tail_when_r_r with (n := N) in Hofs; eauto .

bbb.
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
(**)
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
bbb.
     rewrite root_tail_when_r_r with (n := N) in Hofs; eauto .
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

         eapply root_when_fin; eauto .

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

           intros j Hji.
           unfold multiplicity_decreases in Hn.
           rewrite Hr in Hn.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; eauto .
           rename H into Hrj.
           symmetry.
           eapply r_le_eq_incl; eauto .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
            destruct k; eauto .
            apply Nat.succ_le_mono in Hki.
            apply Hz₁ in Hki; simpl.
            rewrite <- Hpol₁, <- Hns₁; auto.

            intros k Hki.
            pose proof (Hn k) as H.
            apply Nat.nlt_ge in H.
            erewrite nth_r_n; eauto .

         apply summation_all_lt in H.
         eapply Qle_lt_trans; eauto .
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
          eapply nth_in_newton_segments_any_r with (ns₁ := ns₁); eauto .
           clear H.
           remember Hns₁ as H; clear HeqH.
           eapply r_n_next_ns in H; eauto .
            destruct H as (αj₁, (αk₁, H)).
            destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
            eapply List_hd_in; eauto .
            intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

            unfold multiplicity_decreases in Hn.
            rewrite <- Hc, Hr in Hn.
            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns).
             symmetry.
             eapply r_le_eq_incl; eauto .
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
              erewrite nth_r_n; eauto .

             simpl; rewrite <- Hc; assumption.

             simpl; rewrite <- Hc, <- Hpol₁; assumption.

             symmetry.
             apply nth_c_n.
              simpl; rewrite <- Hc; assumption.

              simpl; rewrite <- Hc, <- Hpol₁; assumption.

           rename H into Huofs.
           intros i HiN.
           symmetry.
           eapply r_le_eq_incl; eauto .
            eapply List_hd_in; eauto .
            remember Hns as H; clear HeqH.
            eapply next_has_root_0_or_newton_segments in H; eauto .
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
            erewrite <- nth_r_n in H; eauto .
            apply Nat.nlt_ge in H.
            simpl in H.
            rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
            transitivity (S r); auto.
            rewrite <- Hr; simpl.
            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns);
             auto.
             rewrite <- nth_r_n with (n := O) (pol := pol) (ns := ns); auto.
             eapply r₁_le_r₀; eauto .
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
          eapply f₁_orders in H; eauto .
          erewrite <- nth_pol_succ in H; eauto .
           destruct H as (H, _).
           apply List_In_nth with (d := 0%ps) in Ha.
           destruct Ha as (n, Hn₁).
           rewrite Hn₁.
           apply H.

           symmetry.
           apply nth_c_n; eauto .

         eapply order_root_tail_nonneg_any_r; eauto .
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
      erewrite <- nth_r_n in H; eauto .
      apply Nat.nlt_ge in H.
      symmetry.
      eapply r_le_eq_incl; eauto .
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
   erewrite <- nth_r_n in Hrn; eauto ; subst rn.
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

         eapply root_when_fin; eauto .

        eapply List_hd_in; eauto .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; eauto .
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

        eapply root_when_fin; eauto .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; eauto .
        erewrite <- nth_c_n; eauto .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; eauto .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; eauto .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        eauto .

        erewrite nth_c_n; eauto .

        symmetry.
        apply nth_r_n; eauto .
        erewrite nth_c_n; eauto .

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
     rewrite root_tail_when_r_r with (n := N) in Hofs; eauto .
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

         eapply root_when_fin; eauto .

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

           intros j Hji.
           unfold multiplicity_decreases in Hn.
           rewrite Hr in Hn.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; eauto .
           rename H into Hrj.
           symmetry.
           eapply r_le_eq_incl; eauto .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
            destruct k; eauto .
            apply Nat.succ_le_mono in Hki.
            apply Hz₁ in Hki; simpl.
            rewrite <- Hpol₁, <- Hns₁; auto.

            intros k Hki.
            pose proof (Hn k) as H.
            apply Nat.nlt_ge in H.
            erewrite nth_r_n; eauto .
bbb.
           Focus 1.
           eapply yyy; eauto .
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
           eapply Qle_lt_trans; eauto .
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




(* cf find_coeff_step *)
(* rather use find_coeff_more_iter *)
Theorem find_coeff_step_any_r₉ : ∀ pol ns m c pol₁ ns₁ i di p dp np r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (0 < p ≤ i)%nat
  → (di ≤ dp + 1)%nat
  → np = next_pow (p + dp) ns₁ m
  → (find_coeff i np m pol₁ ns₁ (i + di) =
     find_coeff (S i - p) np m pol₁ ns₁ (i + di))%K.
Proof.
intros pol ns m c pol₁ ns₁ i di p dp np r.
intros Hns HK Hq Hc Hpol₁ Hns₁ Hri H₀ (Hp, Hpi) Hdip Hnp.
remember (S i - p)%nat as id.
revert id Heqid.
revert p dp np Hp Hpi Hdip Hnp.
revert pol ns c pol₁ ns₁ di r Hns HK Hq Hc Hpol₁ Hns₁ Hri.
induction i; intros.
 destruct p; [ exfalso; revert Hp; apply Nat.lt_irrefl | idtac ].
 exfalso; revert Hpi; apply Nat.nle_succ_0.

 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 rewrite <- Hc in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 destruct id; [ exfalso; fast_omega Hpi Heqid | simpl ].
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁]; auto.
 unfold next_pow in Hnp; simpl in Hnp.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 rewrite Hini₁, Hfin₁ in Hnp; simpl in Hnp.
 rewrite Hαk₁ in Hnp; simpl in Hnp.
 assert (0 < r)%nat as Hrpos.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀; apply multiplicity_neq_0; auto.

  rewrite Qnum_inv_Qnat_sub in Hnp; auto.
  rewrite Qden_inv_Qnat_sub in Hnp; auto.
  simpl in Hnp.
  rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r in Hnp.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0 in Hnp.
  do 2 rewrite Pos2Z.inj_mul in Hnp.
  rewrite Z.div_mul_cancel_r in Hnp; auto.
   Focus 1.
   remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
   eapply List_hd_in in Hns₁₁; eauto .
    remember (Nat.compare np (S (i + di))) as cmp₁ eqn:Hnpi .
    symmetry in Hnpi.
    destruct cmp₁; auto.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
    remember (next_pow np ns₂ m) as nnp eqn:Hnnp .
    apply nat_compare_lt in Hnpi.
    assert (Z.of_nat r ≠ 0%Z) as Hrpos₂ by fast_omega Hrpos.
    assert (pol_in_K_1_m pol₁ m) as HK₁.
     replace m with (m * 1)%positive by apply Pos.mul_1_r.
     eapply next_pol_in_K_1_mq with (pol := pol); eauto .

     remember Hns₁₁ as H; clear HeqH.
     eapply num_m_den_is_pos with (m := m) in H; eauto .
     rename H into H₂.
     remember (p_of_m m (γ ns₁)) as p₁ eqn:Hp₁ .

      rewrite <- Nat.add_succ_r.
      assert (q_of_m m (γ ns₁) = 1%positive) as Hq₁.
       replace m with (m * 1)%positive by apply Pos.mul_1_r.
       eapply q_eq_1_any_r; eauto ; [ rewrite Pos.mul_1_r; auto | idtac ].
       rewrite Hr₁; auto.

       rewrite Nat.sub_succ_l in Heqid; auto.
       apply eq_add_S in Heqid.
       subst np; rewrite <- Nat.add_assoc in Hnnp.
       assert (0 < Z.to_nat p₁)%nat as Hp₁pos.
        erewrite αj_m_eq_p_r in Hnpi; eauto .
        rewrite Z.mul_shuffle0 in Hnpi.
        rewrite Zposnat2Znat in Hnpi; auto.
        rewrite Z.div_mul_cancel_r in Hnpi; auto.
        rewrite Z.div_mul in Hnpi; auto.
        erewrite αj_m_eq_p_r in H₂; eauto .
        rewrite Z.div_mul in H₂; auto.
        rewrite Z2Nat.inj_mul in H₂.
         rewrite Nat2Z.id in H₂.
         eapply Nat.mul_pos_cancel_r with (m := r); auto.

         rewrite Hp₁.
         unfold p_of_m; simpl.
         rewrite Hini₁, Hfin₁; simpl.
         rewrite Hαk₁; simpl.
         rewrite Qnum_inv_Qnat_sub; auto.
         rewrite Qden_inv_Qnat_sub; auto.
         rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
         apply Z.div_pos.
          apply Z.mul_nonneg_nonneg; auto.
          apply Z.mul_nonneg_nonneg; auto.
          apply Z.lt_le_incl; auto.

          pose proof
           (Z.gcd_nonneg (Qnum αj₁ * ' Qden αk₁ * ' m)
              (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r))).
          assert
           (Z.gcd (Qnum αj₁ * ' Qden αk₁ * ' m)
              (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r)) ≠ 0)%Z.
           2: omega.

           intros HH.
           apply Z.gcd_eq_0_r in HH.
           revert HH; apply Pos2Z_ne_0.

         destruct r.
          exfalso; revert Hr₁.
          apply multiplicity_neq_0; auto.

          apply Nat2Z.is_nonneg.

        eapply IHi with (p := p); eauto .
         intros j.
         pose proof (Hri (S j)) as H; simpl in H.
         rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

        erewrite αj_m_eq_p_r in Hnpi; eauto .
        rewrite Z.mul_shuffle0 in Hnpi.
        rewrite Zposnat2Znat in Hnpi; auto.
        rewrite Z.div_mul_cancel_r in Hnpi; auto.
        rewrite Z.div_mul in Hnpi; auto.
        omega.

        erewrite αj_m_eq_p_r; eauto .
        rewrite Z.mul_shuffle0.
        rewrite Zposnat2Znat; auto.
        rewrite Z.div_mul_cancel_r; auto.
        rewrite Z.div_mul; auto.
        omega.

    intros H.
    rewrite H in Hns₁.
    rewrite Hns₁ in Hfin₁; simpl in Hfin₁.
    injection Hfin₁; intros.
    rewrite <- Nat2Z.inj_0 in H1.
    apply Nat2Z.inj in H1.
    rewrite <- H1 in Hr₀.
    revert Hr₀.
    apply multiplicity_neq_0; auto.

   apply Pos2Z_ne_0.
Qed.

Theorem p_is_pos : ∀ ns αj αk m r,
  ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → (0 < p_of_m m (γ ns))%Z.
Proof.
intros ns αj αk m r Hini Hfin Hαj Hαk Hr.
unfold p_of_m; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; auto.
rewrite Qden_inv_Qnat_sub; auto.
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
rewrite Z.gcd_comm.
apply Z_div_gcd_r_pos.
apply Z.mul_pos_pos; [ idtac | apply Pos2Z.is_pos ].
apply Z.mul_pos_pos; [ auto | apply Pos2Z.is_pos ].
Qed.

Theorem next_pow_eq_p : ∀ pol ns c αj αk m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → (1 ≠ 0)%K
  → next_pow 0 ns m = Z.to_nat (p_of_m m (γ ns)).
Proof.
intros pol ns c αj αk m r Hns Hm Hc Hr Hini Hfin Hαj Hαk Hrp H₀.
unfold next_pow; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; auto.
rewrite Qden_inv_Qnat_sub; auto.
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r.
rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
rewrite Pos2Z.inj_mul.
rewrite Z.div_mul_cancel_r; auto.
erewrite αj_m_eq_p_r with (pol₁ := pol); eauto .
rewrite Pos.mul_comm.
rewrite Pos2Z.inj_mul, Zposnat2Znat; auto.
rewrite <- Z.mul_assoc.
rewrite Z.div_mul; auto.
rewrite <- Zposnat2Znat; auto.
apply Pos2Z_ne_0.
Qed.

Theorem newton_segments_not_nil : ∀ pol ns αk r,
  ns = List.hd phony_ns (newton_segments pol)
  → fin_pt ns = (Qnat r, αk)
  → (0 < r)%nat
  → newton_segments pol ≠ [].
Proof.
intros pol ns αk r Hns Hfin Hr.
intros H; rewrite H in Hns; subst ns.
simpl in Hfin.
injection Hfin; intros H₁ H₂.
rewrite <- Nat2Z.inj_0 in H₂.
apply Nat2Z.inj in H₂.
rewrite H₂ in Hr.
revert Hr; apply Nat.lt_irrefl.
Qed.

(* cf first_n_pol_in_K_1_m *)
Theorem first_n_pol_in_K_1_m_any_r : ∀ pol ns poln m c r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → q_of_m m (γ ns) = 1%positive
  → (1 ≠ 0)%K
  → ∀ n,
    (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
    → (∀ i, i ≤ n → nth_r i pol ns = r)
    → poln = nth_pol n pol ns
    → pol_in_K_1_m poln m.
Proof.
intros pol ns poln m c r Hns HK Hc Hq H₀ n Hnz Hri Hpoln.
revert pol ns poln m c r Hns HK Hc Hq Hri H₀ Hnz Hpoln.
induction n; intros.
 simpl in Hpoln; subst poln; assumption.

 simpl in Hpoln.
 assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
 apply Hri in H; simpl in H; rename H into Hr₀.
 assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
 apply Hri in H; simpl in H; rename H into Hr₁.
 rewrite <- Hc in Hr₀, Hr₁.
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember Hns₁ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₁, (αk₁, Hfin₁)).
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hpoln.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember Hns₁ as H; clear HeqH.
 apply List_hd_in in H.
  rename H into Hns₁₁.
  remember Hns as H; clear HeqH.
  eapply r_n_j_0_k_n with (r := r) in H; try eassumption.
   destruct H as (Hj₁, (Hk₁, (Hαj₁, Hαk₁))).
   subst j₁ k₁; simpl.
   unfold Qlt in Hαj₁; simpl in Hαj₁.
   unfold Qeq in Hαk₁; simpl in Hαk₁.
   rewrite Z.mul_1_r in Hαj₁, Hαk₁.
   assert (pol_in_K_1_m pol₁ m) as HK₁.
    replace m with (m * 1)%positive by apply Pos.mul_1_r.
    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

    eapply IHn with (pol := pol₁) (ns := ns₁); eauto .
     eapply q_eq_1_any_r with (ns := ns₁); eauto .
     rewrite Hr₁; assumption.

     intros i Hin.
     remember Hin as H; clear HeqH.
     apply Nat.succ_le_mono in H.
     apply Hri in H; simpl in H.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
     eauto .

     intros i Hin.
     remember Hin as H; clear HeqH.
     apply Nat.succ_le_mono in H.
     apply Hnz in H; simpl in H.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
     auto.

   clear H.
   assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
   apply Hnz in H; simpl in H.
   rewrite <- Hc, <- Hpol₁ in H.
   auto.

  clear H.
  remember Hns as H; clear HeqH.
  eapply next_has_root_0_or_newton_segments in H; eauto .
  simpl in H.
  rewrite <- Hc, <- Hpol₁ in H.
  destruct H as [H₁| H₁]; auto.
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hnz in H; simpl in H.
  rewrite <- Hc, <- Hpol₁ in H.
  contradiction.
Qed.

Theorem find_coeff_iter_succ : ∀ pol ns pow m i n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → (∀ j, j ≤ n → nth_r j pol ns = r)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → (find_coeff n pow m pol ns i =
     find_coeff (S n) pow m pol ns i)%K.
Proof.
intros pol ns pow m i n r Hns Hm Hq₀ Hri H₀ Hin.
revert pol ns pow m n Hns Hm Hq₀ Hri Hin.
induction i; intros.
 destruct n; [ exfalso; revert Hin; apply Nat.lt_irrefl | idtac ].
 remember (S n) as sn.
 rewrite Heqsn in |- * at 1; simpl.
 destruct (ps_zerop _ (ps_poly_nth 0 pol)) as [| H₁]; auto.
 remember (Nat.compare pow 0) as cmp₁ eqn:Hcmp₁ .
 symmetry in Hcmp₁.
 destruct cmp₁; auto.
 apply nat_compare_lt in Hcmp₁.
 exfalso; revert Hcmp₁; apply Nat.nlt_0_r.

 pose proof (Hri O (Nat.le_0_l n)) as Hr₀; simpl in Hr₀.
 assert (0 < r)%nat as Hrp.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀.
  apply multiplicity_neq_0; auto.

  destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | idtac ].
  remember (S n) as sn.
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop _ (ps_poly_nth 0 pol)) as [| H₁]; auto.
  remember (Nat.compare pow (S i)) as cmp₁ eqn:Hcmp₁ .
  symmetry in Hcmp₁.
  destruct cmp₁; auto.
  assert (1 ≤ sn)%nat as H by (rewrite Heqsn; apply le_n_S, Nat.le_0_l).
  apply Hri in H; simpl in H.
  rename H into Hr₁.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₂| H₂].
   subst sn; simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
    apply lt_S_n in Hin.
    destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | simpl ].
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₄| H₄].
     reflexivity.

     contradiction.

    contradiction.

   remember Hns as H; clear HeqH.
   eapply r_n_next_ns in H; eauto .
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
   remember Hns₁ as H; clear HeqH.
   eapply newton_segments_not_nil in H; eauto .
   rename H into Hns₁nz.
   remember Hns₁ as H; clear HeqH.
   apply List_hd_in in H; auto.
   rename H into Hns₁₁.
   remember Hpol₁ as H; clear HeqH.
   erewrite <- nth_pol_succ with (n := O) in H; simpl; eauto .
   eapply first_n_pol_in_K_1_m_any_r in H; eauto .
    rename H into HK₁.
    remember (next_pow pow ns₁ m) as pow₁ eqn:Hpow₁ .
    symmetry in Hpow₁.
    destruct pow₁.
     replace pow with (0 + pow)%nat in Hpow₁ by auto.
     rewrite next_pow_add in Hpow₁.
     apply Nat.eq_add_0 in Hpow₁.
     destruct Hpow₁ as (Hpow₁, Hpow).
     erewrite next_pow_eq_p with (pol := pol₁) in Hpow₁; eauto .
     assert (0 < p_of_m m (γ ns₁))%Z as H by (eapply p_is_pos; eauto ).
     rewrite <- Z2Nat.inj_0 in Hpow₁.
     apply Z2Nat.inj in Hpow₁; [ idtac | idtac | reflexivity ].
      rewrite Hpow₁ in H.
      exfalso; revert H; apply Z.lt_irrefl.

      apply Z.lt_le_incl; auto.

     remember (S pow₁) as x.
     rewrite <- Nat.add_1_r; subst x.
     rewrite <- Nat.add_1_r.
     do 2 rewrite find_coeff_add.
     subst sn.
     apply lt_S_n in Hin.
     apply IHi; auto.
      remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
      symmetry in Hr₁.
      eapply q_eq_1_any_r; eauto .

      intros j Hjn.
      apply Nat.succ_le_mono in Hjn.
      apply Hri in Hjn; simpl in Hjn.
      rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hjn.
      assumption.

    intros j Hjn.
    destruct j; auto.
    destruct j; [ simpl; rewrite <- Hc, <- Hpol₁; auto | idtac ].
    apply le_S_n in Hjn.
    exfalso; revert Hjn; apply Nat.nle_succ_0.

    intros j Hjn.
    destruct j; auto.
    destruct j; [ simpl; rewrite <- Hc, <- Hpol₁; auto | idtac ].
     rewrite <- Hns₁, Hr₁, Hr₀.
     rewrite Nat.add_0_r; reflexivity.

     apply le_S_n in Hjn.
     exfalso; revert Hjn; apply Nat.nle_succ_0.
Qed.

Theorem find_coeff_more_iter : ∀ pol ns pow m i n n' r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → (∀ j, nth_r j pol ns = r)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → n ≤ n'
  → (find_coeff n pow m pol ns i =
     find_coeff n' pow m pol ns i)%K.
Proof.
intros pol ns pow m i n n' r Hns Hm Hq₀ Hri H₀ Hin Hn'.
remember (n' - n)%nat as d eqn:Hd .
replace n' with (n + d)%nat by fast_omega Hd Hn'.
clear n' Hn' Hd.
rewrite Nat.add_comm.
revert n pow Hin.
revert pol ns Hns Hm Hq₀ Hri.
induction d; intros; [ reflexivity | idtac ].
rewrite find_coeff_iter_succ; auto; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)) as [| H₁]; auto.
remember (Nat.compare pow i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; auto.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (next_pow pow ns₁ m) as pow₁.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₂| H₂].
 rewrite Nat.add_comm.
 destruct n; simpl.
  exfalso; revert Hin; apply Nat.nlt_0_r.

  destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₃| H₃].
   reflexivity.

   contradiction.

 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto .
 simpl in H.
 rewrite <- Hc, <- Hpol₁ in H.
 destruct H as [| H]; [ contradiction | idtac ].
 rename H into Hns₁nz.
 pose proof (Hri O) as Hr₀; simpl in Hr₀.
 rewrite <- Hc in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 apply IHd; auto.
  eapply List_hd_in; eauto .

  eapply first_n_pol_in_K_1_m_any_r with (n := 1%nat); eauto .
   intros j Hj.
   destruct j; auto.
   apply le_S_n in Hj.
   apply Nat.le_0_r in Hj; rewrite Hj; simpl.
   rewrite <- Hc, <- Hpol₁; assumption.

   simpl; rewrite <- Hc; auto.

  remember Hns as H; clear HeqH.
  eapply r_n_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  eapply q_eq_1_any_r with (pol := pol₁); eauto .
   eapply List_hd_in; eauto .

   eapply first_n_pol_in_K_1_m_any_r with (n := 1%nat); eauto .
    intros j Hj.
    destruct j; auto.
    apply le_S_n in Hj.
    apply Nat.le_0_r in Hj; rewrite Hj; simpl.
    rewrite <- Hc, <- Hpol₁; assumption.

    simpl; rewrite <- Hc; auto.

   rewrite Hr₁; auto.

  intros j.
  pose proof (Hri (S j)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.
Qed.

(* cf nth_in_newton_segments *)
Theorem nth_in_newton_segments_any_r : ∀ pol₁ ns₁ c₁ poln nsn n r,
  ns₁ ∈ newton_segments pol₁
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (∀ i, i ≤ n → nth_r i pol₁ ns₁ = r)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → nsn ∈ newton_segments poln.
Proof.
intros pol₁ ns₁ c₁ poln nsn n r Hns₁ Hc₁ Hpsi Hri Hpoln Hnsn.
subst poln nsn.
pose proof (exists_pol_ord R pol₁) as H.
destruct H as (m, Hm).
revert pol₁ ns₁ c₁ m Hns₁ Hm Hc₁ Hpsi Hri.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
assert (1 ≤ S n) as H₁ by apply le_n_S, Nat.le_0_l.
apply Hpsi in H₁; simpl in H₁.
rewrite <- Hc₁, <- Hpol₂ in H₁.
remember (q_of_m m (γ ns₁)) as q₀ eqn:Hq₀ .
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
apply Hri in H; simpl in H; rename H into Hr₀.
assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
apply Hri in H; simpl in H; rename H into Hr₁.
rewrite <- Hc₁ in Hr₀.
rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hr₁.
eapply IHn with (m := (m * q₀)%positive); eauto .
 remember Hns₂ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₂, (αj₂, Hini₂)).
 remember Hns₂ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₂, (αk₂, Hfin₂)).
 eapply hd_newton_segments; eauto .
 remember Hns₁ as H; clear HeqH.
 eapply r_n_j_0_k_n in H; eauto .
 destruct H as (Hj₂, (Hk₂, (Hαj₂, Hαk₂))).
 subst j₂ k₂.
 destruct r; [ idtac | apply Nat.lt_0_succ ].
 exfalso; revert Hr₀; apply multiplicity_neq_0; auto.

 eapply next_pol_in_K_1_mq; eauto .

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hpsi in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
 assumption.

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
 assumption.
Qed.

Theorem not_zero_1st_prop : ∀ pol ns b,
  zerop_1st_n_const_coeff b (nth_pol 1 pol ns) (nth_ns 1 pol ns) = false
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → (∀ i, i ≤ S b → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps).
Proof.
intros pol ns b Hpsi Hnz.
apply zerop_1st_n_const_coeff_false_iff.
rewrite zerop_1st_n_const_coeff_succ.
rewrite Hpsi, Bool.orb_false_r; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
contradiction.
Qed.

Theorem all_same_r_next : ∀ pol ns c pol₁ ns₁ r,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i : nat, nth_r i pol ns = r)
  → (∀ i : nat, nth_r i pol₁ ns₁ = r).
Proof.
intros pol ns c pol₁ ns₁ r Hc Hpol₁ Hns₁ Hri i.
pose proof (Hri (S i)) as H; simpl in H.
rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
assumption.
Qed.

Theorem nth_pol_in_K_1_m : ∀ pol ns c αj αk poln m n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (∀ i : nat, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → poln = nth_pol n pol ns
  → pol_in_K_1_m poln m.
Proof.
intros pol ns c αj αk poln m n r.
intros Hns HK Hc Hini Hfin Hαj Hαk Hri H₀ Hpsi Hpoln.
eapply first_n_pol_in_K_1_m_any_r with (ns := ns) (n := n); eauto .
eapply q_eq_1_any_r with (ns := ns); eauto .
pose proof (Hri 0%nat) as H; simpl in H.
rewrite <- Hc in H; rewrite H.
assumption.
Qed.

Theorem find_coeff_step_any_r : ∀ pol ns m c pol₁ ns₁ i di p dp np r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (0 < p ≤ i)%nat
  → (di ≤ dp + 1)%nat
  → np = next_pow (p + dp) ns₁ m
  → (find_coeff i np m pol₁ ns₁ (S i - p + di) =
     find_coeff (S i - p) np m pol₁ ns₁ (S i - p + di))%K.
Proof.
(* to be cleaned up *)
intros pol ns m c pol₁ ns₁ i di p dp np r.
intros Hns HK Hq Hc Hpol₁ Hns₁ Hri H₀ (Hp, Hpi) Hdip Hnp.
remember (S i - p)%nat as id.
revert id Heqid.
revert p dp np Hp Hpi Hdip Hnp.
revert pol ns c pol₁ ns₁ di r Hns HK Hq Hc Hpol₁ Hns₁ Hri.
induction i; intros.
 destruct p; [ exfalso; revert Hp; apply Nat.lt_irrefl | idtac ].
 exfalso; revert Hpi; apply Nat.nle_succ_0.

 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 rewrite <- Hc in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 destruct id; [ exfalso; fast_omega Hpi Heqid | simpl ].
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁]; auto.
 unfold next_pow in Hnp; simpl in Hnp.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 rewrite Hini₁, Hfin₁ in Hnp; simpl in Hnp.
 rewrite Hαk₁ in Hnp; simpl in Hnp.
 assert (0 < r)%nat as Hrpos.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀; apply multiplicity_neq_0; auto.

  rewrite Qnum_inv_Qnat_sub in Hnp; auto.
  rewrite Qden_inv_Qnat_sub in Hnp; auto.
  simpl in Hnp.
  rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r in Hnp.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0 in Hnp.
  do 2 rewrite Pos2Z.inj_mul in Hnp.
  rewrite Z.div_mul_cancel_r in Hnp; auto.
   remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
   eapply List_hd_in in Hns₁₁; eauto .
    remember (Nat.compare np (S (id + di))) as cmp₁ eqn:Hnpi .
    symmetry in Hnpi.
    destruct cmp₁; auto.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
    remember (next_pow np ns₂ m) as nnp eqn:Hnnp .
    apply nat_compare_lt in Hnpi.
    assert (Z.of_nat r ≠ 0%Z) as Hrpos₂ by fast_omega Hrpos.
    assert (pol_in_K_1_m pol₁ m) as HK₁.
     replace m with (m * 1)%positive by apply Pos.mul_1_r.
     eapply next_pol_in_K_1_mq with (pol := pol); eauto .

     remember Hns₁₁ as H; clear HeqH.
     eapply num_m_den_is_pos with (m := m) in H; eauto .
     rename H into H₂.
     remember (p_of_m m (γ ns₁)) as p₁ eqn:Hp₁ .
     rewrite <- Nat.add_succ_r.
     assert (q_of_m m (γ ns₁) = 1%positive) as Hq₁.
      replace m with (m * 1)%positive by apply Pos.mul_1_r.
      eapply q_eq_1_any_r; eauto ; [ rewrite Pos.mul_1_r; auto | idtac ].
      rewrite Hr₁; auto.

      rewrite Nat.sub_succ_l in Heqid; auto.
      apply eq_add_S in Heqid.
      subst np; rewrite <- Nat.add_assoc in Hnnp.
      assert (0 < Z.to_nat p₁)%nat as Hp₁pos.
       erewrite αj_m_eq_p_r in Hnpi; eauto .
       rewrite Z.mul_shuffle0 in Hnpi.
       rewrite Zposnat2Znat in Hnpi; auto.
       rewrite Z.div_mul_cancel_r in Hnpi; auto.
       rewrite Z.div_mul in Hnpi; auto.
       erewrite αj_m_eq_p_r in H₂; eauto .
       rewrite Z.div_mul in H₂; auto.
       rewrite Z2Nat.inj_mul in H₂.
        rewrite Nat2Z.id in H₂.
        eapply Nat.mul_pos_cancel_r with (m := r); auto.

        rewrite Hp₁.
        unfold p_of_m; simpl.
        rewrite Hini₁, Hfin₁; simpl.
        rewrite Hαk₁; simpl.
        rewrite Qnum_inv_Qnat_sub; auto.
        rewrite Qden_inv_Qnat_sub; auto.
        rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
        apply Z.div_pos.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.lt_le_incl; auto.

         pose proof
          (Z.gcd_nonneg (Qnum αj₁ * ' Qden αk₁ * ' m)
             (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r))).
         assert
          (Z.gcd (Qnum αj₁ * ' Qden αk₁ * ' m)
             (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r)) ≠ 0)%Z.
          2: omega.

          intros HH.
          apply Z.gcd_eq_0_r in HH.
          revert HH; apply Pos2Z_ne_0.

        destruct r.
         exfalso; revert Hr₁.
         apply multiplicity_neq_0; auto.

         apply Nat2Z.is_nonneg.

       eapply IHi with (p := p); eauto .
        intros j.
        pose proof (Hri (S j)) as H; simpl in H.
        rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

        erewrite αj_m_eq_p_r in Hnpi; eauto .
        rewrite Z.mul_shuffle0 in Hnpi.
        rewrite Zposnat2Znat in Hnpi; auto.
        rewrite Z.div_mul_cancel_r in Hnpi; auto.
        rewrite Z.div_mul in Hnpi; auto.
        omega.

        erewrite αj_m_eq_p_r; eauto .
        rewrite Z.mul_shuffle0.
        rewrite Zposnat2Znat; auto.
        rewrite Z.div_mul_cancel_r; auto.
        rewrite Z.div_mul; auto.
        omega.

    intros H.
    rewrite H in Hns₁.
    rewrite Hns₁ in Hfin₁; simpl in Hfin₁.
    injection Hfin₁; intros.
    rewrite <- Nat2Z.inj_0 in H1.
    apply Nat2Z.inj in H1.
    rewrite <- H1 in Hr₀.
    revert Hr₀.
    apply multiplicity_neq_0; auto.

   apply Pos2Z_ne_0.
Qed.

Theorem nth_r_add : ∀ pol ns i j,
  nth_r (i + j) pol ns = nth_r i (nth_pol j pol ns) (nth_ns j pol ns).
Proof.
intros pol ns i j.
revert pol ns j.
induction i; intros.
 simpl.
 apply nth_r_n; auto; symmetry.
 apply nth_c_n; auto.

 rewrite Nat.add_succ_l, <- Nat.add_succ_r; simpl.
 rewrite IHi; simpl.
 f_equal; [ eapply nth_pol_n; eauto | idtac ].
 eapply nth_ns_n; eauto .
Qed.

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

Theorem nth_ns_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_ns (S n) pol ns = nth_ns n pol₁ ns₁.
Proof. intros; subst; reflexivity. Qed.

Theorem nth_c_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_c (S n) pol ns = nth_c n pol₁ ns₁.
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
 eapply hd_newton_segments in Hns₁i; eauto .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; eauto .
 rewrite <- Heqm₁ in H.
 rename H into HK₁; move HK₁ before Hns₁i.
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

   rename H₂ into Hnzn₂; move Hnzn₂ before Hnsn₂.
   remember Hpoln₂ as H; clear HeqH.
   erewrite <- nth_pol_succ2 with (c := c₁) in H; eauto .
   rename H into Hpoln₂₁; move Hpoln₂₁ before Hpoln₂.
   remember Hnsn₂ as H; clear HeqH.
   erewrite <- nth_ns_succ2 with (c := c₁) in H; eauto .
   rename H into Hnsn₂₁; move Hnsn₂₁ before Hnsn₂.
   remember Hpsi as H; clear HeqH.
   apply zerop_1st_n_const_coeff_false_iff in H.
   remember Hnzn₂ as HH; clear HeqHH.
   rewrite Hpoln₂₁ in HH.
   apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
   rewrite zerop_1st_n_const_coeff_false_iff in H.
   clear Hpsi; rename H into Hpsi; move Hpsi after Hri.
   remember Hns as H; clear HeqH.
   eapply r_n_nth_ns with (poln := poln₂) (n := S n) in H; eauto .
   destruct H as (αjn₂, (αkn₂, H)).
   destruct H as (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂))).
   unfold ps_add, ps_mul; simpl.
   unfold cm; simpl.
   unfold ps_terms_add, ps_ordnum_add; simpl.
   unfold root_tail_from_cγ_list; simpl.
   erewrite nth_γ_n; eauto ; simpl.
   rewrite Hinin₁, Hfinn₁, Hinin₂, Hfinn₂; simpl.
   rewrite Hαkn₁, Hαkn₂; simpl.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   do 2 rewrite Z.add_0_r, Z.mul_1_r.
   rewrite Nat.sub_0_r.
   remember (Qnum αjn₁ * ' Qden αkn₁)%Z as nd₁ eqn:Hnd₁ .
   remember (Qden αjn₁ * Qden αkn₁ * Pos.of_nat r)%positive as dd₁ eqn:Hdd₁ .
   remember (Qnum αjn₂ * ' Qden αkn₂)%Z as nd₂ eqn:Hnd₂ .
   remember (Qden αjn₂ * Qden αkn₂ * Pos.of_nat r)%positive as dd₂ eqn:Hdd₂ .
   rewrite Z.mul_add_distr_r.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc.
   remember (nd₁ * ' m₁ * ' dd₁)%Z as x.
   remember (nd₂ * ' m₁ / ' dd₂ * ' dd₁ * ' dd₁)%Z as y.
   assert (x <= x + y)%Z as Hle; subst x y.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.div_pos; [ subst nd₂ | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.lt_le_incl; auto.

    pose proof (Hpsi n (Nat.le_succ_diag_r n)) as H.
    rewrite <- Hpoln₁ in H.
    rename H into Hnzn₁; move Hnzn₁ before Hnsn₁.
    remember Hnsn₂ as H; clear HeqH.
    erewrite nth_ns_n with (c := c₁) in H; eauto .
    erewrite <- nth_pol_n with (c := c₁) in H; eauto .
    rewrite <- Hpoln₂ in H.
    rename H into Hnsn₂h; move Hnsn₂h before Hαkn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply newton_segments_not_nil in H; eauto .
    rename H into Hns₂nz; move Hns₂nz before Hnzn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply List_hd_in in H; eauto .
    rename H into Hnsn₂i; move Hnsn₂i before Hnsn₂h.
    remember Hpoln₂₁ as H; clear HeqH.
    eapply nth_pol_in_K_1_m in H; eauto .
    rename H into HKn₂; move HKn₂ before Hnsn₂i.
    remember (ac_root (Φq poln₂ nsn₂)) as cn₂ eqn:Hcn₂ .
    move Hcn₂ before Hnsn₂.
    pose proof (Hri₁ (S n)) as H.
    erewrite nth_r_n in H; eauto .
    erewrite nth_c_n in H; eauto .
    rewrite <- Hcn₂ in H.
    rename H into Hrn₂; move Hrn₂ after Hcn₂.
    rewrite Z.min_l; auto.
    rewrite Z.min_r; auto.
    rewrite Z.sub_diag; simpl.
    rewrite Z.add_simpl_l.
    unfold adjust_series at 1.
    rewrite series_shift_0, series_stretch_const.
    rewrite series_stretch_const, series_mul_1_l.
    rewrite Pos.mul_comm.
    rewrite ps_adjust_eq with (n := O) (k := (dd₁ * dd₁)%positive).
    unfold adjust_ps; simpl.
    rewrite series_shift_0, Z.sub_0_r, Pos.mul_assoc.
    apply mkps_morphism; auto.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     unfold adjust_series; simpl.
     rewrite <- series_stretch_stretch.
     rewrite Z2Nat_inj_mul_pos_r.
     rewrite <- stretch_shift_series_distr.
     rewrite <- series_stretch_const.
     rewrite <- series_stretch_add_distr.
     apply stretch_morph; auto.
     constructor; simpl; intros i.
     rewrite Hnd₂, Hdd₂.
     rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
     rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     erewrite αj_m_eq_p_r with (pol₁ := poln₂); eauto .
     rewrite <- Zposnat2Znat; eauto .
     rewrite Z.mul_shuffle0, <- Z.mul_assoc.
     rewrite <- Pos2Z.inj_mul.
     rewrite Z.div_mul; auto.
     remember (p_of_m m₁ (γ nsn₂)) as pn₂ eqn:Hpn₂ .
     destruct i.
      simpl.
      destruct (lt_dec 0 (Z.to_nat pn₂)) as [H₁| H₁].
       rewrite rng_add_0_r.
       unfold root_tail_series_from_cγ_list; simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        rewrite Hcn₁; reflexivity.

       exfalso; apply H₁; rewrite Hpn₂.
       rewrite <- Z2Nat.inj_0.
       apply Z2Nat.inj_lt; [ reflexivity | idtac | eapply p_is_pos; eauto ].
       apply Z.lt_le_incl.
       eapply p_is_pos; eauto .

      remember minus as f; simpl; subst f.
      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list.
      remember (S i) as si.
      remember (si - Z.to_nat pn₂)%nat as id eqn:Hid .
      symmetry in Hid.
      destruct (lt_dec si (Z.to_nat pn₂)) as [H₁| H₁].
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        clear H₂.
        rewrite <- Hcn₁.
        erewrite <- nth_pol_n with (c := c₁); eauto .
        rewrite <- Hpoln₂.
        erewrite nth_pol_n with (c := c₁) in Hpoln₂; eauto .
        erewrite <- nth_ns_n with (c := c₁) (n := n); eauto .
        erewrite <- nth_pol_n with (c := c₁) in Hpoln₂; eauto .
        rewrite <- Hnsn₂.
        subst si; simpl.
        destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
         contradiction.

         clear H₂.
         erewrite next_pow_eq_p; eauto .
         rewrite <- Hpn₂.
         remember (Nat.compare (Z.to_nat pn₂) (S i)) as cmp₁ eqn:Hcmp₁ .
         symmetry in Hcmp₁.
         destruct cmp₁; [ idtac | idtac | reflexivity ].
          apply nat_compare_eq in Hcmp₁.
          rewrite Hcmp₁ in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          apply nat_compare_lt in Hcmp₁.
          eapply Nat.lt_trans in H₁; eauto .
          exfalso; revert H₁; apply Nat.lt_irrefl.

       apply Nat.nlt_ge in H₁.
       symmetry in Hrn₁.
       remember Hnsn₁i as H; clear HeqH.
       eapply q_eq_1_any_r in H; eauto .
       rename H into Hqn₁; move Hqn₁ before HKn₁.
       symmetry in Hrn₂.
       remember Hnsn₂i as H; clear HeqH.
       eapply q_eq_1_any_r in H; eauto .
       rename H into Hqn₂; move Hqn₂ before HKn₂.
       assert (∀ j, nth_r j poln₁ nsn₁ = r) as Hrin₁.
        intros j; rewrite Hpoln₁, Hnsn₁, <- nth_r_add; apply Hri₁.

        assert (∀ j, nth_r j poln₂ nsn₂ = r) as Hrin₂.
         intros j; rewrite Hpoln₂₁, Hnsn₂₁, <- nth_r_add; apply Hri₁.

         move Hrin₁ before Hqn₁.
         move Hrin₂ before Hqn₂.
         rewrite find_coeff_iter_succ with (r := r); auto; symmetry.
         rewrite find_coeff_iter_succ with (r := r); auto; symmetry.
         remember (S (S si)) as ssi.
         remember (S id) as sid; simpl.
         rewrite <- Hcn₂.
         remember (next_pol poln₂ (β nsn₂) (γ nsn₂) cn₂) as poln₃ eqn:Hpoln₃ .
         remember (List.hd phony_ns (newton_segments poln₃)) as nsn₃.
         rename Heqnsn₃ into Hnsn₃h.
         destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
          contradiction.

          clear H₂.
          destruct id.
           subst sid.
           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); eauto .
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; eauto .
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁); eauto .
            clear H.
            subst ssi; remember (S i) as si; simpl; subst si.
            rewrite <- Hnsn₂, <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             erewrite next_pow_eq_p; eauto .
             rewrite <- Hpn₂.
             apply Nat.sub_0_le in Hid.
             eapply Nat.le_antisymm in Hid; eauto ; rewrite Hid.
             remember (Nat.compare (S i) (S i)) as cmp₁ eqn:Hcmp₁ .
             symmetry in Hcmp₁.
             destruct cmp₁; auto.
              apply nat_compare_lt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

              apply nat_compare_gt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); eauto .
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; eauto .
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁); eauto .
            clear H.
            rewrite <- Hnsn₂.
            subst ssi; remember (S i) as si; simpl.
            rewrite <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             erewrite next_pow_eq_p; eauto .
             rewrite <- Hpn₂.
             remember (Nat.compare (Z.to_nat pn₂) si) as cmp₁ eqn:Hcmp₁ .
             symmetry in Hcmp₁.
             destruct cmp₁.
              apply nat_compare_eq in Hcmp₁.
              rewrite Hcmp₁, Nat.sub_diag in Hid.
              discriminate Hid.

              apply nat_compare_lt in Hcmp₁.
              replace (Z.to_nat pn₂) with (0 + Z.to_nat pn₂)%nat by auto.
              rewrite next_pow_add.
              apply Nat.add_sub_eq_nz in Hid.
               rewrite Nat.add_comm in Hid.
               rewrite <- Hid.
               rewrite find_coeff_add, Hid.
               subst si sid; symmetry.
               destruct (ps_zerop R (ps_poly_nth 0 poln₃)) as [H₂| H₂].
                remember (S id) as sid; simpl.
                destruct (ps_zerop R (ps_poly_nth 0 poln₃)) as [H₃| H₃].
                 reflexivity.

                 contradiction.

                rename H₂ into Hnzn₃; move Hnzn₃ before Hnsn₃h.
                remember Hnsn₂i as H; clear HeqH.
                eapply next_has_root_0_or_newton_segments in H; eauto .
                simpl in H.
                rewrite <- Hcn₂, <- Hpoln₃ in H.
                destruct H as [| H]; [ contradiction | idtac ].
                rename H into Hns₃nz; move Hns₃nz before Hnzn₃.
                remember Hnsn₃h as H; clear HeqH.
                apply List_hd_in in H; auto.
                rename H into Hnsn₃i.
                move Hnsn₃i before Hnsn₃h.
                remember Hpsi as H; clear HeqH.
                apply zerop_1st_n_const_coeff_false_iff in H.
                remember Hnzn₃ as HH; clear HeqHH.
                rewrite Hpoln₃ in HH.
                erewrite <- nth_pol_n with (c := c₁) in HH; eauto .
                erewrite <- nth_pol_succ2 with (c := c₁) in HH; eauto .
                apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
                rewrite zerop_1st_n_const_coeff_false_iff in H.
                clear Hpsi; rename H into Hpsi; move Hpsi before Hri.
                remember Hns₁i as H; clear HeqH.
                eapply nth_pol_in_K_1_m with (c := c₁) in H; eauto .
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_pol_n with (c := c₁) in H; eauto .
                rewrite <- Hpoln₃ in H.
                rename H into HKn₃; move HKn₃ before Hns₃nz.
                remember Hns as H; clear HeqH.
                eapply r_n_nth_ns in H; eauto .
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_ns_n with (c := c₁) in H; eauto .
                rewrite <- Hnsn₃h in H.
                destruct H as (αjn₃, (αkn₃, H)).
                destruct H as (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃))).
                remember (ac_root (Φq poln₃ nsn₃)) as cn₃ eqn:Hcn₃ .
                move Hcn₃ before HKn₃.
                pose proof (Hri₁ (S (S n))) as H.
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_r_n in H; eauto .
                erewrite nth_c_n in H; eauto .
                erewrite nth_ns_succ in H; eauto .
                erewrite nth_pol_n with (c := c₁) in H; eauto .
                rewrite <- Hpoln₃, <- Hnsn₃h, <- Hcn₃ in H.
                rename H into Hrn₃.
                move Hrn₃ before Hcn₃.
                symmetry in Hrn₃.
                remember Hnsn₃i as H; clear HeqH.
                eapply q_eq_1_any_r in H; eauto .
                rename H into Hqn₃; move Hqn₃ before HKn₃.
                apply find_coeff_more_iter with (r := r); auto.
                 intros j.
                 pose proof (Hrin₂ (S j)) as H; simpl in H.
                 rewrite <- Hcn₂, <- Hpoln₃, <- Hnsn₃h in H; auto.

                 remember Hinin₂ as H; clear HeqH.
                 eapply p_is_pos with (m := m₁) in H; eauto .
                 rewrite <- Hpn₂ in H.
                 apply Z2Nat.inj_lt in H; [ idtac | reflexivity | idtac ].
                  simpl in H.
                  rewrite <- Hid.
                  destruct (Z.to_nat pn₂) as [| pn].
                   exfalso; revert H; apply Nat.lt_irrefl.

                   rewrite Nat.add_succ_r, Nat.add_succ_l.
                   do 2 apply le_n_S.
                   apply Nat.le_add_r.

                  apply Z.lt_le_incl; auto.

               intros H; discriminate H.

              apply nat_compare_gt in Hcmp₁.
              apply Nat.nle_gt in Hcmp₁; contradiction.

     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     apply Z.mul_cancel_r; auto.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto.
      rewrite Z.mul_comm.
      rewrite Z.div_mul; auto.

      rewrite Hnd₁, Hdd₁.
      rewrite Pos_mul_shuffle0, Z.mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      apply Z.mul_divide_cancel_r; auto.
      erewrite αj_m_eq_p_r with (ns₁ := nsn₁); eauto .
      rewrite <- Zposnat2Znat; eauto .
      rewrite Z.mul_shuffle0, <- Z.mul_assoc.
      rewrite <- Pos2Z.inj_mul.
      apply Z.divide_factor_r.
Qed.

Theorem β_lower_bound_r_const : ∀ pol ns pol₁ ns₁ m r η,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → (0 < r)%nat
  → (1 ≠ 0)%K
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → η = 1 # (2 * m * q_of_m m (γ ns))
  → ∀ n nsn,
    zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → (∀ i, i ≤ S n → nth_r i pol ns = r)
    → nsn = nth_ns n pol₁ ns₁
    → η < β nsn.
Proof.
intros pol ns pol₁ ns₁ m r η Hns Hm Hr H₀ Hpol₁ Hns₁ Hη n nsn Hnz Hri Hnsn.
remember Hns as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
eapply r_n_nth_ns in H; eauto .
destruct H as (αjn, (αkn, H)).
destruct H as (Hinin, (Hfinn, (Hαjn, Hαkn))).
unfold β.
rewrite Hinin; simpl.
unfold Qnat; simpl.
rewrite rng_mul_0_l, rng_add_0_r.
remember Hpol₁ as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; eauto .
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
eapply r_n_next_ns in H; eauto .
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember Hns₁ as H; clear HeqH.
eapply hd_newton_segments in H; eauto .
rename H into Hns₁i.
remember HK₁ as H; clear HeqH.
eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁) in H; eauto .
 rename H into HKn.
 remember (nth_pol n pol₁ ns₁) as poln eqn:Hpoln .
 remember Hns₁i as H; clear HeqH.
 eapply nth_in_newton_segments_any_r with (n := n) in H; eauto .
  rename H into Hnsni.
  remember HKn as H; clear HeqH.
  eapply pol_ord_of_ini_pt in H; eauto .
  rewrite Hη, H.
  rewrite <- Pos.mul_assoc.
  remember (m * q_of_m m (γ ns))%positive as m₁ eqn:Hm₁ .
  unfold mh_of_m.
  erewrite <- qden_αj_is_ps_polord; eauto .
  remember (2 * m₁)%positive as m₂.
  unfold Qlt; simpl; subst m₂.
  clear H.
  assert (0 < Qnum αjn * ' m₁ / ' Qden αjn)%Z as H.
   apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
    apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.lt_le_incl; assumption.

    eapply num_m_den_is_pos with (ns := nsn); eauto .

   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   replace (' m₁)%Z with (1 * ' m₁)%Z at 1 by reflexivity.
   apply Z.mul_lt_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
   fast_omega H.

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hri in Hin; simpl in Hin.
  rewrite <- Hpol₁, <- Hns₁ in Hin.
  eauto .

 eapply q_eq_1_any_r with (ns := ns₁); eauto .
 rewrite Hr₁; eauto .

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hpol₁, <- Hns₁ in Hin.
 eauto .
Qed.

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
eapply in_pts_in_ppl with (h := Qnat k) (hv := αk) (def := 0%ps) in H; eauto .
 simpl in H.
 rewrite Nat2Z.id, Nat.sub_0_r in H.
 rewrite <- Hkps in H.
 destruct H as (Hkppl, Hkord).
 remember Hkppl as H; clear HeqH.
 rewrite Hppl in H.
 apply in_power_list_lt in H.
 rewrite nat_num_Qnat in H; auto.

 eapply in_ppl_in_pts; eauto; [ apply Nat.le_0_l | idtac ].
 rewrite Nat.sub_0_r.
 eapply order_in_newton_segment; eauto .
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
eapply j_0_k_betw_r₀_r₁ in H; eauto .
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
eapply IHi; eauto .
 eapply List_hd_in; eauto .
 clear H.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto .
 destruct H as [H₁| H₁].
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hnz in H; contradiction.

  simpl in H₁.
  rewrite <- Hc, <- Hpol₁ in H₁; auto.

 apply Nat.le_antisymm.
  clear H.
  remember Hns as H; clear HeqH.
  eapply r₁_le_r₀ in H; eauto .
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
 eapply Nat.le_trans in Hin; eauto .
 apply Hnz in Hin; simpl in Hin.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; auto.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; eauto .
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
 eapply multiplicity_is_pos in H; eauto .
 rename H into Hrpos; move Hrpos before Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 move H before Hnz₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as H; clear HeqH.
 eapply hd_newton_segments in H; eauto .
 rename H into Hns₁i; move Hns₁i before Hns₁.
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; eauto .
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
 erewrite αj_m_eq_p_r with (ns₁ := ns₁); eauto .
 rewrite Z.mul_shuffle0.
 rewrite <- Zposnat2Znat; auto.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite Z.div_mul; auto.
 unfold Qle; simpl.
 rewrite Z.mul_1_r.
 apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
 apply Z.lt_le_incl.
 eapply p_is_pos; eauto .

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
  eapply multiplicity_is_pos in H; eauto .
  rename H into Hrpos; move Hrpos before Hns₁.
  remember Hns₁ as H; clear HeqH.
  eapply r_n_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  remember Hns₁ as H; clear HeqH.
  eapply hd_newton_segments in H; eauto .
  rename H into Hns₁i; move Hns₁i before Hns₁.
  remember Hns as H; clear HeqH.
  eapply next_pol_in_K_1_mq in H; eauto .
  rewrite <- Hm₁ in H.
  rename H into HK₁; move HK₁ before Hns₁i.
  eapply IHn with (ns := ns₁) (pol := pol₁); eauto .
   symmetry in Hr₁; symmetry.
   eapply q_eq_1_any_r with (pol := pol₁); eauto .

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

End theorems.
