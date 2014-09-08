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
eapply hd_newton_segments₉ in H; eauto .
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

(*
Theorem k_le_pol_degree : ∀ pol ns k αk,
  ns ∈ newton_segments pol
  → fin_pt ns = (Qnat k, αk)
  → (k ≤ degree (ps_zerop _) pol)%nat.
Proof.
intros pol ns k αk Hns Hfin.
bbb.
*)

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
  → j₁ = 0%nat ∧ r₁ ≤ k₁ ∧ k₁ ≤ r ∧ αj₁ > 0 ∧ αk₁ >= 0.
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
           rewrite H₂; reflexivity.

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
            apply Nat.lt_le_incl; auto.

            apply IHpts₂; auto.
            eapply Sorted_minus_2nd; eauto .
            intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

          destruct pts₁ as [| pt₁]; [ contradiction | idtac ].
          simpl in Hpts.
          injection Hpts; clear Hpts; intros Hpts H₁.
          subst pt₁.
          eapply k_le_r; eauto .
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

Theorem yyy : ∀ pol ns r n,
  ns ∈ newton_segments pol
  → nth_r 0 pol ns = r
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ n → r ≤ nth_r i pol ns)
  → (∀ i, i ≤ n → r = nth_r i pol ns).
Proof.
intros pol ns r n Hns Hr₀ Hnz Hri i Hin.
bbb.
remember Hin as H; clear HeqH.
apply Hri in H.
apply Nat.le_antisymm; auto.
clear H.
revert pol ns r n Hns Hr₀ Hnz Hri Hin.
induction i; intros.
 rewrite <- Hr₀; reflexivity.

 remember Hin as H; clear HeqH.
 apply Hri in H.
 simpl in H; simpl.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 eapply IHi; eauto .
  Focus 2.
  apply Nat.le_antisymm.
   Focus 2.
   clear H.
   destruct n.
    exfalso; revert Hin; apply Nat.nle_succ_0.

    assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
    apply Hri in H.
    simpl in H.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.
bbb.
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
           assert (nth_ns j pol ns ∈ newton_segments (nth_pol j pol ns)) as H.
            Focus 2.
            eapply r₁_le_r₀ in H; eauto .
             do 2 rewrite <- nth_r_add in H.
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

End theorems.
