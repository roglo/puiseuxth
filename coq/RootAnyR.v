(* RootAnyR.v *)

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

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem lowest_i_such_that_ri_lt_r₀ : ∀ pol ns r n,
  r = nth_r 0 pol ns
  → (nth_r n pol ns < r)%nat
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ r ≤ nth_r (pred i) pol ns) ∧
    (nth_r i pol ns < r)%nat.
Proof.
intros pol ns r n Hr Hrnr.
subst r.
revert pol ns Hrnr.
induction n; intros.
 exfalso; revert Hrnr; apply Nat.lt_irrefl.

 destruct (lt_dec (nth_r n pol ns) (nth_r 0 pol ns)) as [H| H].
  apply IHn in H.
  destruct H as (i, (Hin, (Hir, Hri))).
  exists i.
  split; [ idtac | split; assumption ].
  apply Nat.le_le_succ_r; assumption.

  apply Nat.nlt_ge in H.
  exists (S n).
  split; [ reflexivity | idtac ].
  split; [ idtac | assumption ].
  right; rewrite Nat.pred_succ; assumption.
Qed.

Theorem multiplicity_lt_length : ∀ cpol c,
  (al cpol ≠ [])%lap
  → (root_multiplicity acf c cpol < length (al cpol))%nat.
Proof.
intros cpol c Hnz.
unfold root_multiplicity.
remember (al cpol) as la; clear Heqla.
remember (length la) as len eqn:H.
assert (length la ≤ len) as Hlen by (apply Nat.eq_le_incl, Nat.eq_sym, H).
clear H.
revert la Hnz Hlen.
induction len; intros.
 apply Nat.le_0_r in Hlen.
 destruct la as [| a]; [ exfalso; apply Hnz; reflexivity | idtac ].
 discriminate Hlen.

 simpl.
 destruct (fld_zerop (lap_mod_deg_1 la c)) as [H₁| H₁].
  apply lt_n_S.
  destruct la as [| a]; [ exfalso; apply Hnz; reflexivity | idtac ].
  simpl in Hlen.
  apply le_S_n in Hlen.
  unfold lap_mod_deg_1 in H₁; simpl in H₁.
  unfold lap_div_deg_1; simpl.
  apply IHlen.
   revert Hnz H₁; clear; intros.
   revert a c Hnz H₁.
   induction la as [| b]; intros.
    simpl in H₁.
    rewrite rng_mul_0_l, rng_add_0_l in H₁.
    exfalso; apply Hnz; rewrite H₁.
    constructor; reflexivity.

    simpl in H₁; simpl.
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H as (H₂, H₃).
    rewrite H₂ in H₁.
    rewrite rng_mul_0_l, rng_add_0_l in H₁.
    revert H₃.
    apply IHla with (a := b); [ | assumption ].
    intros H.
    rewrite H in Hnz.
    apply Hnz; rewrite H₁.
    constructor; reflexivity.

   rewrite length_lap_mod_div_deg_1; assumption.

  apply Nat.lt_0_succ.
Qed.

Theorem k_le_r : ∀ αj₁ αk₁ k₁ r pt pts v ms pts₁ pts₂,
  pts = pts₁ ++ [end_pt ms … pts₂]
  → Sorted fst_lt [(Qnat 0, αj₁); pt … pts]
  → ms = minimise_slope (Qnat 0, αj₁) pt pts
  → end_pt ms = (Qnat k₁, αk₁)
  → v == 0
  → 0 < αj₁
  → 0 <= αk₁
  → (Qnat (S r), v) ∈ [pt … pts₁]
  → k₁ ≤ S r.
Proof.
intros αj₁ αk₁ k₁ r pt pts v ms pts₁ pts₂.
intros Hpts Hsort Heqms Hfin₁ Hz Hpos₀ Hnnegk Hsr.
apply Nat.nlt_ge.
intros Hrk.
assert (slope ms < slope_expr (Qnat (S r), v) (Qnat k₁, αk₁)) as H.
 apply Qnot_le_lt.
 intros H.
 rewrite slope_slope_expr in H; [ | symmetry; eassumption ].
 rewrite <- Hfin₁ in H.
 rewrite Hfin₁ in H; simpl in H.
 unfold slope_expr in H; simpl in H.
 rewrite Hz in H.
 rewrite Q_sub_0_r in H.
 unfold Qle in H; simpl in H.
 rewrite Qnum_inv_Qnat_sub in H; [ | assumption ].
 rewrite Z.mul_1_r in H.
 remember Hrk as Hk₁; clear HeqHk₁.
 apply Nat.lt_trans with (n := O) in Hk₁; [ idtac | apply Nat.lt_0_succ ].
 rewrite Qnum_inv_Qnat_sub in H; [ idtac | assumption ].
 rewrite Z.mul_1_r in H.
 rewrite Qden_inv_Qnat_sub in H; [ idtac | assumption ].
 rewrite Qden_inv_Qnat_sub in H; [ idtac | assumption ].
 rewrite Nat.sub_0_r in H.
 rewrite Z.mul_opp_l in H.
 rewrite Z.add_opp_r in H.
 rewrite Z.mul_comm in H.
 rewrite Pos2Z.inj_mul in H.
 rewrite Pos2Z.inj_mul in H.
 rewrite Z.mul_comm in H.
 rewrite Pos2Z.inj_mul in H.
 rewrite Z.mul_comm in H.
 do 2 rewrite <- Z.mul_assoc in H.
 rewrite Z.mul_comm in H.
 rewrite Z.mul_assoc in H.
 rewrite Z.mul_assoc in H.
 remember (' Qden αj₁ * ' Pos.of_nat k₁ * Qnum αk₁ * ' Qden αk₁)%Z as x.
 rewrite Z.mul_shuffle0 in H.
 subst x.
 apply Z.mul_le_mono_pos_r in H; [ idtac | apply Pos2Z.is_pos ].
 rewrite Z.mul_sub_distr_r in H.
 rewrite Nat2Pos.inj_sub in H; [ idtac | intros HH; discriminate HH ].
 rewrite Pos2Z.inj_sub in H.
  rewrite Z.mul_sub_distr_l in H.
  rewrite <- Z.mul_assoc, Z.mul_comm in H.
  rewrite <- Z.mul_assoc, Z.mul_comm in H.
  apply Z.le_add_le_sub_r in H.
  apply Z.le_add_le_sub_r in H.
  apply Z.nlt_ge in H.
  apply H.
  rewrite <- Z.add_assoc.
  apply Z.lt_sub_lt_add_l.
  rewrite Z.sub_diag.
  apply Z.add_pos_nonneg.
   apply Z.mul_pos_pos.
    apply Z.mul_pos_pos; [ idtac | apply Pos2Z.is_pos ].
    unfold Qlt in Hpos₀; simpl in Hpos₀.
    rewrite Z.mul_1_r in Hpos₀; assumption.

    rewrite <- Pos2Z.inj_sub; [ apply Pos2Z.is_pos | idtac ].
    apply -> Pos.compare_lt_iff.
    rewrite <- Nat2Pos.inj_compare.
     apply nat_compare_lt; assumption.

     intros HH; discriminate HH.

     intros Hk; subst k₁.
     revert Hrk; apply Nat.nlt_0_r.

   apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
   apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
   unfold Qle in Hnnegk; simpl in Hnnegk.
   rewrite Z.mul_1_r in Hnnegk; assumption.

  apply -> Pos.compare_lt_iff.
  rewrite <- Nat2Pos.inj_compare.
   apply nat_compare_lt; assumption.

   intros HH; discriminate HH.

   intros Hk; subst k₁.
   revert Hrk; apply Nat.nlt_0_r.

 rename H into Hsl.
 subst pts.
 remember Heqms as H; clear HeqH.
 symmetry in H.
 destruct Hsr as [Hsr| Hsr].
  subst pt.
  eapply minimise_slope_expr_le in H; try eassumption.
   apply Qle_not_lt in H; contradiction.

   simpl; apply Qnat_lt; assumption.

  eapply min_slope_le with (pt₃ := (Qnat (S r), v)) in H; try eassumption.
   apply Qle_not_lt in H; contradiction.

   apply List.in_or_app; left; assumption.

   simpl; apply Qnat_lt; assumption.
Qed.

Theorem next_has_root_0_or_newton_segments : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = nth_pol 1 pol ns
  → (ps_poly_nth 0 pol₁ = 0)%ps ∨ (newton_segments pol₁ ≠ []).
Proof.
intros pol ns c pol₁ Hns Hc Hpol₁.
remember Hns as H; clear HeqH.
eapply f₁_orders in H; eauto ; simpl.
simpl in Hpol₁.
rewrite <- Hc in Hpol₁.
rewrite <- Hpol₁ in H.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
destruct H as (Hnneg, (Hpos, Hz)).
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 pose proof (Hpos O (Nat.lt_0_succ r)) as H₂.
 destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  left; assumption.

  right.
  apply order_fin in H₁; intros H.
  unfold newton_segments in H.
  unfold points_of_ps_polynom in H.
  unfold points_of_ps_lap in H.
  unfold points_of_ps_lap_gen in H.
  unfold qpower_list in H.
  unfold ps_poly_nth in Hz, H₁.
  remember (al pol₁) as la; clear Heqla.
  unfold ps_lap_nth in Hz, H₁.
  destruct la as [| a].
   simpl in Hz.
   rewrite order_0 in Hz; inversion Hz.

   simpl in Hz, H₁, H.
   remember (order a) as oa eqn:Hoa .
   symmetry in Hoa.
   destruct oa as [oa| ].
    remember 1%nat as pow.
    assert (1 ≤ pow)%nat as Hpow by (subst pow; auto).
    clear Heqpow Hr Hpos a Hoa.
    revert r pow H Hz Hpow.
    induction la as [| a]; intros.
     simpl in Hz.
     rewrite match_id in Hz.
     rewrite order_0 in Hz; inversion Hz.

     simpl in Hz.
     destruct r.
      simpl in H.
      remember (order a) as oa₁ eqn:Hoa .
      symmetry in Hoa.
      destruct oa₁ as [oa₁| ].
       unfold lower_convex_hull_points in H.
       discriminate H.

       inversion Hz.

      simpl in H.
      remember (order a) as oa₁ eqn:Hoa .
      symmetry in Hoa.
      destruct oa₁ as [oa₁| ].
       unfold lower_convex_hull_points in H.
       discriminate H.

       eapply IHla; eauto .

    apply H₁; reflexivity.
Qed.

Theorem next_has_ns : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → newton_segments pol₁ ≠ [].
Proof.
intros pol ns c pol₁ Hns Hc Hpol₁ Hnz₁.
eapply next_has_root_0_or_newton_segments in Hns; eauto.
simpl in Hns; rewrite <- Hc, <- Hpol₁ in Hns.
destruct Hns; auto; contradiction.
Qed.

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
 apply multiplicity_neq_0; try eassumption .

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
   eapply List_hd_in; try eassumption .
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
   eapply order_in_newton_segment in H; try eassumption .
   rename H into Hαj₁.
   unfold ps_lap_nth in Hnneg, Hz, Hpos₀.
   unfold points_of_ps_lap in Hns₁.
   unfold points_of_ps_lap_gen in Hns₁.
   simpl in Hns₁.
   remember (order a₀) as v₀.
   symmetry in Heqv₀.
   destruct v₀ as [v₀| ].
    assert (al (Φq pol₁ ns₁) ≠ [])%lap as Hnz.
     rewrite al_Φq; simpl.
     rewrite Nat.sub_diag; simpl.
     intros H.
     apply lap_eq_cons_nil_inv in H.
     destruct H as (H₁, H₂).
     revert H₁.
     rewrite Hini₁; simpl.
     rewrite nat_num_Qnat.
     eapply ord_coeff_non_zero_in_newt_segm; try eassumption; eauto .
     left; rewrite Hini₁; reflexivity.

     remember Hnz as H; clear HeqH.
     apply multiplicity_lt_length with (c := c₁) in H.
     rewrite Hr₁ in H.
     rewrite al_Φq in H.
     rewrite <- Hpl in H.
     erewrite length_char_pol in H; try eassumption; try reflexivity.
      rewrite Hini₁ in H; simpl in H.
      rewrite nat_num_Qnat in H.
      unfold lower_convex_hull_points in Hns₁.
      simpl in Hns₁.
      remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
      remember (filter_finite_ord (List.map f (power_list 1 la))) as pts.
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
       apply multiplicity_neq_0; assumption.

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
       eapply order_in_newton_segment with (h := k₁) (αh := αk₁) in H; eauto.
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
        eapply in_ppl_in_pts with (h := S r) (hv := v) in H; eauto.
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
          destruct pts₁ as [| pt₁]; [ contradiction | idtac ].
          simpl in Hpts.
          injection Hpts; clear Hpts; intros Hpts H₁.
          subst pt₁.
          assert (k₁ ≤ S r) as H by (eapply k_le_r; try eassumption ).
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
              apply IHpts₃; assumption.

              intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

            apply IHpts₃; auto.
            simpl in Hsort.
            apply Sorted_inv_1 in Hsort; assumption.

           left.
           apply Nat_le_neq_lt; auto.
           eapply Nat.le_trans; try eassumption .

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
            split; [ idtac | apply Nat.lt_le_incl; assumption ].
            left; eapply Nat.le_lt_trans; try eassumption .

            apply IHpts₂; auto.
            eapply Sorted_minus_2nd; try eassumption .
            intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

         apply le_n_S, Nat.le_0_l.

         rewrite Nat_sub_succ_1; assumption.

        rewrite Hpl, <- Hfin₁, Hns₁; simpl; right.
        apply List.in_or_app; right; left; reflexivity.

      rewrite Hini₁; simpl.
      rewrite nat_num_Qnat; reflexivity.

    unfold ps_poly_nth, ps_lap_nth in Hps₀.
    rewrite <- Heqla in Hps₀; simpl in Hps₀.
    contradiction.
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
  → r = r₁ ∧
    ∃ αj₁ αk₁,
    ini_pt ns₁ = (Qnat 0, αj₁) ∧
    fin_pt ns₁ = (Qnat r, αk₁) ∧
    (0 < Qnum αj₁)%Z ∧
    Qnum αk₁ = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ c₁ r r₁.
intros Hns Hc Hpol₁ Hns₁ Hc₁ Hnz₁ Hr Hr₁ Hrle.
remember Hns as H; clear HeqH.
eapply next_has_ns in H; try eassumption .
rename H into Hns₁nz.
remember Hns₁ as H; clear HeqH.
eapply List_hd_in in H; try eassumption .
rename H into Hns₁i.
remember Hns₁i as H; clear HeqH.
apply exists_ini_pt_nat in H.
destruct H as (j₁, (αj₁, Hini₂)).
remember Hns₁i as H; clear HeqH.
apply exists_fin_pt_nat in H.
destruct H as (k₁, (αk₁, Hfin₂)).
remember Hns as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ with (c := c) in H; try eassumption .
destruct H as (Hj₁, (Hrk₁, (Hk₁r, (Hαj₁, (Hαk₁, Hαk₁z))))).
remember Hrle as H; clear HeqH.
eapply Nat.le_trans in H; try eassumption .
eapply Nat.le_antisymm in H; try eassumption .
move H at top; subst r₁.
apply Nat.le_antisymm in Hrle; try eassumption .
move Hrle at top; subst k₁.
split; auto.
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

Theorem r_n_next_ns : ∀ pol ns c pol₁ ns₁ c₁ r,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r
  → ∃ αj αk,
    ini_pt ns₁ = (Qnat 0, αj) ∧
    fin_pt ns₁ = (Qnat r, αk) ∧
    (0 < Qnum αj)%Z ∧
    Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ c₁ r.
intros Hns Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁.
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns₁ as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ in H; eauto .
destruct H as (Hj, (Hrk, (Hkr, (Haj, (Hak, Hrak))))).
apply Nat.le_antisymm in Hrk; auto.
subst j₁ k₁.
exists αj₁, αk₁.
split; auto.
split; auto.
destruct Hrak as [H| H]; [ exfalso; revert H; apply Nat.lt_irrefl | idtac ].
unfold Qlt in Haj.
unfold Qeq in H.
simpl in Haj, H.
rewrite Z.mul_1_r in Haj, H.
split; assumption.
Qed.

Theorem r_n_nth_ns : ∀ pol ns c pol₁ ns₁ c₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → ∀ n poln nsn,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → (∀ i, (i ≤ S n)%nat → (nth_r i pol ns = r))
    → poln = nth_pol n pol₁ ns₁
    → nsn = nth_ns n pol₁ ns₁
    → ∃ αj αk,
      ini_pt nsn = (Qnat 0, αj) ∧
      fin_pt nsn = (Qnat r, αk) ∧
      (0 < Qnum αj)%Z ∧
      Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ c₁ m r Hns Hm Hc Hpol₁ Hns₁ Hc₁.
intros n poln nsn Hpsi Hri Hpoln Hnsn.
destruct r.
 pose proof (Hri O (Nat.le_0_l (S n))) as H.
 simpl in H.
 rewrite <- Hc in H.
 eapply multiplicity_neq_0 in Hns; eauto .
 contradiction.

 remember (S r) as r'.
 assert (0 < r')%nat as Hrnz by (subst r'; apply Nat.lt_0_succ).
 clear r Heqr'; rename r' into r.
 remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
 revert poln nsn Hpsi Hpoln Hnsn.
 revert pol ns c pol₁ ns₁ c₁ m q₀ r Hns Hm Hq₀ Hc Hc₁ Hpol₁ Hns₁ Hri Hrnz.
 induction n; intros.
  pose proof (Hpsi O (Nat.le_0_l O)) as Hnz; simpl in Hnz.
  simpl in Hpoln, Hnsn; subst poln nsn.
  remember Hns as H; clear HeqH.
  eapply r_n_next_ns in H; eauto .
   pose proof (Hri O Nat.le_0_1) as Hr; simpl in Hr.
   rewrite <- Hc in Hr; assumption.

   pose proof (Hri 1%nat (Nat.le_refl 1)) as Hr₁; simpl in Hr₁.
   rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁; assumption.

  pose proof (Hpsi O (Nat.le_0_l (S n))) as H; simpl in H.
  rename H into Hnz₁.
  remember Hns as H; clear HeqH.
  eapply r_n_next_ns with (ns₁ := ns₁) (r := r) in H; try eassumption.
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
   remember Hns₁ as H; clear HeqH.
   eapply List_hd_in in H.
    rename H into Hns₁i.
    simpl in Hpoln, Hnsn.
    rewrite <- Hc₁ in Hpoln, Hnsn.
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
    eapply IHn with (ns := ns₁) (ns₁ := ns₂) (m := (m * q₀)%positive); eauto .
     eapply next_pol_in_K_1_mq with (ns := ns); eassumption .

     intros i Hin.
     apply le_n_S in Hin.
     apply Hri in Hin; simpl in Hin.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
     assumption.

     intros i Hin.
     apply le_n_S in Hin.
     apply Hpsi in Hin; simpl in Hin.
     rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
     assumption.

    clear H.
    intros H; rewrite H in Hns₁; subst ns₁.
    simpl in Hini₁, Hfin₁.
    injection Hfin₁; intros H₁ H₂.
    rewrite <- Nat2Z.inj_0 in H₂.
    apply Nat2Z.inj in H₂.
    subst r.
    revert Hrnz; apply Nat.lt_irrefl.

   assert (0 ≤ S (S n)) as H₁ by apply Nat.le_0_l.
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc in H₁; assumption.

   assert (0 ≤ S n) as H₁ by apply Nat.le_0_l.
   apply Nat.succ_le_mono in H₁.
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H₁; assumption.
Qed.

Theorem nth_newton_segments_nil : ∀ pol ns n,
  ns ∈ newton_segments pol
  → newton_segments (nth_pol n pol ns) = []
  → (∃ i,
     i ≤ n ∧
     (i = O ∨ zerop_1st_n_const_coeff (pred i) pol ns = false) ∧
     zerop_1st_n_const_coeff i pol ns = true).
Proof.
intros pol ns n Hns Hnse.
revert pol ns Hns Hnse.
induction n; intros.
 simpl in Hnse; rewrite Hnse in Hns; contradiction.

 simpl in Hnse.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto .
 destruct H as [H| H].
  simpl in H.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
   exists 0%nat.
   split; [ apply Nat.le_0_l | idtac ].
   split; [ left; reflexivity | simpl ].
   destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.

   exists 1%nat.
   split; [ apply le_n_S, Nat.le_0_l | idtac ].
   split.
    right; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
    contradiction.

    simpl.
    destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
    rewrite <- Hc, <- Hpol₁.
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)); auto.

  simpl in H.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rename H into Hnse₁.
  remember Hnse as H; clear HeqH.
  apply IHn in H; eauto .
   destruct H as (i, (Hin, (Hiz, Hinz))).
   destruct Hiz as [Hiz| Hiz].
    subst i.
    simpl in Hinz.
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)); eauto .
     destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₂| H₂].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.

      exists 1%nat.
      split; [ apply le_n_S, Nat.le_0_l | idtac ].
      split.
       right; simpl.
       destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
       contradiction.

       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
       rewrite <- Hc, <- Hpol₁.
       destruct (ps_zerop K (ps_poly_nth 0 pol₁)); auto.

     discriminate Hinz.

    destruct i.
     rewrite Nat.pred_0 in Hiz.
     rewrite Hinz in Hiz; discriminate Hiz.

     rewrite Nat.pred_succ in Hiz.
     destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.

      exists (S (S i)).
      split; [ apply Nat.succ_le_mono in Hin; assumption | idtac ].
      split.
       right; rewrite Nat.pred_succ.
       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 pol)).
        contradiction.

        rewrite <- Hc, <- Hpol₁, <- Hns₁.
        assumption.

       remember (S i) as si; simpl; subst si.
       destruct (ps_zerop K (ps_poly_nth 0 pol)).
        reflexivity.

        rewrite <- Hc, <- Hpol₁, <- Hns₁.
        assumption.

   eapply List_hd_in; eassumption .
Qed.

Theorem List_seq_split_first : ∀ len start,
  List.seq start (S len) = [start … List.seq (S start) len].
Proof. reflexivity. Qed.

Theorem List_seq_split_last : ∀ len start,
  List.seq start (S len) = List.seq start len ++ [start + len]%nat.
Proof.
intros len start; simpl.
revert start.
induction len; intros; simpl.
 rewrite Nat.add_0_r; reflexivity.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite <- IHlen; reflexivity.
Qed.

Definition nth_coeff (a : α) n i := rng_mul_nat R (comb n i) (a ^ (n - i))%K.

Theorem binomial_expansion : ∀ (a : α) n,
  (lap_power [a; 1%K … []] n =
   List.map (nth_coeff a n) (List.seq 0 (S n)))%lap.
Proof.
intros a n.
induction n.
 simpl.
 unfold nth_coeff; simpl.
 rewrite rng_add_0_l.
 reflexivity.

 remember List.seq as f; simpl; subst f.
 rewrite IHn.
 remember (List.map (nth_coeff a (S n)) (List.seq 0 (S (S n)))) as r.
 rewrite lap_mul_cons_l.
 rewrite lap_mul_1_l.
 rewrite lap_mul_const_l.
 rewrite List.map_map.
 rewrite List_seq_split_first in |- * at 1.
 remember (S n) as s; simpl.
 unfold nth_coeff at 1; simpl.
 rewrite comb_0_r, Nat.sub_0_r, rng_add_0_r.
 rewrite rng_mul_nat_1_l.
 subst s.
 rewrite List_seq_split_last.
 rewrite Nat.add_0_l.
 rewrite <- List.seq_shift.
 rewrite List.map_map.
 rewrite List.map_app; simpl.
 rewrite lap_app_add, lap_add_assoc.
 rewrite List.map_length, List.seq_length.
 unfold nth_coeff at 3.
 rewrite comb_id, Nat.sub_diag; simpl.
 rewrite lap_add_map2.
 unfold nth_coeff; simpl.
 subst r.
 remember (S n) as sn; simpl; subst sn.
 constructor.
  unfold nth_coeff; simpl.
  rewrite rng_add_0_l; reflexivity.

  rewrite List_seq_split_last.
  simpl.
  rewrite List.map_app.
  simpl.
  rewrite lap_app_add.
  rewrite List.map_length.
  rewrite List.seq_length.
  unfold nth_coeff at 2.
  rewrite Nat.sub_diag.
  rewrite comb_id.
  apply lap_add_compat; [ idtac | destruct n; reflexivity ].
  rewrite <- List.seq_shift.
  rewrite List.map_map.
  apply lap_eq_map_ext.
  intros b.
  unfold nth_coeff; simpl.
  rewrite <- rng_mul_nat_mul_swap.
  rewrite rng_mul_nat_add_distr_r.
  rewrite rng_add_comm.
  apply rng_add_compat_l.
  destruct (eq_nat_dec n b) as [H₁| H₁].
   subst b; simpl.
   rewrite comb_lt; auto.

   destruct (le_dec (S b) n) as [H₂| H₂].
    rewrite Nat.sub_succ_r.
    remember (n - b)%nat as nb eqn:Hnb .
    symmetry in Hnb.
    destruct nb; [ simpl | reflexivity ].
    apply Nat.sub_0_le in Hnb.
    apply Nat.nle_gt in H₂; contradiction.

    apply Nat.nle_gt in H₂.
    rewrite comb_lt; auto.
Qed.

Theorem q_eq_1_any_r : ∀ pol ns c αj αk m q r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → r = root_multiplicity acf c (Φq pol ns)
  → ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (1 ≠ 0)%K
  → q = 1%positive.
Proof.
intros pol ns c αj αk m q r Hns Hm Hq Hc Hr Hini Hfin Hαj Hαk H₀.
remember Hr as Hrv; clear HeqHrv.
remember (al (Φq pol ns)) as cpol eqn:Hcpol .
remember Hcpol as H; clear HeqH.
rewrite al_Φq in H.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point pol) pl) as tl eqn:Htl .
rewrite Hini in H.
simpl in H.
rewrite nat_num_Qnat in H; simpl in H.
subst cpol.
rename H into Hcpol.
unfold root_multiplicity in Hr.
rewrite Hcpol in Hr.
erewrite length_char_pol in Hr; eauto .
rewrite <- Hcpol in Hr.
rewrite Nat.sub_0_r in Hr.
remember Hrv as H; clear HeqH.
eapply phi_zq_eq_z_sub_c₁_psy in H; eauto .
unfold eq_poly in H.
rewrite Hcpol in H.
remember quotient_phi_x_sub_c_pow_r as f; simpl in H; subst f.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c r) as Ψ.
eapply Ψ_length in HeqΨ; eauto .
rewrite Nat.sub_0_r, Nat_sub_succ_diag in HeqΨ.
rename H into Hcp.
remember Hns as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk) in H; eauto .
 rewrite <- Hq, Nat.sub_0_r in H.
 remember (mh_of_m m αj (ps_poly_nth 0 pol)) as mj eqn:Hmj .
 eapply pol_ord_of_ini_pt in Hmj; eauto .
 remember (mh_of_m m αk (ps_poly_nth r pol)) as mk eqn:Hmk .
 eapply pol_ord_of_fin_pt in Hmk; eauto .
 destruct H as (_, Hqjr).
 unfold Qeq in Hmk.
 simpl in Hmk.
 rewrite Hαk in Hmk.
 simpl in Hmk.
 symmetry in Hmk.
 apply Z.mul_eq_0_l in Hmk; auto.
 subst mk.
 rewrite Z.sub_0_r in Hqjr.
 rewrite positive_nat_Z in Hqjr.
 remember (p_of_m m (γ ns)) as p eqn:Hp .
 move Hp after Hq.
 remember Hns as H; clear HeqH.
 eapply phi_degree_is_k_sub_j_div_q in H; eauto .
 unfold Φs in H.
 rewrite Nat.sub_0_r, <- Hq in H.
 unfold has_degree in H.
 unfold pseudo_degree in H.
 remember (al (poly_shrink (Pos.to_nat q) (Φq pol ns))) as psh eqn:Hpsh .
 unfold poly_shrink in Hpsh.
 rewrite Hcpol in Hpsh.
 simpl in Hpsh.
 destruct H as (Hshr, (Hdeg, Hpdeg)).
 remember (Pos.to_nat q) as nq eqn:Hnq .
 symmetry in Hnq.
 destruct nq; [ exfalso; revert Hnq; apply Pos2Nat_ne_0 | idtac ].
 destruct nq; [ apply Pos2Nat.inj; assumption | exfalso ].
 unfold poly_shrinkable in Hshr.
 rewrite Hcpol in Hshr.
 assert (1 mod S (S nq) ≠ 0)%nat as H.
  rewrite Nat.mod_1_l; auto.
  apply lt_n_S, Nat.lt_0_succ.

  apply Hshr in H.
  remember (al Ψ) as la eqn:Hla .
  symmetry in Hla.
  destruct la as [| a]; [ discriminate HeqΨ | idtac ].
  destruct la; [ idtac | discriminate HeqΨ ].
  destruct (fld_zerop a) as [H₁| H₁].
   rewrite H₁ in Hcp.
   rewrite lap_eq_0 in Hcp.
   rewrite lap_mul_nil_r in Hcp.
   rewrite Htl, Hpl in Hcp.
   simpl in Hcp.
   rewrite Hini in Hcp; simpl in Hcp.
   apply lap_eq_cons_nil_inv in Hcp.
   rewrite nat_num_Qnat in Hcp.
   destruct Hcp as (Hoj, Hcp).
   revert Hoj.
   eapply ord_coeff_non_zero_in_newt_segm; eauto .
   left; symmetry; eauto .

   rewrite lap_mul_comm in Hcp.
   rewrite binomial_expansion in Hcp.
   rewrite lap_mul_const_l in Hcp.
   rewrite List.map_map in Hcp.
   assert (List.nth 1 (make_char_pol R 0 tl) 0 = 0)%K as HH.
    rewrite H; reflexivity.

    rewrite list_nth_rng_eq in HH; eauto .
    simpl in HH.
    destruct r.
     symmetry in Hrv.
     revert Hrv; apply multiplicity_neq_0; auto.

     simpl in HH.
     unfold nth_coeff in HH.
     simpl in HH.
     rewrite comb_0_r, comb_1_r in HH.
     rewrite Nat.add_1_l in HH.
     rewrite Nat.sub_0_r in HH.
     apply fld_eq_mul_0_r in HH; auto.
     rewrite <- rng_mul_1_l in HH.
     rewrite rng_mul_comm in HH.
     rewrite rng_mul_nat_assoc in HH.
     rewrite rng_mul_comm in HH.
     rewrite <- rng_mul_nat_assoc in HH.
     apply fld_eq_mul_0_r in HH; auto.
      clear H.
      remember Hns as H; clear HeqH.
      eapply char_pol_root_ne_0 with (m := m) (c₁ := c) in H; eauto .
      apply H.
      apply rng_opp_inj_wd.
      rewrite rng_opp_0.
      remember r as n in HH.
      clear Heqn.
      induction n; [ contradiction | idtac ].
      simpl in HH.
      apply fld_eq_mul_0_r in HH; auto.
      intros I.
      apply rng_opp_inj_wd in I.
      apply H.
      rewrite rng_opp_0 in I.
      rewrite <- I.
      apply rng_add_move_0_r.
      apply rng_add_opp_r.

      destruct r; [ simpl; rewrite rng_add_0_l; auto | idtac ].
      apply ac_charac_01.

 apply List.in_or_app; right; left; assumption.
Qed.

Theorem αj_m_eq_p_r : ∀ pol₁ ns₁ αj₁ αk₁ m p₁ c₁ r,
  ns₁ ∈ newton_segments pol₁
  → pol_in_K_1_m pol₁ m
  → ini_pt ns₁ = (Qnat 0, αj₁)
  → fin_pt ns₁ = (Qnat r, αk₁)
  → (0 < Qnum αj₁)%Z
  → Qnum αk₁ = 0%Z
  → c₁ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r
  → p₁ = p_of_m m (γ ns₁)
  → (1 ≠ 0)%K
  → (Qnum αj₁ * ' m = p₁ * Z.of_nat r * ' Qden αj₁)%Z.
Proof.
intros pol₁ ns₁ αj₁ αk₁ m p₁ c₁ r.
intros Hns₁ Hm Hini₁ Hfin₁ Hαj₁ Hαk₁ Hc₁ Hr₁ Hp₁ H₀.
remember Hns₁ as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk₁) in H; eauto .
 rewrite Nat.sub_0_r in H.
 destruct H as (HH₂, HH₃).
 remember (q_of_m m (γ ns₁)) as q₁.
 remember (mh_of_m m αj₁ (ps_poly_nth 0 pol₁)) as mj'.
 remember (mh_of_m m αk₁ (ps_poly_nth r pol₁)) as mk.
 unfold Qeq in HH₂; simpl in HH₂.
 rewrite Hαk₁ in HH₂; simpl in HH₂.
 symmetry in HH₂.
 apply Z.eq_mul_0_l in HH₂; auto.
 move HH₂ at top; subst mk.
 rewrite Z.sub_0_r in HH₃.
 rewrite positive_nat_Z in HH₃.
 unfold mh_of_m in Heqmj'.
 unfold mh_of_m in Heqmj'.
 erewrite <- qden_αj_is_ps_polord in Heqmj'; eauto .
 remember Heqq₁ as H; clear HeqH.
 eapply q_eq_1_any_r in H; eauto .
  rewrite H in HH₃.
  rewrite Z.mul_1_l in HH₃.
  rewrite <- HH₃.
  rewrite Heqmj'.
  symmetry.
  rewrite Z.mul_comm.
  rewrite <- Z.divide_div_mul_exact; auto.
   rewrite Z.mul_comm.
   rewrite Z.div_mul; auto.

   eapply den_αj_divides_num_αj_m; eassumption .

  rewrite Hr₁; assumption.

 apply List.in_or_app.
 right; left; eassumption .
Qed.

Theorem all_r_le_next : ∀ pol ns c pol₁ ns₁ r,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ n : nat, r ≤ nth_r n pol ns)
  → (∀ n : nat, r ≤ nth_r n pol₁ ns₁).
Proof.
intros pol ns c pol₁ ns₁ r Hc Hpol₁ Hns₁ Hri i.
pose proof (Hri (S i)) as H; simpl in H.
rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
assumption.
Qed.

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
erewrite αj_m_eq_p_r with (pol₁ := pol); try eassumption; [ idtac | eauto  ].
rewrite Pos.mul_comm.
rewrite Pos2Z.inj_mul, Zposnat2Znat; auto.
rewrite <- Z.mul_assoc.
rewrite Z.div_mul; auto.
rewrite <- Zposnat2Znat; auto.
apply Pos2Z_ne_0.
Qed.

Theorem next_ns_in_pol : ∀ pol ns c pol₁ ns₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ ∈ newton_segments pol₁.
Proof.
intros pol ns c pol₁ ns₁ Hns Hc Hpol₁ Hns₁ Hnz₁.
eapply next_has_ns in Hns; try eassumption .
eapply List_hd_in; try eassumption .
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

Theorem q_eq_1_r_non_decr : ∀ pol ns c pol₁ ns₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ i, r ≤ nth_r i pol ns)
  → (1 ≠ 0)%K
  → q_of_m m (γ ns₁) = 1%positive.
Proof.
intros pol ns c pol₁ ns₁ m r Hns HK Hq Hc Hpol₁ Hns₁ Hnz₁ Hr₀ Hrle H₀.
remember Hns as H; clear HeqH.
eapply next_ns_in_pol in H; try eassumption .
rename H into Hns₁i.
pose proof (Hrle 1%nat) as H; simpl in H.
rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
rename H into Hrle₁.
remember (root_multiplicity acf c₁ (Φq pol₁ ns₁)) as r₁ eqn:Hr₁ .
remember Hns as H; clear HeqH.
symmetry in Hr₁.
eapply next_ns_r_non_decr in H; try eassumption .
clear Hrle₁.
destruct H as (Heq, H); move Heq at top; subst r₁.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember Hns₁i as H; clear HeqH.
symmetry in Hr₁.
eapply q_eq_1_any_r with (ns := ns₁); try eassumption; eauto.
replace m with (m * 1)%positive by apply Pos.mul_1_r.
symmetry in Hq.
eapply next_pol_in_K_1_mq with (ns := ns); eassumption.
Qed.

Theorem first_n_pol_in_K_1_m_any_r : ∀ pol ns poln m c r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → q_of_m m (γ ns) = 1%positive
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ i, r ≤ nth_r i pol ns)
  → (1 ≠ 0)%K
  → ∀ n,
    (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
    → poln = nth_pol n pol ns
    → pol_in_K_1_m poln m.
Proof.
intros pol ns poln m c r Hns HK Hc Hq Hr Hri H₀ n Hnz Hpoln.
revert pol ns poln m c Hns HK Hc Hq Hr Hri Hnz Hpoln.
induction n; intros.
 simpl in Hpoln; subst poln; assumption.

 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember Hns₁ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₁, (αk₁, Hfin₁)).
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 simpl in Hpoln.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hpoln.
 assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
 apply Hnz in H; simpl in H.
 rewrite <- Hc, <- Hpol₁ in H.
 rename H into Hnz₁.
 remember Hns as H; clear HeqH.
 eapply next_ns_in_pol in H; try eassumption.
 rename H into Hns₁i.
 remember Hns as H; clear HeqH.
 eapply q_eq_1_r_non_decr in H; try eassumption.
 rename H into Hq₁.
 remember (root_multiplicity acf c₁ (Φq pol₁ ns₁)) as r₁ eqn:Hr₁ .
 pose proof (Hri 1%nat) as H; simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
 rewrite <- Hr₁ in H.
 rename H into Hrr.
 remember Hns as H; clear HeqH.
 symmetry in Hr₁.
 eapply next_ns_r_non_decr in H; try eassumption.
 destruct H as (H, _); move H at top; subst r₁.
 clear Hrr.
 eapply IHn with (pol := pol₁); try eassumption.
  replace m with (m * 1)%positive by apply Pos.mul_1_r.
  symmetry in Hq.
  eapply next_pol_in_K_1_mq with (ns := ns); try eassumption.

  eapply all_r_le_next with (pol := pol); try eassumption .

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hnz in Hin; simpl in Hin.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
  assumption.
Qed.

Theorem find_coeff_iter_succ : ∀ pol ns c pow m i n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ n, r ≤ nth_r n pol ns)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → (find_coeff n pow m pol ns i =
     find_coeff (S n) pow m pol ns i)%K.
Proof.
intros pol ns c pow m i n r Hns Hm Hq₀ Hc Hr₀ Hrle H₀ Hin.
revert pol ns c pow m n Hns Hm Hq₀ Hc Hr₀ Hrle Hin.
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
  rewrite <- Hc.
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₂| H₂].
   subst sn; simpl.
   destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₃| H₃].
    apply lt_S_n in Hin.
    destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | simpl ].
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₄| H₄].
     reflexivity.

     contradiction.

    contradiction.

   pose proof (Hrle 1%nat) as H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
   rename H into Hrle₁.
   remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
   remember (root_multiplicity acf c₁ (Φq pol₁ ns₁)) as r₁ eqn:Hr₁ .
   remember Hns as H; clear HeqH.
   symmetry in Hr₁.
   eapply next_ns_r_non_decr in H; try eassumption .
   clear Hrle₁.
   destruct H as (Heq, H); move Heq at top; subst r₁.
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
   remember Hns₁ as H; clear HeqH.
   eapply newton_segments_not_nil in H; try eassumption .
   rename H into Hns₁nz.
   remember Hns₁ as H; clear HeqH.
   apply List_hd_in in H; auto.
   rename H into Hns₁₁.
   remember Hpol₁ as H; clear HeqH.
   erewrite <- nth_pol_succ with (n := O) in H; simpl; try eassumption; auto.
   rename H into Hpol₁n.
   assert (∀ i : nat, i ≤ 1 → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps) as H.
    intros j Hj1.
    destruct j; [ assumption | idtac ].
    destruct j; [ simpl; rewrite <- Hc, <- Hpol₁; assumption | idtac ].
    exfalso; apply le_S_n in Hj1; revert Hj1; apply Nat.nle_succ_0.

    rename H into Hrle₁.
    remember Hpol₁n as H; clear HeqH.
    eapply first_n_pol_in_K_1_m_any_r in H; try eassumption .
    rename H into HK₁.
    remember Hini₁ as H; clear HeqH.
    eapply p_is_pos with (m := m) in H; try eassumption.
    rename H into Hppos.
    remember Hppos as H; clear HeqH.
    apply Z.lt_le_incl in H.
    rename H into Hpnneg.
    remember (next_pow pow ns₁ m) as pow₁ eqn:Hpow₁ .
    symmetry in Hpow₁.
    destruct pow₁.
     replace pow with (0 + pow)%nat in Hpow₁ by auto.
     rewrite next_pow_add in Hpow₁.
     apply Nat.eq_add_0 in Hpow₁.
     destruct Hpow₁ as (Hpow₁, Hpow).
     erewrite next_pow_eq_p with (pol := pol₁) in Hpow₁; try eassumption .
     rewrite <- Z2Nat.inj_0 in Hpow₁.
     apply Z2Nat.inj in Hpow₁; try assumption; [ idtac | reflexivity ].
     rewrite Hpow₁ in Hppos.
     exfalso; revert Hppos; apply Z.lt_irrefl.

     remember (S pow₁) as x.
     rewrite <- Nat.add_1_r; subst x.
     rewrite <- Nat.add_1_r.
     do 2 rewrite find_coeff_add.
     subst sn.
     apply lt_S_n in Hin.
     eapply IHi; try eassumption.
      eapply q_eq_1_r_non_decr with (ns := ns); eassumption.

      eapply all_r_le_next with (pol := pol); try eassumption .
Qed.

Theorem find_coeff_more_iter : ∀ pol ns c pow m i n n' r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ j, r ≤ nth_r j pol ns)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → n ≤ n'
  → (find_coeff n pow m pol ns i =
     find_coeff n' pow m pol ns i)%K.
Proof.
intros pol ns c pow m i n n' r Hns Hm Hq₀ Hc Hr₀ Hrle H₀ Hin Hn'.
remember (n' - n)%nat as d eqn:Hd .
apply Nat.add_cancel_r with (p := n) in Hd.
rewrite Nat.sub_add in Hd; auto.
subst n'; clear Hn'.
revert n pow Hin.
revert pol ns Hns Hm Hq₀ Hr₀ Hc Hrle.
revert c.
induction d; intros; [ reflexivity | idtac ].
erewrite find_coeff_iter_succ; try eassumption; simpl.
destruct (ps_zerop K (ps_poly_nth 0 pol)) as [| H₁]; auto.
remember (Nat.compare pow i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; auto.
rewrite <- Hc.
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
 eapply next_has_ns in H; try eassumption .
 rename H into Hns₁nz.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (root_multiplicity acf c₁ (Φq pol₁ ns₁)) as r₁ eqn:Hr₁ .
 symmetry in Hr₁.
 pose proof (Hrle 1%nat) as H; simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H; auto.
 rewrite Hr₁ in H.
 rename H into Hrr.
 remember Hns as H; clear HeqH.
 eapply next_ns_r_non_decr in H; try eassumption ; clear Hrr.
 destruct H as (Heq, H); move Heq at top; subst r₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as H; clear HeqH.
 apply List_hd_in in H; auto.
 rename H into Hns₁i.
 remember Hns as H; clear HeqH.
 eapply first_n_pol_in_K_1_m_any_r with (n := 1%nat) in H; eauto.
  simpl in H; rewrite <- Hc, <- Hpol₁ in H.
  rename H into HK₁.
  apply IHd with (c := c₁); auto.
   symmetry in Hr₁.
   eapply q_eq_1_any_r with (pol := pol₁); try eassumption; reflexivity.

   intros j.
   pose proof (Hrle (S j)) as H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

  intros j Hj.
  destruct j; auto.
  apply le_S_n in Hj.
  apply Nat.le_0_r in Hj; rewrite Hj; simpl.
  rewrite <- Hc, <- Hpol₁; assumption.
Qed.

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
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hri Hrle H₀.
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
 eapply next_pol_in_K_1_mq in HK₁; try eassumption .
 rewrite <- Heqm₁ in HK₁.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns as H; clear HeqH.
 eapply multiplicity_is_pos in H; try eassumption .
 rename H into Hrpos.
 remember Hrpos as H; clear HeqH.
 apply Nat2Z.inj_lt in H; simpl in H.
 rename H into Hrpos₁.
 remember Hrpos as H; clear HeqH.
 apply Nat.sub_gt in H.
 rewrite Nat.sub_0_r in H.
 rename H into Hrpos₃.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; eauto.
 simpl in H; rewrite <- Hc, <- Hpol₁ in H.
 destruct H as [| H]; [ contradiction | idtac ].
 rename H into Hns₁nz; move Hns₁nz before HK₁.
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply List_hd_in in Hns₁₁; try eassumption .
 remember Hns₁₁ as HK₂; clear HeqHK₂.
 eapply next_pol_in_K_1_mq in HK₂; try eassumption; try reflexivity.
 remember Hns₁₁ as H; clear HeqH.
 symmetry in Hr₁.
 eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
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
  symmetry in Hr₁.
  erewrite αj_m_eq_p_r; try eassumption; [ idtac | reflexivity ].
  rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
  rewrite <- Z.mul_assoc.
  rewrite <- Zposnat2Znat; simpl; try eassumption .
  rewrite Z.div_mul; auto.
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
   destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    contradiction.

    destruct i; [ reflexivity | simpl ].
    destruct (ps_zerop K (ps_poly_nth 0 pol₂)) as [H₃| H₃]; auto.
    contradiction.

   subst x.
   rewrite Z.mul_shuffle0.
   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   apply Z.mul_cancel_r; auto.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc; symmetry.
   subst pr.
   rewrite Zposnat2Znat; auto.
   eapply αj_m_eq_p_r; try eassumption; reflexivity.

  rename H₁ into Hnz₂.
  pose proof (Hrle 2%nat) as H.
  remember (S 0) as one in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
  subst one; simpl in H.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
  rename H into Hrle₂.
  remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
  remember (root_multiplicity acf c₂ (Φq pol₂ ns₂)) as r₂ eqn:Hr₂ .
  symmetry in Hr₁, Hr₂.
  remember Hns₁₁ as H; clear HeqH.
  eapply next_ns_r_non_decr in H; try eassumption .
  destruct H as (Heq, H); move Heq at top; subst r₂.
  clear Hrle₂; destruct H as (αj₂, (αk₂, H)).
  destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
  remember Hns as H; clear HeqH.
  eapply next_ns_in_pol in H; try eassumption .
  rename H into Hns₁i; move Hns₁i before Hns₁.
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
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
  do 3 rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; [ idtac | simpl; auto | simpl; auto ].
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_shuffle0, Z.mul_assoc; simpl.
  remember Hns₁i as H; clear HeqH.
  eapply next_ns_in_pol in H; try eassumption .
  rename H into Hns₂i; move Hns₂i before Hns₂.
  remember (nd * ' dd * ' m₁)%Z as x.
  remember (Qnum αj₂ * ' m₁ / ' (Qden αj₂ * rq))%Z as y.
  rename Heqy into Hy.
  assert (x <= x + y * '  dd * ' dd)%Z as Hle.
   apply Z.le_sub_le_add_l.
   rewrite Z.sub_diag.
   subst y.
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.mul_nonneg_nonneg; auto.
   destruct (Qnum αj₂); simpl.
    rewrite Z.div_0_l; auto; reflexivity.

    apply Z_div_pos_is_nonneg.

    apply Z.nle_gt in Hαj₂.
    exfalso; apply Hαj₂, Pos2Z.neg_is_nonpos.

   rewrite Z.min_l; auto.
   rewrite Z.min_r; auto.
   rewrite Z.sub_diag, Z.add_simpl_l; simpl.
   rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
   unfold adjust_ps; simpl.
   rewrite series_shift_0.
   rewrite Z.sub_0_r.
   apply mkps_morphism.
    erewrite αj_m_eq_p_r in Hy; try eassumption; eauto; subst rq.
    rewrite <- Zposnat2Znat in Hy; auto; simpl in Hy.
    rewrite Pos.mul_comm, Pos2Z.inj_mul in Hy.
    rewrite <- Z.mul_assoc in Hy; simpl in Hy.
    rewrite Z.div_mul in Hy; auto.
    unfold adjust_series; simpl.
    rewrite series_shift_0.
    do 2 rewrite fold_series_const.
    do 2 rewrite series_stretch_const.
    rewrite series_mul_1_l.
    rewrite <- series_stretch_stretch.
    rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
    remember Hini₂ as H; clear HeqH.
    eapply p_is_pos with (m := m₁) in H; try eassumption .
    rewrite <- Hy in H.
    rename H into Hppos.
    remember Hppos as H; clear HeqH.
    apply Z.lt_le_incl in H.
    rewrite Z2Nat.inj_mul; auto; simpl.
    rewrite <- stretch_shift_series_distr.
    rewrite <- series_stretch_const with (k := (dd * dd)%positive).
    rewrite <- series_stretch_add_distr.
    apply stretch_morph; [ reflexivity | idtac ].
    unfold series_add; simpl.
    constructor; intros i; simpl.
    destruct (lt_dec i (Z.to_nat y)) as [H₁| H₁].
     destruct (zerop i) as [H₂| H₂].
      subst i; simpl.
      rewrite rng_add_0_r.
      unfold root_tail_series_from_cγ_list; simpl.
      rewrite <- Hc₁.
      destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
      contradiction.

      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list; simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      rewrite Hy in H₁.
      erewrite <- next_pow_eq_p in H₁; try eassumption .
      destruct i; [ exfalso; revert H₂; apply Nat.lt_irrefl | idtac ].
      clear H₂; simpl.
      destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [| H₂]; auto.
      clear H₂.
      destruct (ps_zerop K (ps_poly_nth 0 pol₂)) as [| H₂]; auto.
      clear H₂.
      remember (next_pow 0 ns₂ m₁) as p₂ eqn:Hp₂ .
      remember (Nat.compare p₂ (S i)) as cmp; symmetry in Heqcmp.
      destruct cmp as [H₄| H₄| H₄]; auto.
       apply nat_compare_eq in Heqcmp.
       rewrite Heqcmp in H₁.
       exfalso; revert H₁; apply Nat.lt_irrefl.

       apply nat_compare_lt in Heqcmp.
       apply Nat.lt_le_incl, Nat.nlt_ge in Heqcmp.
       contradiction.

     apply Nat.nlt_ge in H₁.
     destruct (zerop i) as [H₂| H₂].
      subst i; simpl.
      apply Nat.le_0_r in H₁.
      rewrite <- Z2Nat.inj_0 in H₁.
      apply Z2Nat.inj in H₁; auto; [ idtac | reflexivity ].
      rewrite H₁ in Hppos.
      exfalso; revert Hppos; apply Z.lt_irrefl.

      rewrite rng_add_0_l.
      remember (Z.to_nat y) as n₂.
      remember (i - n₂)%nat as id.
      unfold root_tail_series_from_cγ_list.
      clear H.
      symmetry in Hr₁.
      remember Hns₁i as H; clear HeqH.
      eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
      rename H into Hq₁; move Hq₁ before Hns₁nz.
      symmetry in Hr₂.
      remember Hns₂i as H; clear HeqH.
      eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
      rename H into Hq₂; move Hq₂ before Hnz₂.
      assert (∀ n, r ≤ nth_r n pol₁ ns₁) as Hrle₁.
       eapply all_r_le_next with (pol := pol); eassumption .

       move Hrle₁ before Hrle.
       assert (∀ n, r ≤ nth_r n pol₂ ns₂) as Hrle₂.
        eapply all_r_le_next with (pol := pol₁); eassumption .

        move Hrle₂ before Hrle₁.
        rewrite find_coeff_iter_succ with (r := r); eauto; symmetry.
        rewrite find_coeff_iter_succ with (r := r); eauto; symmetry.
        subst x; clear Hle.
        remember (S i) as si.
        remember (S (S id)) as x; simpl; subst x.
        destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₄| H₄].
         contradiction.

         destruct i; [ exfalso; revert H₂; apply Nat.lt_irrefl | idtac ].
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂; symmetry.
         rewrite <- find_coeff_add with (dp := n₂).
         rewrite Heqid.
         rewrite Nat.add_0_l, Nat.sub_add; auto.
         rewrite <- Heqid.
         subst si; remember (S i) as si.
         rewrite Hy in Heqn₂.
         symmetry in Hr₂.
         erewrite <- next_pow_eq_p in Heqn₂; try eassumption .
         remember (S id) as sid.
         subst n₂; simpl.
         destruct (ps_zerop K (ps_poly_nth 0 pol₂)) as [H₃| H₃].
          reflexivity.

          remember (next_pow 0 ns₂ m₁) as pow₁ eqn:Hpow₁ .
          remember (Nat.compare pow₁ si) as cmp₁ eqn:Hcmp₁ .
          symmetry in Hcmp₁.
          destruct cmp₁; auto.
          rewrite <- Hc₂.
          remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃.
          remember (List.hd phony_ns (newton_segments pol₃)) as ns₃.
          destruct (ps_zerop _ (ps_poly_nth 0 pol₃)) as [H₅| H₅].
           subst si sid; simpl.
           destruct (ps_zerop _ (ps_poly_nth 0 pol₃)) as [H₆| H₆].
            reflexivity.

            contradiction.

           rename H₅ into Hnz₃.
           replace pow₁ with (0 + pow₁)%nat by auto.
           rewrite next_pow_add.
           apply Nat.add_cancel_r with (p := pow₁) in Heqid.
           rewrite Nat.sub_add in Heqid; auto.
           rewrite <- Heqid.
           do 2 rewrite find_coeff_add.
           subst sid.
           remember Hns₂i as H; clear HeqH.
           eapply next_ns_in_pol in H; try eassumption .
           rename H into Hns₃i.
           remember Hns₂i as H; clear HeqH.
           symmetry in Hq₂.
           eapply next_pol_in_K_1_mq with (q := xH) in H; try eassumption .
           rewrite Pos.mul_1_r in H.
           rename H into HK₃.
           pose proof (Hrle₁ 2%nat) as H.
           remember (S 0) as one; simpl in H.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
           subst one; simpl in H.
           rename Heqpol₃ into Hpol₃.
           rename Heqns₃ into Hns₃.
           rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in H.
           remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
           remember (root_multiplicity acf c₃ (Φq pol₃ ns₃)) as r₃ eqn:Hr₃ .
           rename H into Hrr.
           remember Hns₂i as H; clear HeqH.
           symmetry in Hr₃.
           eapply next_ns_r_non_decr in H; try eassumption ; clear Hrr.
           destruct H as (Heq, H); move Heq at top; subst r₃.
           destruct H as (αj₃, (αk₃, H)).
           destruct H as (Hini₃, (Hfin₃, (Hαj₃, Hαk₃))).
           remember Hns₃i as H; clear HeqH.
           symmetry in Hr₃.
           eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
           rename H into Hq₃.
           assert (∀ n, r ≤ nth_r n pol₃ ns₃) as Hrle₃.
            eapply all_r_le_next with (pol := pol₂); eassumption .

            move Hrle₃ before Hrle₂.
            symmetry in Hr₃.
            eapply find_coeff_more_iter; try eassumption; auto.
            erewrite next_pow_eq_p in Hpow₁; try eassumption .
            rewrite <- Hy in Hpow₁.
            destruct pow₁.
             rewrite <- Z2Nat.inj_0 in Hpow₁.
             apply Z2Nat.inj in Hpow₁; [ idtac | reflexivity | idtac ].
              rewrite <- Hpow₁ in Hppos.
              exfalso; revert Hppos; apply Z.lt_irrefl.

              apply Z.lt_le_incl; auto.

             rewrite Nat.add_succ_r, <- Nat.add_succ_l.
             apply Nat.le_sub_le_add_l.
             rewrite Nat.sub_diag; apply Nat.le_0_l.

    subst x.
    rewrite Z.mul_shuffle0, Pos2Z.inj_mul, Z.mul_assoc.
    apply Z.mul_cancel_r; auto.
    rewrite Z.mul_comm.
    rewrite <- Z.divide_div_mul_exact; auto.
     rewrite Z.mul_comm.
     apply Z.div_mul; auto.

     rewrite Heqdd, Heqnd.
     rewrite Pos_mul_shuffle0, Z.mul_shuffle0, Pos2Z.inj_mul.
     apply Z.mul_divide_mono_r.
     erewrite αj_m_eq_p_r with (ns₁ := ns₁); try eassumption; eauto.
     rewrite Pos.mul_comm, Hrq.
     rewrite Pos2Z.inj_mul, Zposnat2Znat; auto.
     exists (p_of_m m₁ (γ ns₁)).
     rewrite Z.mul_assoc; reflexivity.

    rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.
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
destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
contradiction.
Qed.

Theorem nth_in_newton_segments_any_r : ∀ pol₁ ns₁ c₁ poln nsn n,
  ns₁ ∈ newton_segments pol₁
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → nsn ∈ newton_segments poln.
Proof.
intros pol₁ ns₁ c₁ poln nsn n Hns₁ Hc₁ Hpsi Hpoln Hnsn.
subst poln nsn.
pose proof (exists_pol_ord K pol₁) as H.
destruct H as (m, (Hm, Hp)); clear Hm.
revert pol₁ ns₁ c₁ m Hns₁ Hp Hc₁ Hpsi.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
assert (1 ≤ S n) as H₁ by apply le_n_S, Nat.le_0_l.
apply Hpsi in H₁; simpl in H₁.
rewrite <- Hc₁, <- Hpol₂ in H₁.
remember (q_of_m m (γ ns₁)) as q₀ eqn:Hq₀ .
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
eapply IHn with (m := (m * q₀)%positive); try eassumption; try reflexivity.
 eapply next_ns_in_pol; eassumption .

 eapply next_pol_in_K_1_mq; eassumption .

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hpsi in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
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
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ n, r ≤ nth_r n pol ns)
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (1 ≠ 0)%K
  → poln = nth_pol n pol ns
  → pol_in_K_1_m poln m.
Proof.
intros pol ns c αj αk poln m n r.
intros Hns HK Hc Hini Hfin Hαj Hαk Hr Hrle Hpsi H₀ Hpoln.
eapply first_n_pol_in_K_1_m_any_r; try eassumption.
symmetry in Hr.
eapply q_eq_1_any_r; try eassumption.
reflexivity.
Qed.

Theorem all_ns_in_newton_segments : ∀ pol ns b r,
  ns ∈ newton_segments pol
  → zerop_1st_n_const_coeff b pol ns = false
  → nth_r 0 pol ns = r
  → (∀ i, r ≤ nth_r i pol ns)
  → ∀ n : nat, n ≤ b → nth_ns n pol ns ∈ newton_segments (nth_pol n pol ns).
Proof.
intros pol ns b r Hns Hz Hr Hri n Hnb.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
revert pol ns n Hns Hz Hr Hri Hnb.
induction b; intros; [ apply Nat.le_0_r in Hnb; subst n; auto | idtac ].
destruct n; auto.
apply le_S_n in Hnb; simpl.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
apply IHb; auto.
 eapply nth_in_newton_segments_any_r with (n := 1%nat); try eassumption.
  intros i Hi1.
  apply Hz.
  transitivity 1%nat; auto; apply le_n_S, Nat.le_0_l.

  simpl; rewrite <- Hc; assumption.

  simpl; rewrite <- Hc, <- Hpol₁; assumption.

 intros i Hib.
 apply Nat.succ_le_mono in Hib.
 apply Hz in Hib; simpl in Hib.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hib; assumption.

 simpl in Hr; rewrite <- Hc in Hr.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (root_multiplicity acf c₁ (Φq pol₁ ns₁)) as r₁ eqn:Hr₁ .
 remember Hns as H; clear HeqH.
 symmetry in Hr₁.
 eapply next_ns_r_non_decr in H; try eassumption.
  destruct H as (H, _); move H at top; subst r₁.
  simpl; rewrite <- Hc₁; assumption.

  clear H.
  assert (1 ≤ S b)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hz in H; simpl in H.
  rewrite <- Hc, <- Hpol₁ in H; assumption.

  clear H.
  pose proof (Hri 1%nat) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁, Hr₁ in H; assumption.

 intros i.
 pose proof (Hri (S i)) as H; simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.
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
 eapply nth_ns_n; try eassumption; eauto.
Qed.

Theorem non_decr_imp_eq : ∀ pol ns b r,
  ns ∈ newton_segments pol
  → zerop_1st_n_const_coeff b pol ns = false
  → nth_r 0 pol ns = r
  → (∀ i, r ≤ nth_r i pol ns)
  → ∀ n : nat, n ≤ b → nth_r n pol ns = r.
Proof.
intros pol ns b r Hns Hz Hr Hri n Hnb.
revert pol ns n Hns Hz Hr Hri Hnb.
induction b; intros; [ apply Nat.le_0_r in Hnb; subst n; auto | idtac ].
destruct n; auto.
apply le_S_n in Hnb.
remember Hz as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_succ2 in H.
apply orb_false_iff in H.
destruct H as (Hz₁, _).
remember Hns as H; clear HeqH.
eapply all_ns_in_newton_segments in H; try eassumption.
rename H into Hnsni.
remember (nth_ns n pol ns) as nsn eqn:Hnsn .
remember (nth_pol n pol ns) as poln eqn:Hpoln .
remember (ac_root (Φq poln nsn)) as cn eqn:Hcn .
remember (next_pol poln (β nsn) (γ nsn) cn) as poln₁ eqn:Hpoln₁ .
remember (List.hd phony_ns (newton_segments poln₁)) as nsn₁ eqn:Hnsn₁ .
remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
remember (nth_r (S n) pol ns) as r₁ eqn:Hr₁ .
remember Hnb as H; clear HeqH.
symmetry in Hr₁.
apply Nat.succ_le_mono in H.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
apply Hz in H.
erewrite nth_pol_succ in H; try eassumption; try reflexivity.
erewrite nth_c_n in H; try eassumption.
rewrite <- Hcn, <- Hpoln₁ in H.
rename H into Hnzn₁.
remember Hns as H; clear HeqH.
eapply IHb in H; eauto .
rename H into Hrn.
remember Hcn as H; clear HeqH.
erewrite <- nth_c_n in H; try eassumption.
rename H into Hcnn.
remember Hnsni as H; clear HeqH.
eapply next_ns_r_non_decr with (r := r) (r₁ := r₁) in H; eauto .
 destruct H; symmetry; assumption.

 erewrite <- nth_r_n; try eassumption.

 symmetry; clear H.
 remember Hpoln as H; clear HeqH.
 eapply nth_pol_succ in H; try eassumption.
 rewrite <- Hpoln₁ in H.
 symmetry in H.
 rename H into Hpoln₁₁.
 remember Hpoln₁₁ as H; clear HeqH.
 eapply nth_ns_succ in H; try eassumption.
 rewrite <- Hnsn₁ in H.
 symmetry in H.
 rename H into Hnsn₁₁.
 erewrite nth_r_n in Hr₁; eauto .
 erewrite nth_c_n; try eassumption.

 rewrite <- Hr₁; apply Hri.
Qed.

Theorem zerop_1st_n_const_coeff_false_succ : ∀ pol ns n,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → zerop_1st_n_const_coeff n (nth_pol 1 pol ns) (nth_ns 1 pol ns) = false
  ↔ zerop_1st_n_const_coeff (S n) pol ns = false.
Proof.
intros pol ns n Hnz.
split; intros H.
 apply zerop_1st_n_const_coeff_false_iff.
 apply not_zero_1st_prop; assumption.

 simpl in H.
 destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
 contradiction.
Qed.

Theorem root_tail_from_0_const_r : ∀ pol ns c pol₁ ns₁ c₁ m q₀ b r,
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
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (S b) pol₁ ns₁)%ps.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ b r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hri Hrle H₀.
remember (m * q₀)%positive as m₁.
destruct b; [ subst m₁; eapply root_tail_split_1st_any_r; eauto  | idtac ].
remember (zerop_1st_n_const_coeff (S b) pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 unfold root_tail, root_head.
 rewrite Hz₁.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁; simpl.
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; try eassumption.
 rewrite <- Heqm₁ in HK₁.
 rewrite zerop_1st_n_const_coeff_succ in Hz₁.
 apply Bool.orb_false_iff in Hz₁.
 destruct Hz₁ as (Hz₁, Hpsi).
 simpl in Hz₁.
 remember (ps_poly_nth 0 pol₁) as y.
 destruct (ps_zerop K y) as [| Hnz₁]; [ discriminate Hz₁ | subst y ].
 clear Hz₁.
 pose proof (Hri O Nat.le_0_1) as H; simpl in H.
 rename H into Hr₀.
 pose proof (Hri 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rename H into Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁.
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; try eassumption).
 remember Hns as H; clear HeqH.
 eapply next_ns_in_pol in H; eauto .
 rename H into Hns₁i.
 apply zerop_1st_n_const_coeff_false_succ in Hpsi; [ idtac | assumption ].
 remember Hr₁ as H; clear HeqH.
 rewrite <- nth_r_n with (n := O) (ns := ns₁) (pol := pol₁) in H; auto.
 rename H into Hr₁n.
 assert
  (∀ n, n ≤ S b → nth_ns n pol₁ ns₁ ∈ newton_segments (nth_pol n pol₁ ns₁)).
  apply all_ns_in_newton_segments with (r := r); try assumption.
  intros i.
  pose proof (Hrle (S i)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.

  rename H into Hain.
  assert (∀ n, n ≤ S b → nth_r n pol₁ ns₁ = r) as Hreq.
   apply non_decr_imp_eq; auto.
   intros i.
   pose proof (Hrle (S i)) as H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.

   assert (∀ i, i ≤ S b → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
    apply not_zero_1st_prop; auto.
    apply zerop_1st_n_const_coeff_false_succ; assumption.

    clear Hpsi; rename H into Hpsi.
    assert (∀ i, r ≤ nth_r i pol₁ ns₁) as Hrle₁.
     eapply all_r_le_next with (ns := ns); try eassumption.

     pose proof (Hpsi (S b) (Nat.le_refl (S b))) as H.
     rename H into Hpsib₁.
     remember (S b) as b₁ eqn:Hb₁ .
     remember (nth_ns b₁ pol₁ ns₁) as nsb₂ eqn:Hnsb₂ .
     remember (nth_pol b₁ pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
     pose proof (Hain b₁ (Nat.le_refl b₁)) as H.
     rewrite <- Hnsb₂, <- Hpolb₂ in H.
     rename H into Hnsb₂i.
     remember Hns₁i as H; clear HeqH.
     eapply r_n_nth_ns with (n := b) (r := r) in H; eauto .
      erewrite <- nth_ns_succ2 in H; eauto .
      rewrite <- Hb₁ in H.
      rewrite <- Hnsb₂ in H.
      destruct H as (αjb₂, (αkb₂, H)).
      destruct H as (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂))).
      unfold root_tail, root_head.
      apply zerop_1st_n_const_coeff_false_iff in Hpsi.
      rewrite Hpsi.
      rewrite zerop_1st_n_const_coeff_succ2.
      rewrite Hpsi.
      rewrite zerop_1st_n_const_coeff_false_iff in Hpsi.
      simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      rewrite <- Hpolb₂, <- Hnsb₂.
      rewrite Nat.add_0_r, rng_add_0_r.
      unfold root_tail_from_cγ_list, ps_monom; simpl.
      rewrite Nat.add_0_r, Z.mul_1_r, Z.add_0_r.
      rewrite Pos.mul_1_r.
      erewrite nth_γ_n; eauto ; simpl.
      remember (nth_pol b₁ pol₂ ns₂) as polb₃ eqn:Hpolb₃ .
      remember (nth_ns b₁ pol₂ ns₂) as nsb₃ eqn:Hnsb₃ .
      rewrite Hinib₂, Hfinb₂; simpl.
      rewrite Hαkb₂; simpl.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; auto.
      remember Hns₁ as H; clear HeqH.
      eapply r_n_next_ns with (ns := ns) in H; try eassumption.
      destruct H as (αj₁, (αk₁, H)).
      destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
      remember Hns₁i as H; clear HeqH.
      eapply nth_pol_in_K_1_m with (poln := polb₂) in H; eauto .
      rename H into HKb₂.
      pose proof (Hreq b₁ (Nat.le_refl b₁)) as H.
      erewrite nth_r_n in H; eauto .
      erewrite nth_c_n in H; eauto .
      rename H into Hrb₂.
      erewrite αj_m_eq_p_r with (pol₁ := polb₂); eauto .
      rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
      rewrite <- Z.mul_assoc.
      rewrite <- Zposnat2Znat; simpl; try eassumption.
      rewrite Z.div_mul; auto.
      destruct (ps_zerop K (ps_poly_nth 0 polb₃)) as [H₁| H₁].
       rewrite rng_mul_0_r, rng_add_0_r.
       remember (Qden αjb₂ * Pos.of_nat r * Qden αkb₂)%positive as dd.
       rewrite ps_adjust_eq with (n := O) (k := dd); symmetry.
       rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
       unfold adjust_ps; simpl.
       rewrite Pos.mul_comm.
       do 2 rewrite Z.sub_0_r.
       do 2 rewrite series_shift_0.
       rewrite fold_series_const, series_stretch_const.
       rewrite Z.mul_shuffle0.
       erewrite αj_m_eq_p_r with (pol₁ := polb₂); try eassumption; eauto .
       do 2 rewrite <- Z.mul_assoc.
       remember (Z.of_nat r * (' Qden αjb₂ * ' Qden αkb₂))%Z as x.
       rewrite Z.mul_comm, Z.mul_shuffle0 in Heqx.
       rewrite <- Zposnat2Znat in Heqx; auto.
       simpl in Heqx.
       rewrite <- Heqdd in Heqx; subst x.
       apply mkps_morphism; auto.
       unfold series_stretch.
       constructor; intros i; simpl.
       rename H₁ into Hzb₃.
       destruct (zerop (i mod Pos.to_nat dd)) as [H₁| H₁].
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
         destruct (ps_zerop K (ps_poly_nth 0 polb₂)) as [H₁| H₁].
          contradiction.

          erewrite nth_c_n; try eassumption; reflexivity.

         simpl.
         destruct (ps_zerop K (ps_poly_nth 0 polb₂)) as [| H₂]; auto.
         destruct d.
          rewrite Hd in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          remember (ac_root (Φq polb₂ nsb₂)) as cb₂ eqn:Hcb₂ .
          erewrite <- nth_pol_n with (c := c₁); eauto .
          erewrite <- nth_ns_n with (c := c₁); eauto .
           simpl.
           rewrite <- Hpolb₃.
           destruct (ps_zerop K (ps_poly_nth 0 polb₃));
            [ reflexivity | contradiction ].

           eapply nth_pol_n with (c := c₁); eauto .

        destruct (zerop i); [ subst i | reflexivity ].
        rewrite Nat.mod_0_l in H₁; auto.
        exfalso; revert H₁; apply Nat.lt_irrefl.

       rename H₁ into Hnzb₃.
       remember Hnsb₃ as H; clear HeqH.
       erewrite nth_ns_n in H; eauto .
       erewrite <- nth_pol_n in H; eauto .
       rewrite <- Hpolb₃ in H.
       rename H into Hnsb₃₁.
       remember Hpolb₃ as H; clear HeqH.
       erewrite nth_pol_n in H; eauto .
       rename H into Hpolb₃n.
       remember Hnsb₃₁ as H; clear HeqH.
       eapply next_ns_in_pol with (pol := polb₂) in H; eauto .
       rename H into Hnsb₃i.
       assert (1 ≤ b₁) as H by (subst b₁; apply le_n_S, Nat.le_0_l).
       apply Hain in H; simpl in H.
       rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
       rename H into Hns₂i.
       pose proof (Hrle₁ (S b₁)) as H; simpl in H.
       rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
       rename H into Hler₃.
       remember Hnsb₂i as H; clear HeqH.
       remember (ac_root (Φq polb₃ nsb₃)) as cb₃ eqn:Hcb₃ .
       remember (root_multiplicity acf cb₃ (Φq polb₃ nsb₃)) as rcb₃ eqn:Hrcb₃ .
       symmetry in Hrcb₃.
       erewrite nth_r_n in Hler₃; eauto .
       erewrite nth_c_n in Hler₃; eauto .
       rewrite <- Hcb₃, Hrcb₃ in Hler₃.
       eapply next_ns_r_non_decr in H; eauto .
       destruct H as (H₁, H); move H₁ at top; subst rcb₃.
       destruct H as (αjb₃, (αkb₃, H)).
       destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
       rewrite Hinib₃, Hfinb₃; simpl.
       rewrite Hαkb₃; simpl.
       rewrite Qnum_inv_Qnat_sub; auto.
       rewrite Qden_inv_Qnat_sub; auto.
       rewrite Nat.sub_0_r.
       rewrite Z.add_0_r, Z.mul_1_r.
       remember (Qden αjb₂ * Pos.of_nat r * Qden αkb₂)%positive as dd.
       rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
       do 2 rewrite Pos2Z.inj_mul.
       rewrite Z.div_mul_cancel_r; simpl; auto.
       remember (Qnum αjb₂ * ' Qden αkb₂)%Z as nd.
       assert (∀ n, r ≤ nth_r n polb₂ nsb₂) as Hrle₂.
        intros i.
        pose proof (Hrle₁ (i + b₁)%nat) as H.
        rewrite nth_r_add in H.
        rewrite <- Hpolb₂, <- Hnsb₂ in H; assumption.

        remember Hnsb₂i as H; clear HeqH.
        eapply nth_pol_in_K_1_m with (n := 1%nat) in H; eauto .
         rename H into HKb₃.
         erewrite αj_m_eq_p_r with (pol₁ := polb₃); try eassumption; eauto .
         rewrite Z.mul_shuffle0.
         rewrite <- Zposnat2Znat; auto.
         rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
         rewrite Z.div_mul; auto.
         unfold ps_add, ps_mul; simpl.
         unfold cm; simpl.
         do 2 rewrite fold_series_const.
        unfold ps_terms_add; simpl.
        unfold ps_ordnum_add; simpl.
        rewrite Z.mul_add_distr_r.
        rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
        remember (nd * ' m₁ * ' dd)%Z as x.
        remember (p_of_m m₁ (γ nsb₃)) as pb₃ eqn:Hpb₃ .
        remember Hinib₃ as H; clear HeqH.
        eapply p_is_pos with (m := m₁) in H; eauto .
        rewrite <- Hpb₃ in H.
        rename H into Hpb₃pos.
        remember Hpb₃pos as H; clear HeqH.
        apply Z.lt_le_incl in H.
        rename H into Hpb₃nneg.
        assert (x <= x + pb₃ * ' dd * ' dd)%Z as Hle.
         apply Z.le_sub_le_add_l.
         rewrite Z.sub_diag.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.mul_nonneg_nonneg; auto.

         rewrite Z.min_l; auto.
         rewrite Z.min_r; auto.
         rewrite Z.add_simpl_l, Z.sub_diag; simpl.
         rewrite Pos.mul_assoc.
         rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
         unfold adjust_ps; simpl.
         rewrite series_shift_0.
         rewrite Z.sub_0_r.
         subst nd x.
         remember (Qnum αjb₂ * ' Qden αkb₂ * ' m₁)%Z as x.
         rewrite Z.mul_shuffle0 in Heqx; subst x.
         erewrite αj_m_eq_p_r with (ns₁ := nsb₂) (pol₁ := polb₂); eauto .
         remember (p_of_m m₁ (γ nsb₂)) as pb₂ eqn:Hpb₂ .
         remember (pb₂ * Z.of_nat r * ' Qden αjb₂ * ' Qden αkb₂)%Z as x.
         do 2 rewrite <- Z.mul_assoc in Heqx.
         rewrite Z.mul_comm, Z.mul_assoc in Heqx.
         remember (Z.of_nat r * ' Qden αjb₂ * ' Qden αkb₂)%Z as y eqn:Hy .
         rewrite Z.mul_comm in Heqx; subst x.
         rewrite Z.mul_shuffle0, Z.mul_comm in Hy.
         rewrite Z.mul_assoc in Hy.
         rewrite <- Zposnat2Znat in Hy; auto.
         simpl in Hy; rewrite <- Heqdd in Hy; subst y.
         remember (m₁ * (dd * dd))%positive as x.
         rewrite Pos.mul_comm in Heqx; subst x.
         rewrite Pos2Z.inj_mul, Z.mul_assoc.
         apply mkps_morphism; auto.
         unfold adjust_series; simpl.
         rewrite series_shift_0.
         do 2 rewrite series_stretch_const.
         rewrite series_mul_1_l.
         rewrite <- series_stretch_stretch.
         rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
         rewrite Z2Nat.inj_mul; auto; simpl.
         rewrite <- stretch_shift_series_distr.
         rewrite <- series_stretch_const with (k := (dd * dd)%positive).
         rewrite <- series_stretch_add_distr.
         apply stretch_morph; [ reflexivity | idtac ].
         constructor; simpl; intros i.
         destruct (zerop i) as [H₁| H₁].
          subst i; simpl.
          destruct (lt_dec 0 (Z.to_nat pb₃)) as [H₁| H₁].
           rewrite rng_add_0_r.
           unfold root_tail_series_from_cγ_list; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 polb₂)) as [H₃| H₃].
            contradiction.

            clear H₃; symmetry.
            erewrite nth_c_n; try eassumption; reflexivity.

           apply Nat.nlt_ge in H₁.
           apply Nat.le_0_r in H₁.
           rewrite <- Z2Nat.inj_0 in H₁.
           apply Z2Nat.inj in H₁; auto; [ idtac | reflexivity ].
           rewrite H₁ in Hpb₃pos.
           exfalso; revert Hpb₃pos; apply Z.lt_irrefl.

          rewrite rng_add_0_l.
          destruct (lt_dec i (Z.to_nat pb₃)) as [H₂| H₂].
           unfold root_tail_series_from_cγ_list; simpl.
           destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
           clear H₁.
           rewrite <- Hpolb₃n, <- Hnsb₃₁.
           destruct (ps_zerop K (ps_poly_nth 0 polb₂)) as [| H₁]; auto; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 polb₃)) as [| H₃]; auto.
           clear H₁ H₃.
           erewrite next_pow_eq_p; eauto .
           rewrite <- Hpb₃.
           remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp eqn:Hcmp .
           symmetry in Hcmp.
           destruct cmp; auto.
            apply nat_compare_eq in Hcmp.
            rewrite Hcmp in H₂.
            exfalso; revert H₂; apply Nat.lt_irrefl.

            apply nat_compare_lt in Hcmp.
            eapply Nat.lt_trans in H₂; eauto .
            exfalso; revert H₂; apply Nat.lt_irrefl.

            apply Nat.nlt_ge in H₂.
            remember (i - Z.to_nat pb₃)%nat as id.
            unfold root_tail_series_from_cγ_list.
            remember Hinib₂ as H; clear HeqH.
            symmetry in Hrb₂.
            eapply q_eq_1_any_r in H; eauto .
            rename H into Hqb₂.
            remember Hinib₃ as H; clear HeqH.
            symmetry in Hrcb₃.
            eapply q_eq_1_any_r in H; eauto .
            rename H into Hqb₃.
            rewrite find_coeff_iter_succ with (r := r); auto; symmetry.
            rewrite Hcb₃ in Hrcb₃.
            rewrite find_coeff_iter_succ with (r := r); auto.
             symmetry.
             remember (S i) as si.
             remember (S (S id)) as ssid; simpl.
             destruct i.
              exfalso; revert H₁; apply Nat.lt_irrefl.

              clear H₁.
              destruct (ps_zerop K (ps_poly_nth 0 polb₂)) as [H₁| H₁].
               contradiction.

               clear H₁.
               erewrite <- nth_pol_n with (c := c₁); eauto .
               rewrite <- Hpolb₃, <- Hnsb₃₁.
               rewrite <- Hcb₃ in Hrcb₃.
               symmetry in Hrcb₃.
               erewrite next_pow_eq_p; try eassumption.
               rewrite <- Hpb₃.
               subst si ssid.
               remember (S i) as si.
               remember (S id) as sid; simpl.
               destruct (ps_zerop K (ps_poly_nth 0 polb₃)) as [| H₁]; auto.
               clear H₁.
               subst si.
               remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁.
               rename Heqcmp₁ into Hcmp₁.
               symmetry in Hcmp₁.
               destruct cmp₁.
                apply nat_compare_eq in Hcmp₁.
                rewrite Hcmp₁, Nat.sub_diag in Heqid; subst id; reflexivity.

                apply nat_compare_lt in Hcmp₁.
                destruct id.
                 symmetry in Heqid.
                 apply Nat.sub_gt in Heqid; try assumption.
                 contradiction.

                 rewrite <- Hcb₃.
                 remember (next_pol polb₃ (β nsb₃) (γ nsb₃) cb₃) as polb₄.
                 remember (List.hd phony_ns (newton_segments polb₄)) as nsb₄.
                 rename Heqpolb₄ into Hpolb₄.
                 rename Heqnsb₄ into Hnsb₄.
                 subst sid.
                 remember (Z.to_nat pb₃) as x.
                 replace x with (0 + x)%nat by reflexivity.
                 rewrite next_pow_add.
                 replace (S i)%nat with (S i - x + x)%nat at 2
                  by (apply Nat.sub_add; assumption).
                 rewrite find_coeff_add.
                 rewrite <- Heqid.
                 symmetry.
                 destruct (ps_zerop K (ps_poly_nth 0 polb₄)) as [H₁| H₁].
                  remember (S id) as sid; simpl.
                  destruct (ps_zerop K (ps_poly_nth 0 polb₄)) as [H₃| H₃].
                   reflexivity.

                   contradiction.

                  remember Hinib₂ as H; clear HeqH.
                  eapply p_is_pos with (m := m₁) in H; eauto .
                  rewrite <- Hpb₂ in H.
                  rename H into Hpb₂pos.
                  remember Hnsb₃i as H; clear HeqH.
                  eapply next_ns_in_pol in H; eauto .
                  rename H into Hnsb₄i.
                  remember Hnsb₃i as H; clear HeqH.
                  eapply nth_pol_in_K_1_m with (n := 1%nat) in H; eauto .
                   simpl in H.
                   rewrite <- Hcb₃, <- Hpolb₄ in H.
                   rename H into HK₄.
                   remember Hnsb₃i as H; clear HeqH.
                   eapply q_eq_1_r_non_decr in H; eauto .
                    rename H into Hqb₄.
                    remember (ac_root (Φq polb₄ nsb₄)) as cb₄ eqn:Hcb₄ .
                    remember
                     (root_multiplicity acf cb₄ (Φq polb₄ nsb₄)) as r₁
                     eqn:Hrb₄ .
                    symmetry in Hrb₄.
                    pose proof (Hrle₂ 2%nat) as H.
                    remember (S 0) as one in H; simpl in H.
                    erewrite <- nth_pol_n with (c := c₁) in H; eauto .
                    rewrite <- Hpolb₃, <- Hnsb₃₁ in H.
                    subst one; simpl in H.
                    rewrite <- Hcb₃, <- Hpolb₄, <- Hnsb₄, <- Hcb₄ in H.
                    rewrite Hrb₄ in H.
                    rename H into Hrr.
                    eapply find_coeff_more_iter with (r := r); eauto .
                     remember Hnsb₃i as H; clear HeqH.
                     eapply next_ns_r_non_decr in H; eauto .
                     destruct H as (HH, H); move H₁ at top; subst r₁.
                     symmetry; assumption.

                     intros j.
                     pose proof (Hrle₂ (j + 2)%nat) as H.
                     rewrite nth_r_add in H.
                     remember (S 0) as one in H; simpl in H.
                     erewrite <- nth_pol_n with (c := c₁) in H; eauto .
                     rewrite <- Hpolb₃, <- Hnsb₃₁ in H.
                     subst one; simpl in H.
                     rewrite <- Hcb₃, <- Hpolb₄, <- Hnsb₄ in H.
                     assumption.

                     subst x.
                     apply Z2Nat.inj_lt in Hpb₃pos; auto.
                      rewrite Heqid.
                      apply le_n_S.
                      apply Nat.le_sub_le_add_l.
                      apply Nat.le_sub_le_add_r.
                      rewrite Nat_sub_succ_diag.
                      assumption.

                      reflexivity.

                    intros j; clear H.
                    pose proof (Hrle₂ (j + 1)%nat) as H.
                    rewrite nth_r_add in H; simpl in H.
                    erewrite <- nth_pol_n with (c := c₁) in H; eauto .
                    rewrite <- Hpolb₃, <- Hnsb₃₁ in H.
                    assumption.

                   intros j; clear H.
                   pose proof (Hrle₂ (j + 1)%nat) as H.
                   rewrite nth_r_add in H; simpl in H.
                   erewrite <- nth_pol_n with (c := c₁) in H; eauto .
                   rewrite <- Hpolb₃, <- Hnsb₃₁ in H.
                   assumption.

                   intros j Hj.
                   destruct j; auto; simpl.
                   apply le_S_n in Hj.
                   rewrite Nat.le_0_r in Hj; subst j.
                   rewrite <- Hcb₃, <- Hpolb₄, <- Hnsb₄.
                   assumption.

                apply nat_compare_gt in Hcmp₁.
                apply Nat.nle_gt in Hcmp₁.
                contradiction.

             intros j.
             pose proof (Hrle₂ (j + 1)%nat) as H.
             rewrite nth_r_add in H; simpl in H.
             erewrite <- nth_pol_n with (c := c₁) in H; eauto .
             rewrite <- Hpolb₃, <- Hnsb₃₁ in H; assumption.

         intros j Hj.
         destruct j; auto; simpl.
         apply le_S_n in Hj.
         rewrite Nat.le_0_r in Hj; subst j; simpl.
         erewrite <- nth_pol_n with (c := c₁) (pol₁ := pol₂); eauto .
         rewrite <- Hpolb₃; assumption.

      intros i Hib.
      apply le_n_S in Hib.
      rewrite <- Hb₁ in Hib.
      apply Hpsi in Hib; simpl in Hib.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hib; assumption.

      rewrite <- Hb₁; assumption.
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
eapply ord_coeff_non_zero_in_newt_segm with (hps := jps) in H; try eassumption .
 apply order_inf in H₁.
 unfold order in H₁; simpl in H₁.
 unfold order_coeff in H; simpl in H.
 remember (series_order (ps_terms jps) 0) as v eqn:Hv .
 destruct v as [v| ].
  discriminate H₁.

  exfalso; apply H; reflexivity.

 left; symmetry; try eassumption; eauto.
Qed.

Theorem zerop_1st_n_const_coeff_more : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_poly_nth 0 (nth_pol (S n) pol ns) ≠ 0)%ps
  → zerop_1st_n_const_coeff (S n) pol ns = false.
Proof.
intros pol ns n Hz Hn.
rewrite zerop_1st_n_const_coeff_succ2.
rewrite Hz, Bool.orb_false_l.
remember (S n) as sn; simpl; subst sn.
destruct (ps_zerop K (ps_poly_nth 0 (nth_pol (S n) pol ns))); auto.
contradiction.
Qed.

Theorem root_tail_sep_1st_monom : ∀ pol ns pol₁ ns₁ c m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (∀ j : nat, r ≤ nth_r j pol₁ ns₁)
  → (∀ i : nat, i ≤ S n → nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → zerop_1st_n_const_coeff (S n) pol ns = false
  → (root_tail (m * q₀) n pol₁ ns₁ =
     ps_monom (nth_c n pol₁ ns₁) (nth_γ n pol₁ ns₁) +
     ps_monom 1%K (nth_γ n pol₁ ns₁) * root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ n r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi₁ Hrle₁ Hri H₀ Hz.
remember Hz as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_succ in H.
apply Bool.orb_false_iff in H; simpl in H.
rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
destruct H as (H, Hz₁).
remember (ps_poly_nth 0 pol) as x.
destruct (ps_zerop K x) as [Hnz| Hnz]; [ discriminate H | clear H ].
subst x.
remember (m * q₀)%positive as m₁.
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
move Hc₁ before Hns₁.
move c₁ before c.
pose proof (Hri 0%nat (Nat.le_0_l (S n))) as Hr₀; simpl in Hr₀.
assert (1 ≤ S n)%nat as Hr₁ by apply le_n_S, Nat.le_0_l.
apply Hri in Hr₁; simpl in Hr₁.
rewrite <- Hc in Hr₀.
rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁.
assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; eauto ).
pose proof (Hpsi₁ 0%nat (Nat.le_0_l n)) as H; simpl in H.
rename H into Hnz₁.
remember Hns₁ as H; clear HeqH.
eapply r_n_next_ns in H; try eassumption.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember Hns₁ as Hns₁i; clear HeqHns₁i.
eapply hd_newton_segments in Hns₁i; try eassumption.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
remember Hns as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; try eassumption.
rewrite <- Heqm₁ in H.
rename H into HK₁; move HK₁ before Hns₁i.
remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
remember (nth_ns n pol₂ ns₂) as nsn₂ eqn:Hnsn₂ .
remember Hr₀ as H; clear HeqH.
erewrite <- nth_r_n with (n := O) in H; simpl; eauto .
rename H into Hr₀₁.
remember Hns as H; clear HeqH.
eapply all_ns_in_newton_segments with (n := S n) in H; eauto .
 erewrite nth_ns_succ2 in H; eauto .
 erewrite nth_pol_succ2 in H; eauto .
 rewrite <- Hnsn₁, <- Hpoln₁ in H.
 rename H into Hnsn₁i; move Hnsn₁i before Hnsn₁.
 remember Hpoln₂ as H; clear HeqH.
 erewrite nth_pol_n with (c := c₁) in H; eauto .
 rename H into Hpoln₂₁; move Hpoln₂₁ before Hpoln₂.
 remember Hns as H; clear HeqH.
 eapply r_n_nth_ns with (poln := poln₁) in H; try eassumption.
 destruct H as (αjn₁, (αkn₁, H)).
 destruct H as (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁))).
 remember Hnsn₁ as H; clear HeqH.
 erewrite nth_ns_n with (c := c) in H; eauto .
 erewrite <- nth_pol_n with (c := c) in H; try eassumption; eauto .
 rewrite <- Hpoln₁ in H.
 rename H into Hnsn₁h.
 remember Hnsn₁h as H; clear HeqH.
 eapply newton_segments_not_nil in H; try eassumption.
 rename H into Hns₁nz.
 pose proof (Hri (S n) (Nat.le_refl (S n))) as Hrn₁; simpl in Hrn₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrn₁.
 erewrite nth_r_n in Hrn₁; try eassumption; auto.
 erewrite nth_c_n in Hrn₁; try eassumption.
 rewrite <- Hcn₁ in Hrn₁.
 remember Hns₁i as H; clear HeqH.
 eapply nth_pol_in_K_1_m in H; try eassumption.
 rename H into HKn₁.
 remember (S n) as sn.
 unfold root_tail, ps_monom; simpl.
 do 2 rewrite fold_series_const.
 subst sn.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁.
 rewrite Bool.orb_false_l; simpl.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
 rewrite <- Hpoln₂, <- Hnsn₂.
 rewrite <- Hpoln₁, <- Hnsn₁.
 erewrite nth_c_n; try eassumption.
 rewrite <- Hcn₁.
 destruct (ps_zerop K (ps_poly_nth 0 poln₂)) as [H₂| H₂].
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
  erewrite αj_m_eq_p_r with (ns₁ := nsn₁); try eassumption; eauto .
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
   destruct (ps_zerop K (ps_poly_nth 0 poln₁)) as [H₁| H₁].
    exfalso; revert H₁.
    eapply a₀_neq_0; try eassumption.

    rewrite <- Hcn₁.
    erewrite <- nth_ns_n with (c := c₁); try eassumption; auto.
    erewrite <- nth_pol_n with (c := c₁); try eassumption.
    rewrite <- Hpoln₂, <- Hnsn₂.
    destruct i; simpl; [ rewrite Hcn₁; eauto  | idtac ].
    destruct (ps_zerop K (ps_poly_nth 0 poln₂)); auto; contradiction.

   subst d₁.
   erewrite nth_γ_n; try eassumption; simpl.
   rewrite Hαkn₁; simpl.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
   rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.mul_assoc.
   apply Z.mul_cancel_r; auto.
   erewrite αj_m_eq_p_r; try eassumption; eauto .
   rewrite Zposnat2Znat; auto.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   reflexivity.

  rename H₂ into Hnzn₂; move Hnzn₂ before Hnsn₂.
  remember Hpoln₂ as H; clear HeqH.
  erewrite <- nth_pol_succ2 with (c := c₁) in H; try eassumption.
  rename H into Hpoln₂₂; move Hpoln₂₂ before Hpoln₂₁.
  remember Hnsn₂ as H; clear HeqH.
  erewrite <- nth_ns_succ2 with (c := c₁) in H; try eassumption.
  rename H into Hnsn₂₁; move Hnsn₂₁ before Hnsn₂.
  remember Hpsi₁ as H; clear HeqH.
  apply zerop_1st_n_const_coeff_false_iff in H.
  remember Hnzn₂ as HH; clear HeqHH.
  rewrite Hpoln₂₂ in HH.
  apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
  rewrite zerop_1st_n_const_coeff_false_iff in H.
  clear Hpsi₁; rename H into Hpsi₁; move Hpsi₁ after Hri.
  assert (∀ i, i ≤ S (S n) → nth_r i pol ns = r) as H.
   apply non_decr_imp_eq; auto.
    rewrite zerop_1st_n_const_coeff_succ2, Hz.
    remember (S n) as sn; simpl.
    rewrite <- Hc, <- Hpol₁, <- Hns₁.
    subst sn; simpl.
    rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
    remember (ps_poly_nth 0 (nth_pol n pol₂ ns₂)) as x.
    destruct (ps_zerop K x) as [H₁| ]; auto; subst x.
    pose proof (Hpsi₁ (S n) (Nat.le_refl (S n))) as H; simpl in H.
    rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
    contradiction.

    intros i.
    destruct i; [ rewrite Hr₀₁; auto | simpl ].
    rewrite <- Hc, <- Hpol₁, <- Hns₁.
    apply Hrle₁.

   clear Hri; rename H into Hri.
   remember Hns as H; clear HeqH.
   eapply r_n_nth_ns with (poln := poln₂) (n := S n) in H; eauto .
   destruct H as (αjn₂, (αkn₂, H)).
   destruct H as (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂))).
   unfold ps_add, ps_mul; simpl.
   unfold cm; simpl.
   unfold ps_terms_add, ps_ordnum_add; simpl.
   unfold root_tail_from_cγ_list; simpl.
   erewrite nth_γ_n; try eassumption; simpl.
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

    pose proof (Hpsi₁ n (Nat.le_succ_diag_r n)) as H.
    rewrite <- Hpoln₁ in H.
    rename H into Hnzn₁; move Hnzn₁ before Hnsn₁.
    remember Hnsn₂ as H; clear HeqH.
    erewrite nth_ns_n with (c := c₁) in H; try eassumption.
    rename H into Hnsn₂h; move Hnsn₂h before Hαkn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply newton_segments_not_nil in H; try eassumption.
    rename H into Hns₂nz; move Hns₂nz before Hnzn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply List_hd_in in H; try eassumption.
    rename H into Hnsn₂i; move Hnsn₂i before Hnsn₂h.
    remember Hpoln₂₂ as H; clear HeqH.
    eapply nth_pol_in_K_1_m in H; try eassumption.
    rename H into HKn₂; move HKn₂ before Hnsn₂i.
    remember (ac_root (Φq poln₂ nsn₂)) as cn₂ eqn:Hcn₂ .
    move Hcn₂ before Hnsn₂.
    pose proof (Hri (S (S n)) (Nat.le_refl (S (S n)))) as H.
    erewrite nth_r_succ2 in H; eauto .
    erewrite nth_r_n in H; try eassumption; eauto .
    erewrite nth_c_n in H; try eassumption; eauto .
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
     erewrite αj_m_eq_p_r; try eassumption; eauto .
     rewrite <- Zposnat2Znat; try eassumption.
     rewrite Z.mul_shuffle0, <- Z.mul_assoc.
     rewrite <- Pos2Z.inj_mul.
     rewrite Z.div_mul; auto.
     remember (p_of_m m₁ (γ nsn₂)) as pn₂ eqn:Hpn₂ .
     destruct i.
      simpl.
      destruct (lt_dec 0 (Z.to_nat pn₂)) as [H₁| H₁].
       rewrite rng_add_0_r.
       unfold root_tail_series_from_cγ_list; simpl.
       destruct (ps_zerop K (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        rewrite Hcn₁; reflexivity.

       exfalso; apply H₁; rewrite Hpn₂.
       rewrite <- Z2Nat.inj_0.
       apply Z2Nat.inj_lt;
        [ reflexivity | idtac | eapply p_is_pos; try eassumption ].
       apply Z.lt_le_incl.
       eapply p_is_pos; try eassumption.

      remember minus as f; simpl; subst f.
      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list.
      remember (S i) as si.
      remember (si - Z.to_nat pn₂)%nat as id eqn:Hid .
      symmetry in Hid.
      destruct (lt_dec si (Z.to_nat pn₂)) as [H₁| H₁].
       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        clear H₂.
        rewrite <- Hcn₁.
        erewrite <- nth_pol_n with (c := c₁); try eassumption.
        rewrite <- Hpoln₂.
        erewrite nth_pol_n with (c := c₁) in Hpoln₂; try eassumption.
        erewrite <- nth_ns_n with (c := c₁) (n := n); try eassumption.
        erewrite <- nth_pol_n with (c := c₁) in Hpoln₂; try eassumption.
        rewrite <- Hnsn₂.
        subst si; simpl.
        destruct (ps_zerop K (ps_poly_nth 0 poln₂)) as [H₂| H₂].
         contradiction.

         clear H₂.
         erewrite next_pow_eq_p; try eassumption.
         rewrite <- Hpn₂.
         remember (Nat.compare (Z.to_nat pn₂) (S i)) as cmp₁ eqn:Hcmp₁ .
         symmetry in Hcmp₁.
         destruct cmp₁; [ idtac | idtac | reflexivity ].
          apply nat_compare_eq in Hcmp₁.
          rewrite Hcmp₁ in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          apply nat_compare_lt in Hcmp₁.
          eapply Nat.lt_trans in H₁; try eassumption.
          exfalso; revert H₁; apply Nat.lt_irrefl.

       apply Nat.nlt_ge in H₁.
       symmetry in Hrn₁.
       remember Hnsn₁i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption; eauto .
       rename H into Hqn₁; move Hqn₁ before HKn₁.
       symmetry in Hrn₂.
       remember Hnsn₂i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption; eauto .
       rename H into Hqn₂; move Hqn₂ before HKn₂.
       symmetry in Hrn₁.
       rewrite Hcn₁ in Hrn₁.
       assert (∀ j, r ≤ nth_r j poln₁ nsn₁) as H.
        intros j.
        rewrite Hpoln₁, Hnsn₁.
        rewrite <- nth_r_add.
        apply Hrle₁.

        rename H into Hrlen₁.
        move Hrlen₁ before Hrle₁.
        rewrite find_coeff_iter_succ with (r := r); auto.
        symmetry.
        rewrite Hcn₂ in Hrn₂.
        assert (∀ j, r ≤ nth_r j poln₂ nsn₂) as H.
         eapply all_r_le_next with (c := cn₁); eauto .

         rename H into Hrlen₂.
         move Hrlen₂ before Hrlen₁.
         rewrite find_coeff_iter_succ with (r := r); auto.
         symmetry.
         remember (S (S si)) as ssi.
         remember (S id) as sid; simpl.
         rewrite <- Hcn₂.
         remember (next_pol poln₂ (β nsn₂) (γ nsn₂) cn₂) as poln₃ eqn:Hpoln₃ .
         remember (List.hd phony_ns (newton_segments poln₃)) as nsn₃.
         rename Heqnsn₃ into Hnsn₃h.
         destruct (ps_zerop K (ps_poly_nth 0 poln₂)) as [H₂| H₂].
          contradiction.

          clear H₂.
          destruct id.
           subst sid.
           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption.
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption.
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁);
             try eassumption.
            clear H.
            subst ssi; remember (S i) as si; simpl; subst si.
            rewrite <- Hnsn₂, <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop K (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             rewrite <- Hcn₂ in Hrn₂.
             erewrite next_pow_eq_p; try eassumption.
             rewrite <- Hpn₂.
             apply Nat.sub_0_le in Hid.
             eapply Nat.le_antisymm in Hid; try eassumption; rewrite Hid.
             remember (Nat.compare (S i) (S i)) as cmp₁ eqn:Hcmp₁ .
             symmetry in Hcmp₁.
             destruct cmp₁; auto.
              apply nat_compare_lt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

              apply nat_compare_gt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption.
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption.
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁);
             try eassumption.
            clear H.
            rewrite <- Hnsn₂.
            subst ssi; remember (S i) as si; simpl.
            rewrite <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop K (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             rewrite <- Hcn₂ in Hrn₂.
             erewrite next_pow_eq_p; try eassumption.
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
               destruct (ps_zerop K (ps_poly_nth 0 poln₃)) as [H₂| H₂].
                remember (S id) as sid; simpl.
                destruct (ps_zerop K (ps_poly_nth 0 poln₃)) as [H₃| H₃].
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
                remember Hpsi₁ as H; clear HeqH.
                apply zerop_1st_n_const_coeff_false_iff in H.
                remember Hnzn₃ as HH; clear HeqHH.
                rewrite Hpoln₃ in HH.
                erewrite <- nth_pol_n with (c := c₁) in HH; try eassumption.
                erewrite <- nth_pol_succ2 with (c := c₁) in HH;
                 try eassumption.
                apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
                rewrite zerop_1st_n_const_coeff_false_iff in H.
                rename H into Hpsi; move Hpsi before Hri.
                remember Hns₁i as H; clear HeqH.
                eapply nth_pol_in_K_1_m with (c := c₁) in H; eauto .
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_pol_n with (c := c₁) in H; try eassumption.
                rewrite <- Hpoln₃ in H.
                rename H into HKn₃; move HKn₃ before Hns₃nz.
                assert (∀ i, i ≤ S (S (S n)) → nth_r i pol ns = r) as H.
                 apply non_decr_imp_eq; auto.
                  rewrite zerop_1st_n_const_coeff_succ2.
                  rewrite zerop_1st_n_const_coeff_succ2.
                  rewrite Hz.
                  remember (S (S n)) as sn; simpl.
                  rewrite <- Hc, <- Hpol₁, <- Hns₁.
                  subst sn; remember (S n) as sn; simpl.
                  rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                  rewrite <- Hc, <- Hpol₁, <- Hns₁.
                  subst sn; simpl.
                  rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                  remember (ps_poly_nth 0 (nth_pol n pol₂ ns₂)) as x.
                  destruct (ps_zerop K x) as [H₂| ]; auto; subst x.
                   pose proof (Hpsi₁ (S n) (Nat.le_refl (S n))) as H;
                    simpl in H.
                   rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                   contradiction.

                   clear n0.
                   simpl.
                   erewrite <- nth_pol_succ2 with (ns := ns₂);
                    try eassumption; try reflexivity.
                   erewrite nth_pol_succ; try eassumption; try reflexivity.
                   erewrite nth_c_n; try eassumption.
                   rewrite <- Hcn₂, <- Hpoln₃.
                   remember (ps_poly_nth 0 poln₃) as x.
                   destruct (ps_zerop K x) as [H₂| H₂]; auto; subst x.
                   contradiction.

                  intros j.
                  destruct j; [ rewrite Hr₀₁; auto | simpl ].
                  rewrite <- Hc, <- Hpol₁, <- Hns₁.
                  apply Hrle₁.

                 clear Hri; rename H into Hri.
                 remember Hns as H; clear HeqH.
                 eapply r_n_nth_ns in H; try eassumption; try reflexivity.
                 remember (S n) as sn in H; simpl in H.
                 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                 subst sn.
                 erewrite nth_ns_n with (c := c₁) in H; try eassumption.
                 rewrite <- Hnsn₃h in H.
                 destruct H as (αjn₃, (αkn₃, H)).
                 destruct H as (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃))).
                 remember (ac_root (Φq poln₃ nsn₃)) as cn₃ eqn:Hcn₃ .
                 move Hcn₃ before HKn₃.
                 pose proof (Hri (S (S (S n))) (Nat.le_refl (S (S (S n)))))
                  as H.
                 remember (S (S n)) as sn in H; simpl in H.
                 rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
                 subst sn; remember (S n) as sn in H; simpl in H.
                 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                 subst sn.
                 erewrite nth_r_n in H; try eassumption; eauto .
                 erewrite nth_c_n in H; try eassumption; eauto .
                 erewrite nth_ns_succ in H; try eassumption; eauto .
                 erewrite nth_pol_n with (c := c₁) in H; try eassumption.
                 rewrite <- Hpoln₃, <- Hnsn₃h, <- Hcn₃ in H.
                 rename H into Hrn₃.
                 move Hrn₃ before Hcn₃.
                 symmetry in Hrn₃.
                 remember Hnsn₃i as H; clear HeqH.
                 eapply q_eq_1_any_r in H; try eassumption; eauto .
                 rename H into Hqn₃; move Hqn₃ before HKn₃.
                 symmetry in Hrn₃.
                 rewrite Hcn₃ in Hrn₃.
                 eapply find_coeff_more_iter with (r := r); auto.
                  intros j.
                  remember (S (S (S n))) as sn.
                  rewrite Hnsn₃h, Hpoln₃.
                  rewrite Hcn₂.
                  erewrite <- nth_c_succ; eauto .
                  erewrite <- nth_pol_succ; eauto .
                  erewrite <- nth_ns_succ; eauto .
                  rewrite <- nth_r_add.
                  apply Hrle₁.

                  remember Hinin₂ as H; clear HeqH.
                  eapply p_is_pos with (m := m₁) in H; try eassumption.
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
      erewrite αj_m_eq_p_r with (ns₁ := nsn₁); try eassumption; eauto .
      rewrite <- Zposnat2Znat; try eassumption.
      rewrite Z.mul_shuffle0, <- Z.mul_assoc.
      rewrite <- Pos2Z.inj_mul.
      apply Z.divide_factor_r.

 intros i.
 destruct i; [ rewrite Hr₀₁; auto | simpl ].
 rewrite <- Hc, <- Hpol₁, <- Hns₁.
 apply Hrle₁.
Qed.

Theorem root_tail_sep_1st_monom_any_r : ∀ pol ns pol₁ ns₁ c m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, (i ≤ S n)%nat → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ 1%nat → nth_r i pol ns = r)
  → (∀ i, r ≤ nth_r i pol ns)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) n pol₁ ns₁ =
       ps_monom (nth_c n pol₁ ns₁) (nth_γ n pol₁ ns₁) +
       ps_monom 1%K (nth_γ n pol₁ ns₁) *
       root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ n r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi Hri Hrle H₀.
remember (zerop_1st_n_const_coeff (S n) pol ns) as z₁ eqn:Hz .
symmetry in Hz.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz.
 discriminate Hz.

 assert (∀ i, i ≤ S n → nth_r i pol ns = r) as H.
  apply non_decr_imp_eq; auto.

  clear Hri; rename H into Hri; move Hri before Hrle.
  assert (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps) as H.
   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hpsi in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; assumption.

   rename H into Hpsi₁; move Hpsi₁ before Hpsi.
   assert (∀ j, r ≤ nth_r j pol₁ ns₁) as H.
    intros j.
    pose proof (Hrle (S j)) as H; simpl in H.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.

    rename H into Hrle₁; move Hrle₁ before Hrle.
    eapply root_tail_sep_1st_monom; eauto .
Qed.

Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ m q₀ b r n,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, i ≤ 1%nat → nth_r i pol ns = r)
  → (∀ n, r ≤ nth_r n pol ns)
  → (1 ≠ 0)%K
  → zerop_1st_n_const_coeff (S n) pol ns = false
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b n pol₁ ns₁ +
       ps_monom 1%K (γ_sum b n pol₁ ns₁) *
       root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ m q₀ b r n.
intros Hns Hm Hq₀ Hpol₁ Hns₁ Hri Hrle H₀ Hnz.
remember (ac_root (Φq pol ns)) as c eqn:Hc.
revert pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri Hrle Hnz.
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

  rewrite Nat.add_0_r, rng_add_0_r.
  rewrite root_tail_from_0_const_r; try eassumption; auto.
  unfold root_head.
  rewrite Hz₁.
  unfold root_head_from_cγ_list.
  rewrite Nat.add_0_r, rng_add_0_r.
  rewrite Nat.add_1_r; reflexivity.

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
   rewrite IHn; try eassumption.
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

    rewrite zerop_1st_n_const_coeff_succ2 in Hnz.
    apply Bool.orb_false_iff in Hnz.
    destruct Hnz; assumption.

   rewrite IHn; try eassumption.
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
    eapply root_tail_sep_1st_monom_any_r; try eassumption.
    rewrite <- Nat.add_succ_r.
    apply zerop_1st_n_const_coeff_false_iff.
    rewrite zerop_1st_n_const_coeff_succ; simpl.
    rewrite <- Hc, <- Hpol₁, <- Hns₁.
    rewrite Hz; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l (S (S n)))) as H.
    contradiction.

    rewrite zerop_1st_n_const_coeff_succ2 in Hnz.
    apply Bool.orb_false_iff in Hnz.
    destruct Hnz; assumption.
Qed.

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
  rewrite Z.mul_comm.
  apply Z.lt_1_mul_pos; auto.
  apply Z.lt_1_2.

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

End theorems.
