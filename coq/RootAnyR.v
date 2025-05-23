(* RootAnyR.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 QArith Arith ZArith Sorting.

Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import QbarM.
Require Import NbarM.
Require Import Field2.
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

Theorem lowest_i_such_that_ri_lt_r₀ : ∀ f L r n,
  r = nth_r 0 f L
  → (nth_r n f L < r)%nat
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ r ≤ nth_r (pred i) f L) ∧
    (nth_r i f L < r)%nat.
Proof.
intros f L r n Hr Hrnr.
subst r.
revert f L Hrnr.
induction n; intros.
 exfalso; revert Hrnr; apply Nat.lt_irrefl.

 destruct (lt_dec (nth_r n f L) (nth_r 0 f L)) as [H| H].
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

Theorem multiplicity_lt_length : ∀ cf c,
  (al cf ≠ [])%lap
  → (root_multiplicity acf c cf < length (al cf))%nat.
Proof.
intros cf c Hnz.
unfold root_multiplicity.
remember (al cf) as la; clear Heqla.
remember (length la) as len eqn:H.
assert (length la ≤ len) as Hlen by (apply Nat.eq_le_incl, Nat.eq_sym, H).
clear H.
revert la Hnz Hlen.
induction len; intros. {
  apply Nat.le_0_r in Hlen.
  destruct la as [| a]; [ exfalso; apply Hnz; reflexivity | idtac ].
  discriminate Hlen.
}
simpl.
destruct (fld_zerop (lap_mod_deg_1 la c)) as [H₁| H₁]. {
  apply -> Nat.succ_lt_mono.
  destruct la as [| a]; [ exfalso; apply Hnz; reflexivity | idtac ].
  simpl in Hlen.
  apply le_S_n in Hlen.
  unfold lap_mod_deg_1 in H₁; simpl in H₁.
  unfold lap_div_deg_1; simpl.
  apply IHlen. {
    revert Hnz H₁; clear; intros.
    revert a c Hnz H₁.
    induction la as [| b]; intros. {
      simpl in H₁.
      rewrite rng_mul_0_l, rng_add_0_l in H₁.
      exfalso; apply Hnz; rewrite H₁.
      constructor; reflexivity.
    }
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
  }
  rewrite length_lap_mod_div_deg_1; assumption.
}
apply Nat.lt_0_succ.
Qed.

Theorem Qnat_minus_distr_r : ∀ a b, a ≠ 0%Z → a - b # 1 = ((a # 1) - (b # 1)).
Proof.
intros a b Haz.
progress unfold Qminus.
progress unfold Qplus.
cbn.
now do 2 rewrite Z.mul_1_r.
Qed.

Theorem fold_Qnat : ∀ a, Z.of_nat a # 1 = Qnat a.
Proof. easy. Qed.

Theorem k_le_r : ∀ αj₁ αk₁ k₁ r pt pts v ms pts₁ pts₂,
  pts = pts₁ ++ [fin_pt ms … pts₂]
  → Sorted fst_lt [(0%nat, αj₁); pt … pts]
  → ms = minimise_slope (0%nat, αj₁) pt pts
  → fin_pt ms = (k₁, αk₁)
  → v == 0
  → 0 < αj₁
  → 0 <= αk₁
  → (S r, v) ∈ [pt … pts₁]
  → k₁ ≤ S r.
Proof.
intros αj₁ αk₁ k₁ r pt pts v ms pts₁ pts₂.
intros Hpts Hsort Heqms Hfin₁ Hz Hpos₀ Hnnegk Hsr.
apply Nat.nlt_ge.
intros Hrk.
assert (slope ms < slope_expr (S r, v) (k₁, αk₁)) as H. {
  apply Qnot_le_lt.
  intros H.
  rewrite slope_slope_expr in H; [ | symmetry; eassumption ].
  rewrite <- Hfin₁ in H.
  rewrite Hfin₁ in H; simpl in H.
  unfold slope_expr in H; simpl in H.
  rewrite Hz in H.
  rewrite Q_sub_0_r in H.
  unfold Qle in H; simpl in H.
  rewrite Zpos_P_of_succ_nat in H.
  rewrite <- Nat2Z.inj_succ in H.
  do 2 rewrite fold_Qnat in H.
  rewrite Qnum_inv_Qnat_sub in H; [ | assumption ].
  rewrite Z.mul_1_r in H.
  remember Hrk as Hk₁; clear HeqHk₁.
  apply Nat.lt_trans with (n := O) in Hk₁; [ idtac | apply Nat.lt_0_succ ].
  rewrite <- Nat2Z.inj_0 in H.
  rewrite fold_Qnat in H.
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
  remember (Zpos (Qden αj₁) * Zpos (Pos.of_nat k₁) * Qnum αk₁ * Zpos (Qden αk₁))%Z as x.
  rewrite Z.mul_shuffle0 in H.
  subst x.
  apply Z.mul_le_mono_pos_r in H; [ idtac | apply Pos2Z.is_pos ].
  rewrite Z.mul_sub_distr_r in H.
  rewrite Nat2Pos.inj_sub in H; [ idtac | intros HH; discriminate HH ].
  rewrite Pos2Z.inj_sub in H. {
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
    apply Z.add_pos_nonneg. {
      apply Z.mul_pos_pos. {
        apply Z.mul_pos_pos; [ idtac | apply Pos2Z.is_pos ].
        unfold Qlt in Hpos₀; simpl in Hpos₀.
        rewrite Z.mul_1_r in Hpos₀; assumption.
      }
      rewrite <- Pos2Z.inj_sub; [ apply Pos2Z.is_pos | idtac ].
      apply -> Pos.compare_lt_iff.
      rewrite <- Nat2Pos.inj_compare. {
        apply nat_compare_lt; assumption.
      } {
        intros HH; discriminate HH.
      } {
        intros Hk; subst k₁.
        revert Hrk; apply Nat.nlt_0_r.
      }
    }
    apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
    apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
    unfold Qle in Hnnegk; simpl in Hnnegk.
    rewrite Z.mul_1_r in Hnnegk; assumption.
  }
  apply -> Pos.compare_lt_iff.
  rewrite <- Nat2Pos.inj_compare. {
    apply nat_compare_lt; assumption.
  } {
    intros HH; discriminate HH.
  } {
    intros Hk; subst k₁.
    revert Hrk; apply Nat.nlt_0_r.
  }
}
rename H into Hsl.
subst pts.
remember Heqms as H; clear HeqH.
symmetry in H.
destruct Hsr as [Hsr| Hsr]. {
  subst pt.
  eapply minimise_slope_expr_le in H; try eassumption.
  apply Qle_not_lt in H; contradiction.
}
eapply min_slope_le with (pt₃ := (S r, v)) in H; try eassumption. {
  apply Qle_not_lt in H; contradiction.
} {
  apply List.in_or_app; left; assumption.
}
Qed.

Theorem next_has_root_0_or_newton_segments : ∀ f L c f₁,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = nth_pol 1 f L
  → (ps_poly_nth 0 f₁ = 0)%ps ∨ (newton_segments f₁ ≠ None).
Proof.
intros f L c f₁ HL Hc Hf₁.
remember HL as H; clear HeqH.
eapply f₁_orders in H; try eassumption; try apply eq_refl.
simpl in Hf₁.
rewrite <- Hc in Hf₁.
rewrite <- Hf₁ in H.
remember (root_multiplicity acf c (Φq f L)) as r eqn:Hr .
symmetry in Hr.
destruct H as (Hnneg, (Hpos, Hz)).
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 pose proof (Hpos O (Nat.lt_0_succ r)) as H₂.
 destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
  left; assumption.

  right.
  apply order_fin in H₁; intros H.
  unfold newton_segments in H.
  unfold points_of_ps_polynom in H.
  unfold points_of_ps_lap in H.
  unfold points_of_ps_lap_gen in H.
  unfold power_list in H.
  unfold ps_poly_nth in Hz, H₁.
  remember (al f₁) as la; clear Heqla.
  unfold ps_lap_nth in Hz, H₁.
  destruct la as [| a].
   simpl in Hz.
   rewrite order_0 in Hz; inversion Hz.

   simpl in Hz, H₁, H.
   remember (order a) as oa eqn:Hoa .
   symmetry in Hoa.
   destruct oa as [oa| ].
    remember 1%nat as pow.
    assert (1 ≤ pow)%nat as Hpow by (subst pow; apply Nat.le_refl).
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

       eapply IHla; try eassumption; apply le_n_S, Nat.le_0_l.

    apply H₁; reflexivity.
Qed.

Theorem next_has_ns : ∀ f L c f₁,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → newton_segments f₁ ≠ None.
Proof.
intros f L c f₁ HL Hc Hf₁ Hnz₁.
eapply next_has_root_0_or_newton_segments in HL; try reflexivity.
simpl in HL; rewrite <- Hc, <- Hf₁ in HL.
destruct HL; [ contradiction | assumption ].
Qed.

Theorem j_0_k_betw_r₀_r₁ : ∀ f L c f₁ L₁ c₁ j₁ αj₁ k₁ αk₁ r r₁,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq f L) = r
  → root_multiplicity acf c₁ (Φq f₁ L₁) = r₁
  → ini_pt L₁ = (j₁, αj₁)
  → fin_pt L₁ = (k₁, αk₁)
  → j₁ = 0%nat ∧ r₁ ≤ k₁ ∧ k₁ ≤ r ∧ αj₁ > 0 ∧ αk₁ >= 0 ∧
    ((r₁ < r)%nat ∨ αk₁ == 0).
Proof.
intros f L c f₁ L₁ c₁ j₁ αj₁ k₁ αk₁ r r₁.
intros HL Hc Hf₁ HL₁ Hc₁ Hps₀ Hr Hr₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember HL as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
destruct r. {
  symmetry in Hr.
  exfalso; revert Hr.
  apply multiplicity_neq_0; try eassumption.
}
assert (0 < S r)%nat as H by apply Nat.lt_0_succ.
apply Hpos in H; rename H into Hpos₀.
remember HL₁ as HL₁v; clear HeqHL₁v.
unfold newton_segments in HL₁; simpl in HL₁.
unfold points_of_ps_polynom in HL₁; simpl in HL₁.
unfold ps_poly_nth in Hnneg, Hz, Hpos.
remember (al f₁) as la.
destruct la as [| a₀]. {
  unfold ps_lap_nth in Hz; simpl in Hz.
  rewrite order_0 in Hz; inversion Hz.
}
assert (newton_segments f₁ = Some L₁) as HL₁i. {
  remember (newton_segments f₁) as Ls eqn:HLs.
  symmetry in HLs.
  destruct Ls as [Ls| ]; [ rewrite <- HLs | exfalso ]. {
    now simpl in HL₁v; unfold id in HL₁v; subst Ls.
  }
  simpl in HL₁v; move HL₁v at top; subst L₁.
  apply no_newton_segments with (i := S r) in HLs. {
    unfold ps_poly_nth, ps_lap_nth in HLs; simpl in HLs.
    rewrite <- Heqla in HLs; simpl in HLs.
    rewrite HLs in Hz.
    rewrite order_0 in Hz; inversion Hz.
  } {
    intros H.
    apply Hps₀.
    apply eq_Qbar_qinf.
    rewrite H.
    rewrite order_0; reflexivity.
  }
  apply Nat.lt_0_succ.
}
remember [ini_pt L₁ … oth_pts L₁ ++ [fin_pt L₁]] as pl eqn:Hpl .
assert (ini_pt L₁ ∈ pl) as H by (subst pl; left; reflexivity).
rewrite Hini₁ in H.
eapply order_in_newton_segment in H; try eassumption.
rename H into Hαj₁.
unfold ps_lap_nth in Hnneg, Hz, Hpos₀.
unfold points_of_ps_lap in HL₁.
unfold points_of_ps_lap_gen in HL₁.
simpl in HL₁.
remember (order a₀) as v₀.
symmetry in Heqv₀.
destruct v₀ as [v₀| ]. {
  assert (al (Φq f₁ L₁) ≠ [])%lap as Hnz. {
    rewrite al_Φq; simpl.
    rewrite Nat.sub_diag; simpl.
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H as (H₁, H₂).
    revert H₁.
    rewrite Hini₁; simpl.
    eapply ord_coeff_non_zero_in_newt_segm; try eassumption. {
      left; rewrite Hini₁; reflexivity.
    }
    reflexivity.
  }
  remember Hnz as H; clear HeqH.
  apply multiplicity_lt_length with (c := c₁) in H.
  rewrite Hr₁ in H.
  rewrite al_Φq in H.
  rewrite <- Hpl in H.
  erewrite length_char_pol in H; try eassumption; try reflexivity. {
    rewrite Hini₁ in H; simpl in H.
    progress unfold lower_convex_hull_points in HL₁.
    simpl in HL₁.
    remember (filter_finite_ord (power_list 1 la)) as pts.
    symmetry in Heqpts.
    destruct pts as [| pt]. {
      rewrite HL₁ in Hini₁, Hfin₁; simpl in Hini₁, Hfin₁.
      injection Hini₁; intros H₁ H₂.
      injection Hfin₁; intros H₃ H₄.
      subst j₁ k₁.
      rewrite Nat.sub_diag in H.
      apply Nat.lt_1_r in H.
      exfalso; revert H; rewrite <- Hr₁.
      apply multiplicity_neq_0; assumption.
    }
    simpl in HL₁.
    rewrite HL₁ in Hini₁, Hfin₁; simpl in Hini₁, Hfin₁.
    rewrite minimised_slope_beg_pt in Hini₁.
    injection Hini₁; clear Hini₁; intros H₁ H₂.
    subst v₀ j₁.
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
    remember HL₁i as H; clear HeqH.
    eapply order_in_newton_segment with (h := k₁) (αh := αk₁) in H. {
      rename H into Hαk₁.
      pose proof (Hnneg k₁) as H.
      unfold ps_poly_nth, ps_lap_nth in Hαk₁.
      rewrite <- Heqla in Hαk₁.
      rewrite Hαk₁ in H.
      apply Qbar.qfin_le_mono in H.
      rewrite and_assoc.
      split; [ assumption | idtac ].
      rename H into Hnnegk.
      rewrite minimised_slope_beg_pt in HL₁.
      rewrite Hfin₁ in HL₁.
      remember (minimise_slope (0%nat, αj₁) pt pts) as ms.
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
      eapply in_ppl_in_pts with (h := S r) (hv := v) in H; try reflexivity. {
        rename H into Hsr.
        remember HL₁i as H; clear HeqH.
        unfold newton_segments in H.
        unfold points_of_ps_polynom in H.
        unfold points_of_ps_lap in H.
        remember (points_of_ps_lap_gen 0 (al f₁)) as ptsi.
        rename H into Hlch.
        remember Heqptsi as H; clear HeqH.
        apply points_of_polyn_sorted in H.
        rewrite <- Heqla in Heqptsi.
        unfold points_of_ps_lap_gen in Heqptsi.
        simpl in Heqptsi.
        rewrite Heqv₀ in Heqptsi.
        rewrite Heqpts in Heqptsi.
        subst ptsi.
        rename H into Hsort.
        rewrite Hpts in Hsr.
        apply List.in_app_or in Hsr.
        destruct Hsr as [Hsr| Hsr]. {
          destruct pts₁ as [| pt₁]; [ contradiction | idtac ].
          simpl in Hpts.
          injection Hpts; clear Hpts; intros Hpts H₁.
          subst pt₁.
          assert (k₁ ≤ S r) as H by (eapply k_le_r; try eassumption ).
          split; [ | assumption ].
          destruct (eq_nat_dec r₁ (S r)) as [H₁| H₁]. {
            move H₁ at top; subst r₁.
            right.
            apply Nat.le_antisymm in H; [ | assumption ].
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
            destruct Hsr as [Hsr| Hsr]. {
              subst pt.
              clear IHpts₃.
              induction pts₃ as [| pt]. {
                simpl in Hsort.
                apply Sorted_inv in Hsort.
                destruct Hsort as (_, Hrel).
                apply HdRel_inv in Hrel.
                unfold fst_lt in Hrel; simpl in Hrel.
                revert Hrel; apply Nat.lt_irrefl.
              }
              simpl in Hsort.
              apply Sorted_minus_2nd in Hsort. {
                apply IHpts₃; assumption.
              }
              intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
            }
            apply IHpts₃; [ | assumption ].
            simpl in Hsort.
            apply Sorted_inv_1 in Hsort; assumption.
          }
          left.
          apply Nat_le_neq_lt; [ | assumption ].
          eapply Nat.le_trans; eassumption.
        }
        rewrite Hpts in Hsort.
        remember Hsort as H; clear HeqH.
        apply Sorted_inv_1 in H.
        simpl in Hsr.
        destruct Hsr as [Hsr| Hsr]. {
          rewrite Hfin₁ in Hsr.
          injection Hsr; intros H₁ H₂.
          rewrite H₂; split; [ idtac | reflexivity ].
          rewrite <- H₁ in Hz.
          right; assumption.
        }
        apply Sorted_app in H.
        destruct H as (_, H).
        rewrite Hfin₁ in H.
        revert Hrk Hsr H; clear; intros.
        induction pts₂ as [| pt]; [ contradiction | idtac ].
        destruct Hsr as [Hsr| Hsr]. {
          subst pt.
          apply Sorted_inv in H.
          destruct H as (_, H).
          apply HdRel_inv in H.
          unfold fst_lt in H; simpl in H.
          split; [ idtac | apply Nat.lt_le_incl; assumption ].
          left; eapply Nat.le_lt_trans; try eassumption.
        }
        apply IHpts₂; [ assumption | ].
        eapply Sorted_minus_2nd; try eassumption.
        intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
      } {
        apply le_n_S, Nat.le_0_l.
      }
      rewrite Nat_sub_succ_1; assumption.
    } {
      eassumption.
    }
    rewrite Hpl, <- Hfin₁, HL₁; simpl; right.
    apply List.in_or_app; right; left; reflexivity.
  }
  rewrite Hini₁; simpl.
  reflexivity.
}
unfold ps_poly_nth, ps_lap_nth in Hps₀.
rewrite <- Heqla in Hps₀; simpl in Hps₀.
contradiction.
Qed.

Theorem next_ns_r_non_decr : ∀ f L c f₁ L₁ c₁ r r₁,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq f L) = r
  → root_multiplicity acf c₁ (Φq f₁ L₁) = r₁
  → r ≤ r₁
  → r = r₁ ∧
    ∃ αj₁ αk₁,
    ini_pt L₁ = (0%nat, αj₁) ∧
    fin_pt L₁ = (r, αk₁) ∧
    (0 < Qnum αj₁)%Z ∧
    Qnum αk₁ = 0%Z.
Proof.
intros f L c f₁ L₁ c₁ r r₁.
intros HL Hc Hf₁ HL₁ Hc₁ Hnz₁ Hr Hr₁ Hrle.
remember HL as H; clear HeqH.
eapply next_has_ns in H; try eassumption.
rename H into HL₁nz.
remember (newton_segments f₁) as Lo eqn:HLo.
symmetry in HLo.
destruct Lo as [L'₁| ]; [ | easy ].
simpl in HL₁; subst L'₁.
remember (ini_pt L₁) as j₁ eqn:Hini₂.
destruct j₁ as (j₁, αj₁).
symmetry in Hini₂.
remember (fin_pt L₁) as k₁ eqn:Hfin₂.
destruct k₁ as (k₁, αk₁).
symmetry in Hfin₂.
remember HL as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ with (c := c) in H; try eassumption. {
  destruct H as (Hj₁, (Hrk₁, (Hk₁r, (Hαj₁, (Hαk₁, Hαk₁z))))).
  remember Hrle as H; clear HeqH.
  eapply Nat.le_trans in H; try eassumption.
  eapply Nat.le_antisymm in H; try eassumption.
  move H at top; subst r₁.
  apply Nat.le_antisymm in Hrle; try eassumption.
  move Hrle at top; subst k₁.
  split; [ apply eq_refl | ].
  destruct Hαk₁z; [ exfalso; revert H; apply Nat.lt_irrefl | idtac ].
  subst j₁.
  exists αj₁, αk₁.
  split; [ easy | idtac ].
  split; [ easy | idtac ].
  unfold Qlt in Hαj₁; simpl in Hαj₁.
  unfold Qeq in H; simpl in H.
  rewrite Z.mul_1_r in Hαj₁, H.
  split; assumption.
}
now rewrite HLo.
Qed.

Theorem r_n_next_ns : ∀ f L c f₁ L₁ c₁ r,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq f L) = r
  → root_multiplicity acf c₁ (Φq f₁ L₁) = r
  → ∃ αj αk,
    ini_pt L₁ = (0%nat, αj) ∧
    fin_pt L₁ = (r, αk) ∧
    (0 < Qnum αj)%Z ∧
    Qnum αk = 0%Z.
Proof.
intros f L c f₁ L₁ c₁ r.
intros HL Hc Hf₁ HL₁ Hc₁ Hps₀ Hr Hr₁.
remember HL₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember HL₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember HL₁ as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ in H; try eassumption.
destruct H as (Hj, (Hrk, (Hkr, (Haj, (Hak, Hrak))))).
apply Nat.le_antisymm in Hrk; [ | assumption ].
subst j₁ k₁.
exists αj₁, αk₁.
split; [ assumption | ].
split; [ assumption | ].
destruct Hrak as [H| H]; [ exfalso; revert H; apply Nat.lt_irrefl | idtac ].
unfold Qlt in Haj.
unfold Qeq in H.
simpl in Haj, H.
rewrite Z.mul_1_r in Haj, H.
split; assumption.
Qed.

Theorem r_n_nth_ns : ∀ f L c f₁ L₁ c₁ m r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → ∀ n fn Ln,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i f₁ L₁) ≠ 0)%ps)
    → (∀ i, (i ≤ S n)%nat → (nth_r i f L = r))
    → fn = nth_pol n f₁ L₁
    → Ln = nth_ns n f₁ L₁
    → ∃ αj αk,
      ini_pt Ln = (0%nat, αj) ∧
      fin_pt Ln = (r, αk) ∧
      (0 < Qnum αj)%Z ∧
      Qnum αk = 0%Z.
Proof.
intros f L c f₁ L₁ c₁ m r HL Hm Hc Hf₁ HL₁ Hc₁.
intros n fn Ln Hpsi Hri Hfn HLn.
destruct r.
 pose proof (Hri O (Nat.le_0_l (S n))) as H.
 simpl in H.
 rewrite <- Hc in H.
 eapply multiplicity_neq_0 in HL; [ | eassumption ].
 contradiction.

 remember (S r) as r'.
 assert (0 < r')%nat as Hrnz by (subst r'; apply Nat.lt_0_succ).
 clear r Heqr'; rename r' into r.
 remember (q_of_m m (γ L)) as q₀ eqn:Hq₀ .
 revert fn Ln Hpsi Hfn HLn.
 revert f L c f₁ L₁ c₁ m q₀ r HL Hm Hq₀ Hc Hc₁ Hf₁ HL₁ Hri Hrnz.
 induction n; intros.
  pose proof (Hpsi O (Nat.le_0_l O)) as Hnz; simpl in Hnz.
  simpl in Hfn, HLn; subst fn Ln.
  remember HL as H; clear HeqH.
  eapply r_n_next_ns in H; try eassumption.
   pose proof (Hri O Nat.le_0_1) as Hr; simpl in Hr.
   rewrite <- Hc in Hr; assumption.

   pose proof (Hri 1%nat (Nat.le_refl 1)) as Hr₁; simpl in Hr₁.
   rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in Hr₁; assumption.

  pose proof (Hpsi O (Nat.le_0_l (S n))) as H; simpl in H.
  rename H into Hnz₁.
  remember HL as H; clear HeqH.
  eapply r_n_next_ns with (L₁ := L₁) (r := r) in H; try eassumption.
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
   remember HL₁ as H; clear HeqH.
   eapply hd_newton_segments in H; try eassumption.
   rename H into HL₁i.
   simpl in Hfn, HLn.
   rewrite <- Hc₁ in Hfn, HLn.
   remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
   remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
   eapply IHn with (L := L₁) (L₁ := L₂) (m := (m * q₀)%positive);
    try eassumption; try reflexivity.
    eapply next_pol_in_K_1_mq with (L := L); eassumption.

    intros i Hin.
    apply le_n_S in Hin.
    apply Hri in Hin; simpl in Hin.
    rewrite <- Hc, <- Hf₁, <- HL₁ in Hin.
    assumption.

    intros i Hin.
    apply le_n_S in Hin.
    apply Hpsi in Hin; simpl in Hin.
    rewrite <- Hc₁, <- Hf₂, <- HL₂ in Hin.
    assumption.

   assert (0 ≤ S (S n)) as H₁ by apply Nat.le_0_l.
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc in H₁; assumption.

   assert (0 ≤ S n) as H₁ by apply Nat.le_0_l.
   apply Nat.succ_le_mono in H₁.
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in H₁; assumption.
Qed.

Theorem nth_newton_segments_nil : ∀ f L n,
  newton_segments f = Some L
  → newton_segments (nth_pol n f L) = None
  → (∃ i,
     i ≤ n ∧
     (i = O ∨ zerop_1st_n_const_coeff (pred i) f L = false) ∧
     zerop_1st_n_const_coeff i f L = true).
Proof.
intros f L n HL HLe.
revert f L HL HLe.
induction n; intros.
 now simpl in HLe; rewrite HLe in HL.

 simpl in HLe.
 remember HL as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; try apply eq_refl.
 destruct H as [H| H].
  simpl in H.
  remember (ac_root (Φq f L)) as c eqn:Hc .
  remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
   exists 0%nat.
   split; [ apply Nat.le_0_l | idtac ].
   split; [ left; reflexivity | simpl ].
   destruct (ps_zerop K (ps_poly_nth 0 f)); [ | contradiction ].
   apply eq_refl.

   exists 1%nat.
   split; [ apply le_n_S, Nat.le_0_l | idtac ].
   split.
    right; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 f)); [ contradiction | ].
    apply eq_refl.

    simpl.
    destruct (ps_zerop K (ps_poly_nth 0 f)); [ apply eq_refl | ].
    rewrite <- Hc, <- Hf₁.
    destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ | contradiction ].
    apply eq_refl.

  simpl in H.
  remember (ac_root (Φq f L)) as c eqn:Hc .
  remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  rename H into HLe₁.
  remember HLe as H; clear HeqH.
  apply IHn in H.
   destruct H as (i, (Hin, (Hiz, Hinz))).
   destruct Hiz as [Hiz| Hiz].
    subst i.
    simpl in Hinz.
    destruct (ps_zerop K (ps_poly_nth 0 f₁)).
     destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₂| H₂].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop K (ps_poly_nth 0 f)); [ | contradiction ].
      apply eq_refl.

      exists 1%nat.
      split; [ apply le_n_S, Nat.le_0_l | idtac ].
      split.
       right; simpl.
       destruct (ps_zerop K (ps_poly_nth 0 f)); [ | apply eq_refl ].
       contradiction.

       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 f)); [ apply eq_refl | ].
       rewrite <- Hc, <- Hf₁.
       destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ | contradiction ].
       apply eq_refl.

     discriminate Hinz.

    destruct i.
     rewrite Nat.pred_0 in Hiz.
     rewrite Hinz in Hiz; discriminate Hiz.

     rewrite Nat.pred_succ in Hiz.
     destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop K (ps_poly_nth 0 f)); [ | contradiction ].
      apply eq_refl.

      exists (S (S i)).
      split; [ apply Nat.succ_le_mono in Hin; assumption | idtac ].
      split.
       right; rewrite Nat.pred_succ.
       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 f)).
        contradiction.

        rewrite <- Hc, <- Hf₁, <- HL₁.
        assumption.

       remember (S i) as si; simpl; subst si.
       destruct (ps_zerop K (ps_poly_nth 0 f)).
        reflexivity.

        rewrite <- Hc, <- Hf₁, <- HL₁.
        assumption.

   rewrite HL₁.
   now destruct (newton_segments f₁).
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
 rewrite List.length_map, List.length_seq.
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
  rewrite List.length_map.
  rewrite List.length_seq.
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
   rewrite comb_lt; [ | apply Nat.lt_succ_diag_r ].
   reflexivity.

   destruct (le_dec (S b) n) as [H₂| H₂].
    rewrite Nat.sub_succ_r.
    remember (n - b)%nat as nb eqn:Hnb .
    symmetry in Hnb.
    destruct nb; [ simpl | reflexivity ].
    apply Nat.sub_0_le in Hnb.
    apply Nat.nle_gt in H₂; contradiction.

    apply Nat.nle_gt in H₂.
    rewrite comb_lt; [ reflexivity | assumption ].
Qed.

Theorem q_eq_1_any_r : ∀ f L c αj αk m q r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → r = root_multiplicity acf c (Φq f L)
  → ini_pt L = (0%nat, αj)
  → fin_pt L = (r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → q = 1%positive.
Proof.
intros f L c αj αk m q r HL Hm Hq Hc Hr Hini Hfin Hαj Hαk.
remember Hr as Hrv; clear HeqHrv.
remember (al (Φq f L)) as cf eqn:Hcf .
remember Hcf as H; clear HeqH.
rewrite al_Φq in H.
remember [ini_pt L … oth_pts L ++ [fin_pt L]] as pl eqn:Hpl .
remember (List.map (term_of_point f) pl) as tl eqn:Htl .
rewrite Hini in H.
simpl in H.
subst cf.
rename H into Hcf.
unfold root_multiplicity in Hr.
rewrite Hcf in Hr.
erewrite length_char_pol in Hr; try eassumption.
rewrite <- Hcf in Hr.
rewrite Nat.sub_0_r in Hr.
remember Hrv as H; clear HeqH.
eapply phi_zq_eq_z_sub_c₁_psi in H; [  | reflexivity ].
unfold eq_poly in H.
rewrite Hcf in H.
remember quotient_phi_x_sub_c_pow_r as g; simpl in H; subst g.
remember (quotient_phi_x_sub_c_pow_r (Φq f L) c r) as Ψ.
eapply Ψ_length in HeqΨ; try eassumption.
rewrite Nat.sub_0_r, Nat_sub_succ_diag in HeqΨ.
rename H into Hcp.
remember HL as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk) in H; try eassumption;
 try reflexivity; [  | symmetry; eassumption |  ]. {
  rewrite <- Hq, Nat.sub_0_r in H.
  remember (mh_of_m m αj (ps_poly_nth 0 f)) as mj eqn:Hmj .
  eapply pol_ord_of_ini_pt in Hmj; try eassumption; [  | symmetry; assumption ].
  remember (mh_of_m m αk (ps_poly_nth r f)) as mk eqn:Hmk .
  eapply pol_ord_of_fin_pt in Hmk; try eassumption; [  | symmetry; assumption ].
  destruct H as (_, Hqjr).
  unfold Qeq in Hmk.
  simpl in Hmk.
  rewrite Hαk in Hmk.
  simpl in Hmk.
  symmetry in Hmk.
  apply Z.mul_eq_0_l in Hmk; [  | apply Pos2Z_ne_0 ].
  subst mk.
  rewrite Z.sub_0_r in Hqjr.
  rewrite positive_nat_Z in Hqjr.
  remember (p_of_m m (γ L)) as p eqn:Hp .
  move Hp after Hq.
  remember HL as H; clear HeqH.
  eapply phi_degree_is_k_sub_j_div_q in H; try (symmetry; eassumption);
   [  | eassumption | reflexivity ].
  unfold Φs in H.
  rewrite Nat.sub_0_r, <- Hq in H.
  unfold has_degree in H.
  unfold pseudo_degree in H.
  remember (al (poly_shrink (Pos.to_nat q) (Φq f L))) as psh eqn:Hpsh .
  unfold poly_shrink in Hpsh.
  rewrite Hcf in Hpsh.
  simpl in Hpsh.
  destruct H as (Hshr, (Hdeg, Hpdeg)).
  remember (Pos.to_nat q) as nq eqn:Hnq .
  symmetry in Hnq.
  destruct nq; [ exfalso; revert Hnq; apply Pos2Nat_ne_0 |  ].
  destruct nq; [ apply Pos2Nat.inj; assumption | exfalso ].
  unfold poly_shrinkable in Hshr.
  rewrite Hcf in Hshr.
  assert (H : (1 mod S (S nq) ≠ 0)%nat). {
    rewrite Nat.mod_1_l; [ intros H; discriminate H |  ].
    apply -> Nat.succ_lt_mono.
    apply Nat.lt_0_succ.
  }
  apply Hshr in H.
  remember (al Ψ) as la eqn:Hla .
  symmetry in Hla.
  destruct la as [| a]; [ discriminate HeqΨ |  ].
  destruct la; [  | discriminate HeqΨ ].
  destruct (fld_zerop a) as [H₁| H₁]. {
    rewrite H₁ in Hcp.
    rewrite lap_eq_0 in Hcp.
    rewrite lap_mul_nil_r in Hcp.
    rewrite Htl, Hpl in Hcp.
    simpl in Hcp.
    rewrite Hini in Hcp; simpl in Hcp.
    apply lap_eq_cons_nil_inv in Hcp.
    destruct Hcp as (Hoj, Hcp).
    revert Hoj.
    eapply ord_coeff_non_zero_in_newt_segm; [ eassumption |  | reflexivity ].
    left; eassumption.
  }
  rewrite lap_mul_comm in Hcp.
  rewrite binomial_expansion in Hcp.
  rewrite lap_mul_const_l in Hcp.
  rewrite List.map_map in Hcp.
  assert (HH : (List.nth 1 (make_char_pol R 0 tl) 0 = 0)%K). {
    rewrite H; reflexivity.
  }
  rewrite list_nth_rng_eq in HH; [  | eassumption ].
  simpl in HH.
  destruct r. {
    symmetry in Hrv.
    revert Hrv; apply multiplicity_neq_0; assumption.
  }
  simpl in HH.
  unfold nth_coeff in HH.
  simpl in HH.
  rewrite comb_0_r, comb_1_r in HH.
  rewrite Nat.add_1_l in HH.
  rewrite Nat.sub_0_r in HH.
  apply fld_eq_mul_0_r in HH; try assumption.
  rewrite <- rng_mul_1_l in HH.
  rewrite rng_mul_comm in HH.
  rewrite rng_mul_nat_assoc in HH.
  rewrite rng_mul_comm in HH.
  rewrite <- rng_mul_nat_assoc in HH.
  apply fld_eq_mul_0_r in HH; [ | assumption | ]. {
    clear H.
    remember HL as H; clear HeqH.
    eapply char_pol_root_ne_0 with (m := m) (c₁ := c) in H; try eassumption.
    apply H.
    apply rng_opp_inj_wd.
    rewrite rng_opp_0.
    remember r as n in HH.
    clear Heqn.
    destruct (fld_zerop 1%K) as [H₀| H₀]. {
      etransitivity; [ apply eq_1_0_all_0; assumption |  ].
      symmetry; apply eq_1_0_all_0; assumption.
    }
    induction n; [ contradiction | ].
    simpl in HH.
    apply fld_eq_mul_0_r in HH; [ apply IHn, HH | assumption |  ].
    intros I.
    apply rng_opp_inj_wd in I.
    apply H.
    rewrite rng_opp_0 in I.
    rewrite <- I.
    apply rng_add_move_0_r.
    apply rng_add_opp_r.
  }
  destruct (fld_zerop 1%K) as [H₀| H₀]. {
    exfalso; apply H₁; apply eq_1_0_all_0; assumption.
  }
  destruct r; [ simpl; rewrite rng_add_0_l; assumption |  ].
  apply ac_charac_01.
}
apply List.in_or_app; right; left; assumption.
Qed.

Theorem αj_m_eq_p_r : ∀ f₁ L₁ αj₁ αk₁ m p₁ c₁ r,
  newton_segments f₁ = Some L₁
  → pol_in_K_1_m f₁ m
  → ini_pt L₁ = (0%nat, αj₁)
  → fin_pt L₁ = (r, αk₁)
  → (0 < Qnum αj₁)%Z
  → Qnum αk₁ = 0%Z
  → c₁ = ac_root (Φq f₁ L₁)
  → root_multiplicity acf c₁ (Φq f₁ L₁) = r
  → p₁ = p_of_m m (γ L₁)
  → (Qnum αj₁ * Zpos m = p₁ * Z.of_nat r * Zpos (Qden αj₁))%Z.
Proof.
intros f₁ L₁ αj₁ αk₁ m p₁ c₁ r.
intros HL₁ Hm Hini₁ Hfin₁ Hαj₁ Hαk₁ Hc₁ Hr₁ Hp₁.
remember HL₁ as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk₁) in H; try eassumption;
  try reflexivity; try (symmetry; eassumption).
 rewrite Nat.sub_0_r in H.
 destruct H as (HH₂, HH₃).
 remember (q_of_m m (γ L₁)) as q₁.
 remember (mh_of_m m αj₁ (ps_poly_nth 0 f₁)) as mj'.
 remember (mh_of_m m αk₁ (ps_poly_nth r f₁)) as mk.
 unfold Qeq in HH₂; simpl in HH₂.
 rewrite Hαk₁ in HH₂; simpl in HH₂.
 symmetry in HH₂.
 apply Z.eq_mul_0_l in HH₂; [ | apply Pos2Z_ne_0 ].
 move HH₂ at top; subst mk.
 rewrite Z.sub_0_r in HH₃.
 rewrite positive_nat_Z in HH₃.
 unfold mh_of_m in Heqmj'.
 unfold mh_of_m in Heqmj'.
 erewrite <- qden_αj_is_ps_polydo in Heqmj';
   [ | eassumption | symmetry; eassumption ].
 remember Heqq₁ as H; clear HeqH.
 eapply q_eq_1_any_r in H; try eassumption; [ | symmetry; assumption ].
 rewrite H in HH₃.
 rewrite Z.mul_1_l in HH₃.
 rewrite <- HH₃.
 rewrite Heqmj'.
 symmetry.
 rewrite Z.mul_comm.
 rewrite <- Z.divide_div_mul_exact; [ | apply Pos2Z_ne_0 | ].
  rewrite Z.mul_comm.
  rewrite Z.div_mul; [ apply eq_refl | apply Pos2Z_ne_0 ].

  eapply den_αj_divides_num_αj_m; eassumption.

 apply List.in_or_app.
 right; left; eassumption.
Qed.

Theorem all_r_le_next : ∀ f L c f₁ L₁ r,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ n : nat, r ≤ nth_r n f L)
  → (∀ n : nat, r ≤ nth_r n f₁ L₁).
Proof.
intros f L c f₁ L₁ r Hc Hf₁ HL₁ Hri i.
pose proof (Hri (S i)) as H; simpl in H.
rewrite <- Hc, <- Hf₁, <- HL₁ in H.
assumption.
Qed.

Theorem multiplicity_is_pos : ∀ f L c r,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = r
  → (0 < r)%nat.
Proof.
intros f L c r HL Hc Hr.
remember HL as H; clear HeqH.
eapply multiplicity_neq_0 in H; [ | eassumption ].
apply Nat.neq_0_lt_0 in H.
rewrite Hr in H.
assumption.
Qed.

Theorem p_is_pos : ∀ L αj αk m r,
  ini_pt L = (0%nat, αj)
  → fin_pt L = (r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → (0 < p_of_m m (γ L))%Z.
Proof.
intros L αj αk m r Hini Hfin Hαj Hαk Hr.
unfold p_of_m; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; [ | assumption ].
rewrite Qden_inv_Qnat_sub; [ | assumption ].
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
rewrite Z.gcd_comm.
apply Z_div_gcd_r_pos.
apply Z.mul_pos_pos; [ | apply Pos2Z.is_pos ].
apply Z.mul_pos_pos; [ assumption | apply Pos2Z.is_pos ].
Qed.

Theorem next_pow_eq_p : ∀ f L c αj αk m r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = r
  → ini_pt L = (0%nat, αj)
  → fin_pt L = (r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → next_pow 0 L m = Z.to_nat (p_of_m m (γ L)).
Proof.
intros f L c αj αk m r HL Hm Hc Hr Hini Hfin Hαj Hαk Hrp.
unfold next_pow; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; [ | assumption ].
rewrite Qden_inv_Qnat_sub; [ | assumption ].
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r.
rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
rewrite Pos2Z.inj_mul.
rewrite Z.div_mul_cancel_r; try apply Pos2Z_ne_0.
erewrite αj_m_eq_p_r with (f₁ := f); try eassumption; [ | reflexivity  ].
rewrite Pos.mul_comm.
rewrite Pos2Z.inj_mul, Zposnat2Znat; [ | assumption ].
rewrite <- Z.mul_assoc.
rewrite Z.div_mul; [ reflexivity | ].
rewrite <- Zposnat2Znat; [ | assumption ].
apply Pos2Z_ne_0.
Qed.

Theorem next_ns_in_f : ∀ f L c f₁ L₁,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → newton_segments f₁ = Some L₁.
Proof.
intros f L c f₁ L₁ HL Hc Hf₁ HL₁ Hnz₁.
eapply next_has_ns in HL; try eassumption.
destruct (newton_segments f₁) as [L'₁| ]; [ | easy ].
now f_equal.
Qed.

Theorem newton_segments_not_nil : ∀ f L αk r,
  L = option_get phony_ns (newton_segments f)
  → fin_pt L = (r, αk)
  → (0 < r)%nat
  → newton_segments f ≠ None.
Proof.
intros f L αk r HL Hfin Hr.
intros H; rewrite H in HL; subst L.
simpl in Hfin.
injection Hfin; intros H₁ H₂.
rewrite H₂ in Hr.
revert Hr; apply Nat.lt_irrefl.
Qed.

Theorem q_eq_1_r_non_decr : ∀ f L c f₁ L₁ m r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q_of_m m (γ L) = 1%positive
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq f L) = r
  → (∀ i, r ≤ nth_r i f L)
  → q_of_m m (γ L₁) = 1%positive.
Proof.
intros f L c f₁ L₁ m r HL HK Hq Hc Hf₁ HL₁ Hnz₁ Hr₀ Hrle.
remember HL as H; clear HeqH.
eapply next_ns_in_f in H; try eassumption.
rename H into HL₁i.
pose proof (Hrle 1%nat) as H; simpl in H.
rewrite <- Hc, <- Hf₁, <- HL₁ in H.
remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
rename H into Hrle₁.
remember (root_multiplicity acf c₁ (Φq f₁ L₁)) as r₁ eqn:Hr₁ .
remember HL as H; clear HeqH.
symmetry in Hr₁.
eapply next_ns_r_non_decr in H; try eassumption.
clear Hrle₁.
destruct H as (Heq, H); move Heq at top; subst r₁.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember HL₁i as H; clear HeqH.
symmetry in Hr₁.
eapply q_eq_1_any_r with (L := L₁); try eassumption; [ | reflexivity ].
replace m with (m * 1)%positive by apply Pos.mul_1_r.
symmetry in Hq.
eapply next_pol_in_K_1_mq with (L := L); eassumption.
Qed.

Theorem first_n_pol_in_K_1_m_any_r : ∀ f L fn m c r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c = ac_root (Φq f L)
  → q_of_m m (γ L) = 1%positive
  → root_multiplicity acf c (Φq f L) = r
  → (∀ i, r ≤ nth_r i f L)
  → ∀ n,
    (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
    → fn = nth_pol n f L
    → pol_in_K_1_m fn m.
Proof.
intros f L fn m c r HL HK Hc Hq Hr Hri n Hnz Hfn.
revert f L fn m c HL HK Hc Hq Hr Hri Hnz Hfn.
induction n; intros.
 simpl in Hfn; subst fn; assumption.

 remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
 remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
 remember HL₁ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₁, (αj₁, Hini₁)).
 remember HL₁ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₁, (αk₁, Hfin₁)).
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 simpl in Hfn.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hfn.
 assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
 apply Hnz in H; simpl in H.
 rewrite <- Hc, <- Hf₁ in H.
 rename H into Hnz₁.
 remember HL as H; clear HeqH.
 eapply next_ns_in_f in H; try eassumption.
 rename H into HL₁i.
 remember HL as H; clear HeqH.
 eapply q_eq_1_r_non_decr in H; try eassumption.
 rename H into Hq₁.
 remember (root_multiplicity acf c₁ (Φq f₁ L₁)) as r₁ eqn:Hr₁ .
 pose proof (Hri 1%nat) as H; simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in H.
 rewrite <- Hr₁ in H.
 rename H into Hrr.
 remember HL as H; clear HeqH.
 symmetry in Hr₁.
 eapply next_ns_r_non_decr in H; try eassumption.
 destruct H as (H, _); move H at top; subst r₁.
 clear Hrr.
 eapply IHn with (f := f₁); try eassumption.
  replace m with (m * 1)%positive by apply Pos.mul_1_r.
  symmetry in Hq.
  eapply next_pol_in_K_1_mq with (L := L); try eassumption.

  eapply all_r_le_next with (f := f); try eassumption.

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hnz in Hin; simpl in Hin.
  rewrite <- Hc, <- Hf₁, <- HL₁ in Hin.
  assumption.
Qed.

Theorem find_coeff_iter_succ : ∀ f L c pow m i n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q_of_m m (γ L) = 1%positive
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = r
  → (∀ n, r ≤ nth_r n f L)
  → (i < n)%nat
  → (find_coeff n pow m f L i =
     find_coeff (S n) pow m f L i)%K.
Proof.
intros f L c pow m i n r HL Hm Hq₀ Hc Hr₀ Hrle Hin.
destruct (fld_zerop 1%K) as [H₀| H₀].
 etransitivity; [ apply eq_1_0_all_0; assumption | ].
 symmetry; apply eq_1_0_all_0; assumption.

revert f L c pow m n HL Hm Hq₀ Hc Hr₀ Hrle Hin.
induction i; intros.
 destruct n; [ exfalso; revert Hin; apply Nat.lt_irrefl | idtac ].
 remember (S n) as sn.
 rewrite Heqsn in |- * at 1; simpl.
 destruct (ps_zerop _ (ps_poly_nth 0 f)) as [| H₁]; [ reflexivity | ].
 remember (Nat.compare pow 0) as cmp₁ eqn:Hcmp₁ .
 symmetry in Hcmp₁.
 destruct cmp₁; [ reflexivity | | reflexivity ].
 apply nat_compare_lt in Hcmp₁.
 exfalso; revert Hcmp₁; apply Nat.nlt_0_r.

 assert (0 < r)%nat as Hrp.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀.
  apply multiplicity_neq_0; assumption.

  destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | idtac ].
  remember (S n) as sn.
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop _ (ps_poly_nth 0 f)) as [| H₁]; [ reflexivity | ].
  remember (Nat.compare pow (S i)) as cmp₁ eqn:Hcmp₁ .
  symmetry in Hcmp₁.
  destruct cmp₁; [ reflexivity | | reflexivity ].
  rewrite <- Hc.
  remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  destruct (ps_zerop _ (ps_poly_nth 0 f₁)) as [H₂| H₂].
   subst sn; simpl.
   destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₃| H₃].
    apply Nat.succ_lt_mono in Hin.
    destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | simpl ].
    destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₄| H₄].
     reflexivity.

     contradiction.

    contradiction.

   pose proof (Hrle 1%nat) as H; simpl in H.
   rewrite <- Hc, <- Hf₁, <- HL₁ in H.
   rename H into Hrle₁.
   remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
   remember (root_multiplicity acf c₁ (Φq f₁ L₁)) as r₁ eqn:Hr₁ .
   remember HL as H; clear HeqH.
   symmetry in Hr₁.
   eapply next_ns_r_non_decr in H; try eassumption.
   clear Hrle₁.
   destruct H as (Heq, H); move Heq at top; subst r₁.
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
   remember HL₁ as H; clear HeqH.
   eapply newton_segments_not_nil in H; try eassumption.
   rename H into HL₁nz.
   remember HL₁ as H; clear HeqH.
   eapply hd_newton_segments in H; try eassumption.
   rename H into HL₁₁.
   remember Hf₁ as H; clear HeqH.
   erewrite <- nth_pol_succ with (n := O) in H; simpl; try eassumption;
   try reflexivity.
   rename H into Hf₁n.
   assert (∀ i : nat, i ≤ 1 → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps) as H.
    intros j Hj1.
    destruct j; [ assumption | idtac ].
    destruct j; [ simpl; rewrite <- Hc, <- Hf₁; assumption | idtac ].
    exfalso; apply le_S_n in Hj1; revert Hj1; apply Nat.nle_succ_0.

    rename H into Hrle₁.
    remember Hf₁n as H; clear HeqH.
    eapply first_n_pol_in_K_1_m_any_r in H; try eassumption.
    rename H into HK₁.
    remember Hini₁ as H; clear HeqH.
    eapply p_is_pos with (m := m) in H; try eassumption.
    rename H into Hppos.
    remember Hppos as H; clear HeqH.
    apply Z.lt_le_incl in H.
    rename H into Hpnneg.
    remember (next_pow pow L₁ m) as pow₁ eqn:Hpow₁ .
    symmetry in Hpow₁.
    destruct pow₁.
     replace pow with (0 + pow)%nat in Hpow₁ by reflexivity.
     rewrite next_pow_add in Hpow₁.
     apply Nat.eq_add_0 in Hpow₁.
     destruct Hpow₁ as (Hpow₁, Hpow).
     erewrite next_pow_eq_p with (f := f₁) in Hpow₁; try eassumption.
     rewrite <- Z2Nat.inj_0 in Hpow₁.
     apply Z2Nat.inj in Hpow₁; try assumption; [ idtac | reflexivity ].
     rewrite Hpow₁ in Hppos.
     exfalso; revert Hppos; apply Z.lt_irrefl.

     remember (S pow₁) as x.
     rewrite <- Nat.add_1_r; subst x.
     rewrite <- Nat.add_1_r.
     do 2 rewrite find_coeff_add.
     subst sn.
     apply Nat.succ_lt_mono in Hin.
     eapply IHi; try eassumption.
      eapply q_eq_1_r_non_decr with (L := L); eassumption.

      eapply all_r_le_next with (f := f); try eassumption.
Qed.

Theorem find_coeff_more_iter : ∀ f L c pow m i n n' r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q_of_m m (γ L) = 1%positive
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = r
  → (∀ j, r ≤ nth_r j f L)
  → (i < n)%nat
  → n ≤ n'
  → (find_coeff n pow m f L i =
     find_coeff n' pow m f L i)%K.
Proof.
intros f L c pow m i n n' r HL Hm Hq₀ Hc Hr₀ Hrle Hin Hn'.
destruct (fld_zerop 1%K) as [H₀| H₀].
 etransitivity; [ apply eq_1_0_all_0; assumption | ].
 symmetry; apply eq_1_0_all_0; assumption.

remember (n' - n)%nat as d eqn:Hd .
apply Nat.add_cancel_r with (p := n) in Hd.
rewrite Nat.sub_add in Hd; [ | assumption ].
subst n'; clear Hn'.
revert n pow Hin.
revert f L HL Hm Hq₀ Hr₀ Hc Hrle.
revert c.
induction d; intros; [ reflexivity | idtac ].
erewrite find_coeff_iter_succ; try eassumption; simpl.
destruct (ps_zerop K (ps_poly_nth 0 f)) as [| H₁]; [ reflexivity | ].
remember (Nat.compare pow i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; [ reflexivity | | reflexivity ].
rewrite <- Hc.
remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
remember (next_pow pow L₁ m) as pow₁.
destruct (ps_zerop _ (ps_poly_nth 0 f₁)) as [H₂| H₂].
 rewrite Nat.add_comm.
 destruct n; simpl.
  exfalso; revert Hin; apply Nat.nlt_0_r.

  destruct (ps_zerop _ (ps_poly_nth 0 f₁)) as [H₃| H₃].
   reflexivity.

   contradiction.

 remember HL as H; clear HeqH.
 eapply next_has_ns in H; try eassumption.
 rename H into HL₁nz.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 remember (root_multiplicity acf c₁ (Φq f₁ L₁)) as r₁ eqn:Hr₁ .
 symmetry in Hr₁.
 pose proof (Hrle 1%nat) as H; simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in H.
 rewrite Hr₁ in H.
 rename H into Hrr.
 remember HL as H; clear HeqH.
 eapply next_ns_r_non_decr in H; try eassumption ; clear Hrr.
 destruct H as (Heq, H); move Heq at top; subst r₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember HL₁ as H; clear HeqH.
 destruct (zerop r) as [Hr| Hr].
  now rewrite Hr in Hr₀; apply multiplicity_neq_0 in Hr₀.

  eapply hd_newton_segments in H; try eassumption.
  rename H into HL₁i.
  remember HL as H; clear HeqH.
  eapply first_n_pol_in_K_1_m_any_r with (n := 1%nat) in H; try eassumption;
  try reflexivity.
   simpl in H; rewrite <- Hc, <- Hf₁ in H.
   rename H into HK₁.
   apply IHd with (c := c₁); try assumption.
    symmetry in Hr₁.
    eapply q_eq_1_any_r with (f := f₁); try eassumption; reflexivity.

    intros j.
    pose proof (Hrle (S j)) as H; simpl in H.
    rewrite <- Hc, <- Hf₁, <- HL₁ in H; assumption.

   intros j Hj.
   destruct j; [ assumption | ].
   apply le_S_n in Hj.
   apply Nat.le_0_r in Hj; rewrite Hj; simpl.
   rewrite <- Hc, <- Hf₁; assumption.
Qed.

Theorem root_tail_split_1st_any_r : ∀ f L c f₁ L₁ c₁ m q₀ r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → (∀ i, i ≤ 1%nat → nth_r i f L = r)
  → (∀ n, r ≤ nth_r n f L)
  → (root_tail (m * q₀) 0 f₁ L₁ =
     root_head 0 0 f₁ L₁ +
       ps_monom 1%K (γ_sum 0 0 f₁ L₁) *
       root_tail (m * q₀) 1 f₁ L₁)%ps.
Proof.
intros f L c f₁ L₁ c₁ m q₀ r.
intros HL Hm Hq₀ Hc Hf₁ HL₁ Hc₁ Hri Hrle.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 f₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 assert (0 ≤ 1)%nat as H by apply Nat.le_0_l.
 apply Hri in H; simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 assert (1 ≤ 1)%nat as H by apply Nat.le_refl.
 apply Hri in H; simpl in H; rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in H.
 rename H into Hr₁; move Hr₁ before Hc₁.
 rename H₁ into Hnz₁.
 remember HL as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; try eassumption.
 rewrite <- Heqm₁ in HK₁.
 remember HL as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember HL as H; clear HeqH.
 eapply multiplicity_is_pos in H; try eassumption.
 rename H into Hrpos.
 remember Hrpos as H; clear HeqH.
 apply Nat2Z.inj_lt in H; simpl in H.
 rename H into Hrpos₁.
 remember Hrpos as H; clear HeqH.
 apply Nat.sub_gt in H.
 rewrite Nat.sub_0_r in H.
 rename H into Hrpos₃.
 remember HL as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H;
   [ | eassumption | reflexivity ].
 simpl in H; rewrite <- Hc, <- Hf₁ in H.
 destruct H as [| H]; [ contradiction | idtac ].
 rename H into HL₁nz.
 remember HL₁ as HL₁₁; clear HeqHL₁₁.
 eapply hd_newton_segments in HL₁₁; try eassumption.
 remember HL₁₁ as HK₂; clear HeqHK₂.
 eapply next_pol_in_K_1_mq in HK₂; try eassumption; try reflexivity.
 remember HL₁₁ as H; clear HeqH.
 symmetry in Hr₁.
 eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
 rewrite H in HK₂; clear H.
 rewrite Pos.mul_1_r in HK₂.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 rewrite <- Hc₁.
 remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
 remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
 destruct (ps_zerop _ (ps_poly_nth 0 f₂)) as [H₁| H₁].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list, ps_monom; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Qnum_inv_Qnat_sub; [ | assumption ].
  rewrite Qden_inv_Qnat_sub; [ | assumption ].
  rewrite Z.mul_1_r, Nat.sub_0_r.
  rewrite Z.add_0_r.
  rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
  rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; try apply Pos2Z_ne_0.
  rewrite fold_series_const.
  symmetry in Hr₁.
  erewrite αj_m_eq_p_r; try eassumption; [ idtac | reflexivity ].
  rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; [ | assumption ].
  rewrite <- Z.mul_assoc.
  rewrite <- Zposnat2Znat; simpl; try eassumption.
  rewrite Z.div_mul; [ | apply Pos2Z_ne_0 ].
  remember (Pos.of_nat r) as pr.
  remember (Qden αj₁ * pr * Qden αk₁)%positive as x.
  rewrite ps_adjust_eq with (n := O) (k := x); symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
  unfold adjust_ps; simpl.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  do 2 rewrite Z.sub_0_r.
  rewrite Pos.mul_comm.
  apply mkps_morphism; [ | | reflexivity ].
   symmetry.
   rewrite <- series_stretch_const with (k := x); subst x.
   apply stretch_morph; [ reflexivity | ].
   constructor; intros i; simpl.
   unfold root_tail_series_from_cγ_list; simpl.
   rewrite <- Hc₁, <- Hf₂, <- HL₂.
   destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ contradiction | ].
   destruct i; [ reflexivity | simpl ].
   destruct (ps_zerop K (ps_poly_nth 0 f₂)); [ | contradiction ].
   reflexivity.

   subst x.
   rewrite Z.mul_shuffle0.
   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | ].
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc; symmetry.
   subst pr.
   rewrite Zposnat2Znat; [ | assumption ].
   eapply αj_m_eq_p_r; try eassumption; reflexivity.

  rename H₁ into Hnz₂.
  pose proof (Hrle 2%nat) as H.
  remember (S 0) as one in H; simpl in H.
  rewrite <- Hc, <- Hf₁, <- HL₁ in H.
  subst one; simpl in H.
  rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
  rename H into Hrle₂.
  remember (ac_root (Φq f₂ L₂)) as c₂ eqn:Hc₂ .
  remember (root_multiplicity acf c₂ (Φq f₂ L₂)) as r₂ eqn:Hr₂ .
  symmetry in Hr₁, Hr₂.
  remember HL₁₁ as H; clear HeqH.
  eapply next_ns_r_non_decr in H; try eassumption.
  destruct H as (Heq, H); move Heq at top; subst r₂.
  clear Hrle₂; destruct H as (αj₂, (αk₂, H)).
  destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
  remember HL as H; clear HeqH.
  eapply next_ns_in_f in H; try eassumption.
  rename H into HL₁i; move HL₁i before HL₁.
  unfold root_tail_from_cγ_list; simpl.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  unfold ps_terms_add; simpl.
  unfold ps_ordnum_add; simpl.
  rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
  rewrite Hαk₁, Hαk₂; simpl.
  rewrite Qnum_inv_Qnat_sub; [ | assumption ].
  rewrite Qden_inv_Qnat_sub; [ | assumption ].
  rewrite Nat.sub_0_r.
  do 2 rewrite Z.add_0_r, Z.mul_1_r.
  remember (Pos.of_nat r) as rq eqn:Hrq .
  remember (Qnum αj₁ * Zpos (Qden αk₁))%Z as nd.
  remember (Qden αj₁ * Qden αk₁ * rq)%positive as dd.
  rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
  do 3 rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; try apply Pos2Z_ne_0.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_shuffle0, Z.mul_assoc; simpl.
  remember HL₁i as H; clear HeqH.
  eapply next_ns_in_f in H; try eassumption.
  rename H into HL₂i; move HL₂i before HL₂.
  remember (nd * Zpos dd * Zpos m₁)%Z as x.
  remember (Qnum αj₂ * Zpos m₁ / Zpos (Qden αj₂ * rq))%Z as y.
  rename Heqy into Hy.
  assert (x <= x + y * Zpos  dd * Zpos dd)%Z as Hle.
   apply Z.le_sub_le_add_l.
   rewrite Z.sub_diag.
   subst y.
   apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
   apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg ].
   destruct (Qnum αj₂); simpl.
    rewrite Z.div_0_l; [ reflexivity | apply Pos2Z_ne_0 ].

    apply Z_div_pos_is_nonneg.

    apply Z.nle_gt in Hαj₂.
    exfalso; apply Hαj₂, Pos2Z.neg_is_nonpos.

   rewrite Z.min_l; [ | assumption ].
   rewrite Z.min_r; [ | assumption ].
   rewrite Z.sub_diag, Z.add_simpl_l; simpl.
   rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
   unfold adjust_ps; simpl.
   rewrite series_shift_0.
   rewrite Z.sub_0_r.
   apply mkps_morphism.
    erewrite αj_m_eq_p_r in Hy; try eassumption; [ subst rq | reflexivity ].
    rewrite <- Zposnat2Znat in Hy; [ simpl in Hy | assumption ].
    rewrite Pos.mul_comm, Pos2Z.inj_mul in Hy.
    rewrite <- Z.mul_assoc in Hy; simpl in Hy.
    rewrite Z.div_mul in Hy; [ | apply Pos2Z_ne_0 ].
    unfold adjust_series; simpl.
    rewrite series_shift_0.
    do 2 rewrite fold_series_const.
    do 2 rewrite series_stretch_const.
    rewrite series_mul_1_l.
    rewrite <- series_stretch_stretch.
    rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
    remember Hini₂ as H; clear HeqH.
    eapply p_is_pos with (m := m₁) in H; try eassumption.
    rewrite <- Hy in H.
    rename H into Hppos.
    remember Hppos as H; clear HeqH.
    apply Z.lt_le_incl in H.
    rewrite Z2Nat.inj_mul; [ simpl | assumption | apply Pos2Z.is_nonneg ].
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
      destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ contradiction | ].
      reflexivity.

      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list; simpl.
      rewrite <- Hc₁, <- Hf₂, <- HL₂.
      rewrite Hy in H₁.
      erewrite <- next_pow_eq_p in H₁; try eassumption.
      destruct i; [ exfalso; revert H₂; apply Nat.lt_irrefl | idtac ].
      clear H₂; simpl.
      destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [| H₂]; [ reflexivity | ].
      clear H₂.
      destruct (ps_zerop K (ps_poly_nth 0 f₂)) as [| H₂]; [ reflexivity | ].
      clear H₂.
      remember (next_pow 0 L₂ m₁) as p₂ eqn:Hp₂ .
      remember (Nat.compare p₂ (S i)) as cmp; symmetry in Heqcmp.
      destruct cmp; [ | | reflexivity ].
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
      apply Z2Nat.inj in H₁; [ | assumption | reflexivity ].
      rewrite H₁ in Hppos.
      exfalso; revert Hppos; apply Z.lt_irrefl.

      rewrite rng_add_0_l.
      remember (Z.to_nat y) as n₂.
      remember (i - n₂)%nat as id.
      unfold root_tail_series_from_cγ_list.
      clear H.
      symmetry in Hr₁.
      remember HL₁i as H; clear HeqH.
      eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
      rename H into Hq₁; move Hq₁ before HL₁nz.
      symmetry in Hr₂.
      remember HL₂i as H; clear HeqH.
      eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
      rename H into Hq₂; move Hq₂ before Hnz₂.
      assert (∀ n, r ≤ nth_r n f₁ L₁) as Hrle₁.
       eapply all_r_le_next with (f := f); eassumption.

       move Hrle₁ before Hrle.
       assert (∀ n, r ≤ nth_r n f₂ L₂) as Hrle₂.
        eapply all_r_le_next with (f := f₁); eassumption.

        move Hrle₂ before Hrle₁.
        rewrite find_coeff_iter_succ with (r := r); try eassumption;
          [ symmetry | symmetry; assumption | apply Nat.lt_succ_diag_r ].
        rewrite find_coeff_iter_succ with (r := r); try eassumption;
          [ symmetry | symmetry; assumption | apply Nat.lt_succ_diag_r ].
        subst x; clear Hle.
        remember (S i) as si.
        remember (S (S id)) as x; simpl; subst x.
        destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₄| H₄].
         contradiction.

         destruct i; [ exfalso; revert H₂; apply Nat.lt_irrefl | idtac ].
         rewrite <- Hc₁, <- Hf₂, <- HL₂; symmetry.
         rewrite <- find_coeff_add with (dp := n₂).
         rewrite Heqid.
         rewrite Nat.add_0_l, Nat.sub_add; [ | assumption ].
         rewrite <- Heqid.
         subst si; remember (S i) as si.
         rewrite Hy in Heqn₂.
         symmetry in Hr₂.
         erewrite <- next_pow_eq_p in Heqn₂; try eassumption.
         remember (S id) as sid.
         subst n₂; simpl.
         destruct (ps_zerop K (ps_poly_nth 0 f₂)) as [H₃| H₃].
          reflexivity.

          remember (next_pow 0 L₂ m₁) as pow₁ eqn:Hpow₁ .
          remember (Nat.compare pow₁ si) as cmp₁ eqn:Hcmp₁ .
          symmetry in Hcmp₁.
          destruct cmp₁; [ reflexivity | | reflexivity ].
          rewrite <- Hc₂.
          remember (next_pol f₂ (β L₂) (γ L₂) c₂) as f₃.
          remember (option_get phony_ns (newton_segments f₃)) as L₃.
          destruct (ps_zerop _ (ps_poly_nth 0 f₃)) as [H₅| H₅].
           subst si sid; simpl.
           destruct (ps_zerop _ (ps_poly_nth 0 f₃)) as [H₆| H₆].
            reflexivity.

            contradiction.

           rename H₅ into Hnz₃.
           replace pow₁ with (0 + pow₁)%nat by reflexivity.
           rewrite next_pow_add.
           apply Nat.add_cancel_r with (p := pow₁) in Heqid.
           rewrite Nat.sub_add in Heqid; [ | assumption ].
           rewrite <- Heqid.
           do 2 rewrite find_coeff_add.
           subst sid.
           remember HL₂i as H; clear HeqH.
           eapply next_ns_in_f in H; try eassumption.
           rename H into HL₃i.
           remember HL₂i as H; clear HeqH.
           symmetry in Hq₂.
           eapply next_pol_in_K_1_mq with (q := xH) in H; try eassumption.
           rewrite Pos.mul_1_r in H.
           rename H into HK₃.
           pose proof (Hrle₁ 2%nat) as H.
           remember (S 0) as one; simpl in H.
           rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
           subst one; simpl in H.
           rename Heqf₃ into Hf₃.
           rename HeqL₃ into HL₃.
           rewrite <- Hc₂, <- Hf₃, <- HL₃ in H.
           remember (ac_root (Φq f₃ L₃)) as c₃ eqn:Hc₃ .
           remember (root_multiplicity acf c₃ (Φq f₃ L₃)) as r₃ eqn:Hr₃ .
           rename H into Hrr.
           remember HL₂i as H; clear HeqH.
           symmetry in Hr₃.
           eapply next_ns_r_non_decr in H; try eassumption ; clear Hrr.
           destruct H as (Heq, H); move Heq at top; subst r₃.
           destruct H as (αj₃, (αk₃, H)).
           destruct H as (Hini₃, (Hfin₃, (Hαj₃, Hαk₃))).
           remember HL₃i as H; clear HeqH.
           symmetry in Hr₃.
           eapply q_eq_1_any_r in H; try eassumption; [ idtac | reflexivity ].
           rename H into Hq₃.
           assert (∀ n, r ≤ nth_r n f₃ L₃) as Hrle₃.
            eapply all_r_le_next with (f := f₂); eassumption.

            move Hrle₃ before Hrle₂.
            symmetry in Hr₃.
            eapply find_coeff_more_iter; try eassumption;
              [ apply Nat.lt_succ_diag_r | ].
            erewrite next_pow_eq_p in Hpow₁; try eassumption.
            rewrite <- Hy in Hpow₁.
            destruct pow₁.
             rewrite <- Z2Nat.inj_0 in Hpow₁.
             apply Z2Nat.inj in Hpow₁; [ idtac | reflexivity | idtac ].
              rewrite <- Hpow₁ in Hppos.
              exfalso; revert Hppos; apply Z.lt_irrefl.

              apply Z.lt_le_incl; assumption.

             rewrite Nat.add_succ_r, <- Nat.add_succ_l.
             apply Nat.le_sub_le_add_l.
             rewrite Nat.sub_diag; apply Nat.le_0_l.

    subst x.
    rewrite Z.mul_shuffle0, Pos2Z.inj_mul, Z.mul_assoc.
    apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | ].
    rewrite Z.mul_comm.
    rewrite <- Z.divide_div_mul_exact; [ | apply Pos2Z_ne_0 | ].
     rewrite Z.mul_comm.
     apply Z.div_mul, Pos2Z_ne_0.

     rewrite Heqdd, Heqnd.
     rewrite Pos_mul_mul_swap, Z.mul_shuffle0, Pos2Z.inj_mul.
     apply Z.mul_divide_mono_r.
     erewrite αj_m_eq_p_r with (L₁ := L₁); try eassumption; try reflexivity.
     rewrite Pos.mul_comm, Hrq.
     rewrite Pos2Z.inj_mul, Zposnat2Znat; [ | assumption ].
     exists (p_of_m m₁ (γ L₁)).
     rewrite Z.mul_assoc; reflexivity.

    rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.
Qed.

Theorem not_zero_1st_prop : ∀ f L b,
  zerop_1st_n_const_coeff b (nth_pol 1 f L) (nth_ns 1 f L) = false
  → (ps_poly_nth 0 f ≠ 0)%ps
  → (∀ i, i ≤ S b → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps).
Proof.
intros f L b Hpsi Hnz.
apply zerop_1st_n_const_coeff_false_iff.
rewrite zerop_1st_n_const_coeff_succ.
rewrite Hpsi, Bool.orb_false_r; simpl.
destruct (ps_zerop K (ps_poly_nth 0 f)); [ contradiction | ].
reflexivity.
Qed.

Theorem nth_in_newton_segments_any_r : ∀ f₁ L₁ c₁ fn Ln n,
  newton_segments f₁ = Some L₁
  → c₁ = ac_root (Φq f₁ L₁)
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i f₁ L₁) ≠ 0)%ps)
  → fn = nth_pol n f₁ L₁
  → Ln = nth_ns n f₁ L₁
  → newton_segments fn = Some Ln.
Proof.
intros f₁ L₁ c₁ fn Ln n HL₁ Hc₁ Hpsi Hfn HLn.
subst fn Ln.
pose proof (exists_pol_ord K f₁) as H.
destruct H as (m, (Hm, Hp)); clear Hm.
revert f₁ L₁ c₁ m HL₁ Hp Hc₁ Hpsi.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
assert (1 ≤ S n) as H₁ by apply le_n_S, Nat.le_0_l.
apply Hpsi in H₁; simpl in H₁.
rewrite <- Hc₁, <- Hf₂ in H₁.
remember (q_of_m m (γ L₁)) as q₀ eqn:Hq₀ .
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
eapply IHn with (m := (m * q₀)%positive); try eassumption; try reflexivity.
 eapply next_ns_in_f; eassumption.

 eapply next_pol_in_K_1_mq; eassumption.

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hpsi in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hf₂, <- HL₂ in Hin.
 assumption.
Qed.

Theorem nth_pol_in_K_1_m : ∀ f L c αj αk fn m n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c = ac_root (Φq f L)
  → ini_pt L = (0%nat, αj)
  → fin_pt L = (r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → root_multiplicity acf c (Φq f L) = r
  → (∀ n, r ≤ nth_r n f L)
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
  → fn = nth_pol n f L
  → pol_in_K_1_m fn m.
Proof.
intros f L c αj αk fn m n r.
intros HL HK Hc Hini Hfin Hαj Hαk Hr Hrle Hpsi Hfn.
eapply first_n_pol_in_K_1_m_any_r; try eassumption.
symmetry in Hr.
eapply q_eq_1_any_r; try eassumption.
reflexivity.
Qed.

Theorem all_L_in_newton_segments : ∀ f L b r,
  newton_segments f = Some L
  → zerop_1st_n_const_coeff b f L = false
  → nth_r 0 f L = r
  → (∀ i, r ≤ nth_r i f L)
  → ∀ n : nat, n ≤ b
  → newton_segments (nth_pol n f L) = Some (nth_ns n f L).
Proof.
intros f L b r HL Hz Hr Hri n Hnb.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
revert f L n HL Hz Hr Hri Hnb.
induction b; intros; [ apply Nat.le_0_r in Hnb; subst n; assumption | ].
destruct n; [ assumption | ].
apply le_S_n in Hnb; simpl.
remember (ac_root (Φq f L)) as c eqn:Hc .
remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
apply IHb; try assumption.
 eapply nth_in_newton_segments_any_r with (n := 1%nat); try eassumption.
  intros i Hi1.
  apply Hz.
  transitivity 1%nat; [ assumption | apply le_n_S, Nat.le_0_l ].

  simpl; rewrite <- Hc; assumption.

  simpl; rewrite <- Hc, <- Hf₁; assumption.

 intros i Hib.
 apply Nat.succ_le_mono in Hib.
 apply Hz in Hib; simpl in Hib.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hib; assumption.

 simpl in Hr; rewrite <- Hc in Hr.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 remember (root_multiplicity acf c₁ (Φq f₁ L₁)) as r₁ eqn:Hr₁ .
 remember HL as H; clear HeqH.
 symmetry in Hr₁.
 eapply next_ns_r_non_decr in H; try eassumption.
  destruct H as (H, _); move H at top; subst r₁.
  simpl; rewrite <- Hc₁; assumption.

  clear H.
  assert (1 ≤ S b)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hz in H; simpl in H.
  rewrite <- Hc, <- Hf₁ in H; assumption.

  clear H.
  pose proof (Hri 1%nat) as H; simpl in H.
  rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁, Hr₁ in H; assumption.

 intros i.
 pose proof (Hri (S i)) as H; simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁ in H; assumption.
Qed.

Theorem nth_r_add : ∀ f L i j,
  nth_r (i + j) f L = nth_r i (nth_pol j f L) (nth_ns j f L).
Proof.
intros f L i j.
revert f L j.
induction i; intros.
 simpl.
 apply nth_r_n; [ reflexivity | reflexivity | symmetry ].
 apply nth_c_n; reflexivity.

 rewrite Nat.add_succ_l, <- Nat.add_succ_r; simpl.
 rewrite IHi; simpl.
 f_equal; [ eapply nth_pol_n; reflexivity | idtac ].
 eapply nth_ns_n; try eassumption; reflexivity.
Qed.

Theorem non_decr_imp_eq : ∀ f L b r,
  newton_segments f = Some L
  → zerop_1st_n_const_coeff b f L = false
  → nth_r 0 f L = r
  → (∀ i, r ≤ nth_r i f L)
  → ∀ n : nat, n ≤ b → nth_r n f L = r.
Proof.
intros f L b r HL Hz Hr Hri n Hnb.
revert f L n HL Hz Hr Hri Hnb.
induction b; intros; [ apply Nat.le_0_r in Hnb; subst n; assumption | ].
destruct n; [ assumption | ].
apply le_S_n in Hnb.
remember Hz as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_succ2 in H.
apply orb_false_iff in H.
destruct H as (Hz₁, _).
remember HL as H; clear HeqH.
eapply all_L_in_newton_segments in H; try eassumption.
rename H into HLni.
remember (nth_ns n f L) as Ln eqn:HLn .
remember (nth_pol n f L) as fn eqn:Hfn .
remember (ac_root (Φq fn Ln)) as cn eqn:Hcn .
remember (next_pol fn (β Ln) (γ Ln) cn) as fn₁ eqn:Hfn₁ .
remember (option_get phony_ns (newton_segments fn₁)) as Ln₁ eqn:HLn₁ .
remember (ac_root (Φq fn₁ Ln₁)) as cn₁ eqn:Hcn₁ .
remember (nth_r (S n) f L) as r₁ eqn:Hr₁ .
remember Hnb as H; clear HeqH.
symmetry in Hr₁.
apply Nat.succ_le_mono in H.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
apply Hz in H.
erewrite nth_pol_succ in H; try eassumption; try reflexivity.
erewrite nth_c_n in H; try eassumption.
rewrite <- Hcn, <- Hfn₁ in H.
rename H into Hnzn₁.
remember HL as H; clear HeqH.
eapply IHb in H; try eassumption.
rename H into Hrn.
remember Hcn as H; clear HeqH.
erewrite <- nth_c_n in H; try eassumption.
rename H into Hcnn.
remember HLni as H; clear HeqH.
eapply next_ns_r_non_decr with (r := r) (r₁ := r₁) in H; try eassumption.
 destruct H; symmetry; assumption.

 erewrite <- nth_r_n; try eassumption.

 symmetry; clear H.
 remember Hfn as H; clear HeqH.
 eapply nth_pol_succ in H; try eassumption.
 rewrite <- Hfn₁ in H.
 symmetry in H.
 rename H into Hfn₁₁.
 remember Hfn₁₁ as H; clear HeqH.
 eapply nth_ns_succ in H; try eassumption.
 rewrite <- HLn₁ in H.
 symmetry in H.
 rename H into HLn₁₁.
 erewrite nth_r_n in Hr₁; try eassumption; [ symmetry; eassumption | ].
 erewrite nth_c_n; try eassumption.

 rewrite <- Hr₁; apply Hri.
Qed.

Theorem zerop_1st_n_const_coeff_false_succ : ∀ f L n,
  (ps_poly_nth 0 f ≠ 0)%ps
  → zerop_1st_n_const_coeff n (nth_pol 1 f L) (nth_ns 1 f L) = false
  ↔ zerop_1st_n_const_coeff (S n) f L = false.
Proof.
intros f L n Hnz.
split; intros H.
 apply zerop_1st_n_const_coeff_false_iff.
 apply not_zero_1st_prop; assumption.

 simpl in H.
 destruct (ps_zerop K (ps_poly_nth 0 f)); [ contradiction | ].
 assumption.
Qed.

Theorem f₁_in_K_1_mq₀ : ∀ f L f₁ m,
  pol_in_K_1_m f m
  → newton_segments f = Some L
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → pol_in_K_1_m f₁ (m * q_of_m m (γ L)).
Proof.
intros f L f₁ m Hm HL Hf₁.
eapply next_pol_in_K_1_mq in HL; try eassumption; reflexivity.
Qed.

Theorem multiplicity_pos : ∀ f L r,
  (∀ i : nat, i ≤ 1 → nth_r i f L = r)
  → newton_segments f = Some L
  → (0 < r)%nat.
Proof.
intros f L r Hri HL.
eapply multiplicity_is_pos; try eassumption; [ reflexivity | ].
pose proof (Hri O Nat.le_0_1) as H; simpl in H.
assumption.
Qed.

Theorem not_zerop_imp_in_newton_segment : ∀ f L f₁ L₁ r b,
  newton_segments f = Some L
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i : nat, i ≤ 1 → nth_r i f L = r)
  → (∀ n : nat, r ≤ nth_r n f L)
  → zerop_1st_n_const_coeff (S b) f₁ L₁ = false
  → ∀ n, n ≤ S b
  → newton_segments (nth_pol n f₁ L₁) = Some (nth_ns n f₁ L₁).
Proof.
intros f L f₁ L₁ r b HL Hf₁ HL₁ Hri Hrle Hz₁.
remember (ac_root (Φq f L)) as c eqn:Hc.
apply all_L_in_newton_segments with (r := r); try assumption.
 eapply next_ns_in_f; try eassumption.
 rewrite zerop_1st_n_const_coeff_succ in Hz₁.
 apply Bool.orb_false_iff in Hz₁.
 destruct Hz₁ as (Hz₁, Hpsi).
 simpl in Hz₁.
 remember (ps_poly_nth 0 f₁) as y.
 destruct (ps_zerop K y) as [| Hnz₁]; [ discriminate Hz₁ | subst y ].
 assumption.

 pose proof (Hri 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁ in H; assumption.

 intros i.
 pose proof (Hrle (S i)) as H; simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁ in H; assumption.
Qed.

Theorem not_zerop_imp_nth_r_eq_r : ∀ f L f₁ L₁ r b,
  newton_segments f = Some L
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → (∀ i : nat, i ≤ 1 → nth_r i f L = r)
  → zerop_1st_n_const_coeff b (nth_pol 1 f₁ L₁) (nth_ns 1 f₁ L₁) = false
  → (∀ n : nat, r ≤ nth_r n f L)
  → ∀ n : nat, n ≤ S b → nth_r n f₁ L₁ = r.
Proof.
intros f L f₁ L₁ r b HL Hf₁ HL₁ Hnz₁ Hri Hpsi Hrle.
apply non_decr_imp_eq; try eassumption.
 eapply next_ns_in_f; try eassumption; reflexivity.

 apply zerop_1st_n_const_coeff_false_succ; assumption.

 pose proof (Hri 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rewrite <- Hf₁, <- HL₁ in H; assumption.

 intros i.
 pose proof (Hrle (S i)) as H; simpl in H.
 rewrite <- Hf₁, <- HL₁ in H; assumption.
Qed.

Theorem nth_root_tail_const : ∀ f L f₁ L₁ n fn Ln fn₁ Ln₁ c m,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → fn = nth_pol n f L
  → Ln = nth_ns n f L
  → (ps_poly_nth 0 fn ≠ 0)%ps
  → fn₁ = nth_pol n f₁ L₁
  → Ln₁ = nth_ns n f₁ L₁
  → (ps_poly_nth 0 fn₁ = 0)%ps
  → ({| terms := root_tail_series_from_cγ_list m fn Ln |} =
     series_const (nth_c n f L))%ser.
Proof.
intros f₁ L₁ f₂ L₂ b₁ fb₂ Lb₂ fb₁ Lb₁ c₁ m₁.
intros Hc₁ Hf₂ HL₂ Hfb₂ HLb₂ Hpsib₁ Hfb₁ HLb₁ H₁.
constructor; intros i; simpl.
rename H₁ into Hzb₃.
destruct (zerop i) as [H₁| H₁].
 subst i; simpl.
 unfold root_tail_series_from_cγ_list; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 fb₂)) as [| H₁]; [ contradiction  |  ].
 erewrite nth_c_n; try eassumption; reflexivity.

 unfold root_tail_series_from_cγ_list; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 fb₂)) as [| H₂]; [ contradiction  |  ].
 destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl |  ].
 remember (ac_root (Φq fb₂ Lb₂)) as cb₂ eqn:Hcb₂ .
 erewrite <- nth_pol_n with (c := c₁); try eassumption.
 erewrite <- nth_ns_n with (c := c₁); try eassumption.
  simpl; rewrite <- Hfb₁.
  destruct (ps_zerop K (ps_poly_nth 0 fb₁)); [  | contradiction  ].
  reflexivity.

  eapply nth_pol_n with (c := c₁); eassumption.
Qed.

Theorem nth_root_tail_const_plus_tail :
  ∀ f f₁ L L₁ Lb Lb₁ b r fb fb₁ αjb₂ αkb₂ m,
  newton_segments f₁ = Some L₁
  → newton_segments fb = Some Lb
  → newton_segments fb₁ = Some Lb₁
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → fb = nth_pol b f L
  → fb₁ = next_pol fb (β Lb) (γ Lb) (ac_root (Φq fb Lb))
  → L₁ = nth_ns 1 f L
  → Lb = nth_ns b f L
  → Lb₁ = option_get phony_ns (newton_segments fb₁)
  → (ps_poly_nth 0 fb ≠ 0)%ps
  → (ps_poly_nth 0 fb₁ ≠ 0)%ps
  → (∀ n, r ≤ nth_r n fb Lb)
  → root_multiplicity acf (ac_root (Φq fb Lb)) (Φq fb Lb) = r
  → root_multiplicity acf (ac_root (Φq fb₁ Lb₁)) (Φq fb₁ Lb₁) = r
  → pol_in_K_1_m fb m
  → pol_in_K_1_m fb₁ m
  → ini_pt Lb = (0%nat, αjb₂)
  → fin_pt Lb = (r, αkb₂)
  → (0 < Qnum αjb₂)%Z
  → Qnum αkb₂ = 0%Z
  → (series (root_tail_series_from_cγ_list m fb Lb) =
     series_const (nth_c b f L) +
     series_shift (Z.to_nat (p_of_m m (γ Lb₁)))
       (series (root_tail_series_from_cγ_list m fb₁ Lb₁)))%ser.
Proof.
intros f f₁ L L₁ Lb Lb₁ b r fb fb₁ αjb αkb m.
intros HL₁i HLbi HLb₁i Hf₁ Hfb Hfb₁n.
intros HL₁ HLb HLb₁₁ Hpsib Hpsib₁ Hrle Hrb Hrb₁ HKb HKb₁.
intros Hinib Hfinb Hαjb Hαkb.
simpl in HL₁; rewrite <- Hf₁ in HL₁.
remember (ac_root (Φq f L)) as c₁ eqn:Hc₁.
remember (ac_root (Φq fb₁ Lb₁)) as cb₃ eqn:Hcb₃.
remember (p_of_m m (γ Lb)) as pb₂ eqn:Hpb₂.
remember (p_of_m m (γ Lb₁)) as pb₃ eqn:Hpb₃.
assert (Hfb₁ : fb₁ = nth_pol b f₁ L₁).
 rewrite Hfb₁n.
 symmetry.
 destruct b.
  simpl in Hfb, HLb; simpl.
  subst fb Lb c₁; assumption.

  apply nth_pol_succ.
   subst fb; simpl.
   rewrite <- Hc₁, <- Hf₁, <- HL₁; reflexivity.

   subst Lb; simpl.
   rewrite <- Hc₁, <- Hf₁, <- HL₁; reflexivity.

   symmetry.
   apply nth_c_n.
    subst fb; simpl.
    rewrite <- Hc₁, <- Hf₁, <- HL₁; reflexivity.

    subst Lb; simpl.
    rewrite <- Hc₁, <- Hf₁, <- HL₁; reflexivity.

 generalize HLbi; intros H.
 eapply next_ns_r_non_decr in H; try eassumption; try reflexivity.
 destruct H as (_, H).
 destruct H as (αjb₃, (αkb₃, H)).
 destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
 assert (Hpb₃pos : (0 < pb₃)%Z).
  subst pb₃.
  eapply p_is_pos; try eassumption.
  eapply multiplicity_is_pos; eassumption.

  constructor; simpl; intros i.
  destruct (zerop i) as [H₁| H₁].
   subst i; simpl.
   destruct (lt_dec 0 (Z.to_nat pb₃)) as [H₁| H₁].
    rewrite rng_add_0_r.
    unfold root_tail_series_from_cγ_list; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 fb)) as [H₃| H₃].
     contradiction .

     clear H₃; symmetry.
     erewrite nth_c_n; try eassumption; reflexivity.

    apply Nat.nlt_ge in H₁.
    apply Nat.le_0_r in H₁.
    rewrite <- Z2Nat.inj_0 in H₁.
    apply Z2Nat.inj in H₁.
     rewrite H₁ in Hpb₃pos.
     exfalso; revert Hpb₃pos; apply Z.lt_irrefl.

     apply Z.lt_le_incl; assumption.

     reflexivity.

   rewrite rng_add_0_l.
   destruct (lt_dec i (Z.to_nat pb₃)) as [H₂| H₂].
    unfold root_tail_series_from_cγ_list; simpl.
    destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl |  ].
    clear H₁.
    rewrite <- Hfb₁n, <- HLb₁₁.
    destruct (ps_zerop K (ps_poly_nth 0 fb)) as [| H₁]; [ reflexivity | ].
    simpl.
    destruct (ps_zerop K (ps_poly_nth 0 fb₁)) as [| H₃]; [ reflexivity | ].
    clear H₁ H₃.
    erewrite next_pow_eq_p; try eassumption.
     rewrite <- Hpb₃.
     remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp eqn:Hcmp .
     symmetry in Hcmp.
     destruct cmp; [ | | reflexivity ].
      apply nat_compare_eq in Hcmp.
      rewrite Hcmp in H₂.
      exfalso; revert H₂; apply Nat.lt_irrefl.

      apply nat_compare_lt in Hcmp.
      eapply Nat.lt_trans in H₂; eauto with Arith.
      exfalso; revert H₂; apply Nat.lt_irrefl.

     eapply multiplicity_is_pos; [ apply HLbi | reflexivity | assumption ].

    apply Nat.nlt_ge in H₂.
    remember (i - Z.to_nat pb₃)%nat as id.
    unfold root_tail_series_from_cγ_list.
    remember Hinib as H; clear HeqH.
    symmetry in Hrb.
    eapply q_eq_1_any_r in H; try eassumption; try reflexivity.
    rename H into Hqb₂.
    remember Hinib₃ as H; clear HeqH.
    symmetry in Hrb₁.
    eapply q_eq_1_any_r in H; try eassumption; try reflexivity.
    rename H into Hqb₃.
    rewrite find_coeff_iter_succ with (r := r); auto with Arith; symmetry.
    rewrite Hcb₃ in Hrb₁.
    rewrite find_coeff_iter_succ with (r := r); auto with Arith.
     symmetry.
     remember (S i) as si.
     remember (S (S id)) as ssid; simpl.
     destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl |  ].
     clear H₁.
     destruct (ps_zerop K (ps_poly_nth 0 fb)); [ contradiction  |  ].
     erewrite <- nth_pol_n with (c := c₁); eauto with Arith.
     rewrite <- Hfb₁, <- HLb₁₁.
     rewrite <- Hcb₃ in Hrb₁.
     symmetry in Hrb₁.
     erewrite next_pow_eq_p; try eassumption.
      rewrite <- Hpb₃.
      subst si ssid.
      remember (S i) as si.
      remember (S id) as sid; simpl.
      destruct (ps_zerop K (ps_poly_nth 0 fb₁)) as [| H₁]; auto with Arith.
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
        contradiction .

        rewrite <- Hcb₃.
        remember (next_pol fb₁ (β Lb₁) (γ Lb₁) cb₃) as fb₄.
        remember (option_get phony_ns (newton_segments fb₄)) as Lb₄.
        rename Heqfb₄ into Hfb₄.
        rename HeqLb₄ into HLb₄.
        subst sid.
        remember (Z.to_nat pb₃) as x.
        replace x with (0 + x)%nat by reflexivity.
        rewrite next_pow_add.
        replace (S i)%nat with (S i - x + x)%nat  at 2
         by (apply Nat.sub_add; assumption).
        rewrite find_coeff_add.
        rewrite <- Heqid.
        symmetry.
        destruct (ps_zerop K (ps_poly_nth 0 fb₄)) as [H₁| H₁].
         remember (S id) as sid; simpl.
         destruct (ps_zerop K (ps_poly_nth 0 fb₄)) as [H₃| H₃].
          reflexivity.

          contradiction .

         remember Hinib as H; clear HeqH.
         eapply p_is_pos with (m := m) in H; eauto with Arith.
          rewrite <- Hpb₂ in H.
          rename H into Hpb₂pos.
          remember HLb₁i as H; clear HeqH.
          eapply next_ns_in_f in H; eauto with Arith.
          rename H into HLb₄i.
          remember HLb₁i as H; clear HeqH.
          eapply nth_pol_in_K_1_m with (n := 1%nat) in H; eauto with Arith.
           simpl in H.
           rewrite <- Hcb₃, <- Hfb₄ in H.
           rename H into HK₄.
           remember HLb₁i as H; clear HeqH.
           eapply q_eq_1_r_non_decr in H; eauto with Arith.
            rename H into Hqb₄.
            remember (ac_root (Φq fb₄ Lb₄)) as cb₄ eqn:Hcb₄ .
            remember (root_multiplicity acf cb₄ (Φq fb₄ Lb₄)) as r₁
             eqn:Hrb₄ .
            symmetry in Hrb₄.
            pose proof (Hrle 2%nat) as H.
            remember (S 0) as one in H; simpl in H.
            erewrite <- nth_pol_n with (c := c₁) in H; eauto with Arith.
            rewrite <- Hfb₁, <- HLb₁₁ in H.
            subst one; simpl in H.
            rewrite <- Hcb₃, <- Hfb₄, <- HLb₄, <- Hcb₄ in H.
            rewrite Hrb₄ in H.
            rename H into Hrr.
            eapply find_coeff_more_iter with (r := r); eauto with Arith.
             remember HLb₁i as H; clear HeqH.
             eapply next_ns_r_non_decr in H; eauto with Arith.
             destruct H as (HH, H); move H₁ at top; subst r₁.
             symmetry; assumption.

             intros j.
             pose proof (Hrle (j + 2)%nat) as H.
             rewrite nth_r_add in H.
             remember (S 0) as one in H; simpl in H.
             erewrite <- nth_pol_n with (c := c₁) in H; eauto with Arith.
             rewrite <- Hfb₁, <- HLb₁₁ in H.
             subst one; simpl in H.
             rewrite <- Hcb₃, <- Hfb₄, <- HLb₄ in H.
             assumption.

             subst x.
             apply Z2Nat.inj_lt in Hpb₃pos; try eassumption.
              rewrite Heqid.
              apply le_n_S.
              apply Nat.le_sub_le_add_l.
              apply Nat.le_sub_le_add_r.
              rewrite Nat_sub_succ_diag.
              assumption.

              reflexivity.

              apply Z.lt_le_incl; assumption.

            intros j; clear H.
            pose proof (Hrle (j + 1)%nat) as H.
            rewrite nth_r_add in H; simpl in H.
            erewrite <- nth_pol_n with (c := c₁) in H; try eassumption.
             rewrite <- Hfb₁, <- HLb₁₁ in H.
             assumption.

             reflexivity.

           intros j; clear H.
           pose proof (Hrle (j + 1)%nat) as H.
           rewrite nth_r_add in H; simpl in H.
           erewrite <- nth_pol_n with (c := c₁) in H; try eassumption.
            rewrite <- Hfb₁, <- HLb₁₁ in H; assumption.

            reflexivity.

           intros j Hj.
           destruct j; [ assumption | simpl ].
           apply le_S_n in Hj.
           rewrite Nat.le_0_r in Hj; subst j.
           rewrite <- Hcb₃, <- Hfb₄, <- HLb₄.
           assumption.

          eapply multiplicity_is_pos; [ apply HLbi | reflexivity |  ].
          symmetry; assumption.

       apply nat_compare_gt, Nat.nle_gt in Hcmp₁.
       contradiction .

      eapply multiplicity_is_pos; [ apply HLbi | reflexivity |  ].
      symmetry; eassumption.

     intros j.
     pose proof (Hrle (j + 1)%nat) as H.
     rewrite nth_r_add in H; simpl in H.
     erewrite <- nth_pol_n with (c := c₁) in H; try eassumption.
      rewrite <- Hfb₁, <- HLb₁₁ in H; assumption.

      reflexivity.
Qed.

Theorem root_tail_from_0_const_r : ∀ f L c f₁ L₁ c₁ m q₀ b r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → c₁ = ac_root (Φq f₁ L₁)
  → (∀ i, i ≤ 1%nat → nth_r i f L = r)
  → (∀ n, r ≤ nth_r n f L)
  → (root_tail (m * q₀) b f₁ L₁ =
     root_head b 0 f₁ L₁ +
       ps_monom 1%K (γ_sum b 0 f₁ L₁) *
       root_tail (m * q₀) (S b) f₁ L₁)%ps.
Proof.
intros f L c f₁ L₁ c₁ m q₀ b r.
intros HL Hm Hq₀ Hc Hf₁ HL₁ Hc₁ Hri Hrle.
destruct b; [ eapply root_tail_split_1st_any_r; eassumption |  ].
remember (zerop_1st_n_const_coeff (S b) f₁ L₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 unfold root_tail, root_head.
 rewrite Hz₁.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁; simpl.
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
 remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
 assert
  (Hain :
   ∀ n, n ≤ S b
   → newton_segments (nth_pol n f₁ L₁) = Some (nth_ns n f₁ L₁)).
  subst c; eapply not_zerop_imp_in_newton_segment; eassumption.

  rewrite zerop_1st_n_const_coeff_succ in Hz₁.
  apply Bool.orb_false_iff in Hz₁.
  destruct Hz₁ as (Hz₁, Hpsi).
  simpl in Hz₁.
  remember (ps_poly_nth 0 f₁) as y.
  destruct (ps_zerop K y) as [| Hnz₁]; [ discriminate Hz₁ | subst y ].
  clear Hz₁.
  assert (Hreq : ∀ n, n ≤ S b → nth_r n f₁ L₁ = r).
   subst c; eapply not_zerop_imp_nth_r_eq_r; eassumption.

   assert (∀ i, i ≤ S b → (ps_poly_nth 0 (nth_pol i f₁ L₁) ≠ 0)%ps).
    apply not_zero_1st_prop; assumption.

    clear Hpsi; rename H into Hpsi.
    pose proof (Hpsi (S b) (Nat.le_refl (S b))) as H.
    rename H into Hpsib₁.
    remember (S b) as b₁ eqn:Hb₁ .
    remember (nth_ns b₁ f₁ L₁) as Lb eqn:HLb .
    remember (nth_pol b₁ f₁ L₁) as fb eqn:Hfb .
    pose proof (Hain b₁ (Nat.le_refl b₁)) as H.
    rewrite <- HLb, <- Hfb in H.
    rename H into HLbi.
    generalize Hf₁; intros H.
    eapply r_n_nth_ns with (r := r) in H; try eassumption.
     destruct H as (αjb₂, (αkb₂, H)).
     destruct H as (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂))).
     unfold root_tail, root_head.
     apply zerop_1st_n_const_coeff_false_iff in Hpsi.
     rewrite Hpsi.
     rewrite zerop_1st_n_const_coeff_succ2.
     rewrite Hpsi.
     rewrite zerop_1st_n_const_coeff_false_iff in Hpsi.
     simpl.
     rewrite <- Hc₁, <- Hf₂, <- HL₂.
     rewrite <- Hfb, <- HLb.
     rewrite Nat.add_0_r, rng_add_0_r.
     unfold root_tail_from_cγ_list, ps_monom; simpl.
     rewrite Nat.add_0_r, Z.mul_1_r, Z.add_0_r.
     rewrite Pos.mul_1_r.
     erewrite nth_γ_n; eauto with Arith; simpl.
     remember (nth_pol b₁ f₂ L₂) as fb₁ eqn:Hfb₁ .
     remember (nth_ns b₁ f₂ L₂) as Lb₁ eqn:HLb₁ .
     rewrite Hinib₂, Hfinb₂; simpl.
     rewrite Hαkb₂; simpl.
     rewrite Qnum_inv_Qnat_sub; [  | eapply multiplicity_pos; eassumption ].
     rewrite Qden_inv_Qnat_sub; [  | eapply multiplicity_pos; eassumption ].
     rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
     remember (m * q₀)%positive as m₁.
     rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
     rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; try eassumption; try apply Pos2Z_ne_0.
     generalize HL₁; intros H.
     eapply r_n_next_ns with (L := L) in H; try eassumption.
      destruct H as (αj₁, (αk₁, H)).
      destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
      assert (H : newton_segments f₁ = Some L₁).
       eapply next_ns_in_f with (f := f); eassumption.

       eapply nth_pol_in_K_1_m with (fn := fb) in H; eauto with Arith.
        rename H into HKb₂.
        pose proof (Hreq b₁ (Nat.le_refl b₁)) as H.
        erewrite nth_r_n in H; eauto with Arith.
        erewrite nth_c_n in H; eauto with Arith.
        rename H into Hrb₂.
        erewrite αj_m_eq_p_r with (f₁ := fb); eauto with Arith.

        rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto with Arith.
         rewrite <- Z.mul_assoc.
         rewrite <- Zposnat2Znat; simpl; try eassumption.
          rewrite Z.div_mul; auto with Arith.
          destruct (ps_zerop K (ps_poly_nth 0 fb₁)) as [H₁| H₁].
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
           erewrite αj_m_eq_p_r with (f₁ := fb); try eassumption; eauto with Arith.
           do 2 rewrite <- Z.mul_assoc.
           remember (Z.of_nat r * (Zpos (Qden αjb₂) * Zpos (Qden αkb₂)))%Z as x.
           rewrite Z.mul_comm, Z.mul_shuffle0 in Heqx.
           rewrite <- Zposnat2Znat in Heqx; auto with Arith.
            simpl in Heqx.
            rewrite <- Heqdd in Heqx; subst x.
            apply mkps_morphism; auto with Arith.
            apply series_stretch_iff_const.
            eapply nth_root_tail_const; eassumption.

            eapply multiplicity_pos; eassumption.

           do 2 rewrite fold_series_const.
           assert (H : 1 ≤ b₁) by (subst b₁; apply le_n_S, Nat.le_0_l).
           apply Hain in H; simpl in H.
           rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
           rename H into HL₂i.
           clear q₀ Hq₀ Heqm₁.
           clear Hpsi Hreq.
           clear αj₁ αk₁ Hαj₁ Hαk₁ Hini₁ Hfin₁.
           clear Hnz₁ Hm Hain Hb₁ b.
           assert (Hrle₁ : ∀ i, r ≤ nth_r i f₁ L₁).
            eapply all_r_le_next with (L := L); eassumption.

            clear Hrle Hf₁ HL₁ Hc.
            revert
             HL HL₂i HLbi Hf₂ Hfb Hfb₁ HL₂ HLb HLb₁ Hpsib₁
             H₁ Hrle₁ Hri Hrb₂ HKb₂ Hc₁ Hinib₂ Hfinb₂ Hαjb₂ Hαkb₂; 
             clear; intros.
            rename H₁ into Hnzb₃.
            remember HLb₁ as H; clear HeqH.
            erewrite nth_ns_n in H; eauto with Arith.
            erewrite <- nth_pol_n in H; eauto with Arith.
            rewrite <- Hfb₁ in H.
            rename H into HLb₁₁.
            remember Hfb₁ as H; clear HeqH.
            erewrite nth_pol_n in H; eauto with Arith.
            rename H into Hfb₁n.
            remember HLb₁₁ as H; clear HeqH.
            eapply next_ns_in_f with (f := fb) in H; eauto with Arith.
            rename H into HLb₁i.
            pose proof (Hrle₁ (S b₁)) as H; simpl in H.
            rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
            rename H into Hler₃.
            remember HLbi as H; clear HeqH.
            remember (ac_root (Φq fb₁ Lb₁)) as cb₃ eqn:Hcb₃ .
            remember (root_multiplicity acf cb₃ (Φq fb₁ Lb₁)) as rcb₃
             eqn:Hrcb₃ .
            symmetry in Hrcb₃.
            erewrite nth_r_n in Hler₃; eauto with Arith.
            erewrite nth_c_n in Hler₃; eauto with Arith.
            rewrite <- Hcb₃, Hrcb₃ in Hler₃.
            eapply next_ns_r_non_decr in H; eauto with Arith.
            destruct H as (H₁, H); move H₁ at top; subst rcb₃.
            destruct H as (αjb₃, (αkb₃, H)).
            destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
            rewrite Hinib₃, Hfinb₃; simpl.
            rewrite Hαkb₃; simpl.
            rewrite Qnum_inv_Qnat_sub;
             [  | eapply multiplicity_pos; eassumption ].
            rewrite Qden_inv_Qnat_sub;
             [  | eapply multiplicity_pos; eassumption ].
            rewrite Nat.sub_0_r.
            rewrite Z.add_0_r, Z.mul_1_r.
            remember (Qden αjb₂ * Pos.of_nat r * Qden αkb₂)%positive as dd.
            rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
            do 2 rewrite Pos2Z.inj_mul.
            rewrite Z.div_mul_cancel_r; simpl; auto with Arith.
            remember (Qnum αjb₂ * Zpos (Qden αkb₂))%Z as nd.
            assert (Hrle₂ : ∀ n, r ≤ nth_r n fb Lb).
             intros i.
             pose proof (Hrle₁ (i + b₁)%nat) as H.
             rewrite nth_r_add in H.
             rewrite <- Hfb, <- HLb in H; assumption.

             remember HLbi as H; clear HeqH.
             eapply nth_pol_in_K_1_m with (n := 1%nat) in H; eauto with Arith.
              rename H into HKb₃.
              erewrite αj_m_eq_p_r with (f₁ := fb₁); try eassumption;
               eauto with Arith.
              rewrite Z.mul_shuffle0.
              rewrite <- Zposnat2Znat; auto with Arith.
               rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
               rewrite Z.div_mul; auto with Arith.
               unfold ps_add, ps_mul; simpl.
               unfold cm; simpl.
               unfold ps_terms_add; simpl.
               unfold ps_ordnum_add; simpl.
               rewrite Z.mul_add_distr_r.
               rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
               remember (nd * Zpos m₁ * Zpos dd)%Z as x.
               remember (p_of_m m₁ (γ Lb₁)) as pb₃ eqn:Hpb₃ .
               remember Hinib₃ as H; clear HeqH.
               eapply p_is_pos with (m := m₁) in H; eauto with Arith.
                rewrite <- Hpb₃ in H.
                rename H into Hpb₃pos.
                assert (Hle : (x <= x + pb₃ * Zpos dd * Zpos dd)%Z).
                 apply Z.le_sub_le_add_l.
                 rewrite Z.sub_diag.
                 apply Z.mul_nonneg_nonneg; auto with Arith.
                 apply Z.mul_nonneg_nonneg; auto with Arith.

                 apply Z.lt_le_incl; assumption.

                 rewrite Z.min_l; auto with Arith.
                 rewrite Z.min_r; auto with Arith.
                 rewrite Z.add_simpl_l, Z.sub_diag; simpl.
                 rewrite Pos.mul_assoc.
                 rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
                 unfold adjust_ps; simpl.
                 rewrite series_shift_0.
                 rewrite Z.sub_0_r.
                 subst nd x.
                 remember (Qnum αjb₂ * Zpos (Qden αkb₂) * Zpos m₁)%Z as x.
                 rewrite Z.mul_shuffle0 in Heqx; subst x.
                 erewrite αj_m_eq_p_r with (L₁ := Lb) (f₁ := fb);
                  eauto with Arith.
                 remember (p_of_m m₁ (γ Lb)) as pb₂ eqn:Hpb₂ .
                 remember (pb₂ * Z.of_nat r * Zpos (Qden αjb₂) * Zpos (Qden αkb₂))%Z as
                  x.
                 do 2 rewrite <- Z.mul_assoc in Heqx.
                 rewrite Z.mul_comm, Z.mul_assoc in Heqx.
                 remember (Z.of_nat r * Zpos (Qden αjb₂) * Zpos (Qden αkb₂))%Z as y
                  eqn:Hy .
                 rewrite Z.mul_comm in Heqx; subst x.
                 rewrite Z.mul_shuffle0, Z.mul_comm in Hy.
                 rewrite Z.mul_assoc in Hy.
                 rewrite <- Zposnat2Znat in Hy; auto with Arith.
                  simpl in Hy; rewrite <- Heqdd in Hy; subst y.
                  remember (m₁ * (dd * dd))%positive as x.
                  rewrite Pos.mul_comm in Heqx; subst x.
                  rewrite Pos2Z.inj_mul, Z.mul_assoc.
                  apply mkps_morphism; auto with Arith.
                  unfold adjust_series; simpl.
                  rewrite series_shift_0.
                  do 2 rewrite series_stretch_const.
                  rewrite series_mul_1_l.
                  rewrite <- series_stretch_stretch.
                  rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
                  rewrite Z2Nat.inj_mul; auto with Arith; simpl.
                  rewrite <- stretch_shift_series_distr.
                  rewrite <- series_stretch_const with
                    (k := (dd * dd)%positive).
                  rewrite <- series_stretch_add_distr.
                  apply stretch_morph; [ reflexivity |  ].
                  subst c₁ cb₃ pb₃ f₂.
                  eapply nth_root_tail_const_plus_tail with (L₁ := L₂);
                    try eassumption; reflexivity.

                  apply Z.lt_le_incl; assumption.

                  eapply multiplicity_pos; eassumption.

                eapply multiplicity_pos; eassumption.

               eapply multiplicity_pos; eassumption.

              intros j Hj.
              destruct j; [ assumption | simpl ].
              apply le_S_n in Hj.
              rewrite Nat.le_0_r in Hj; subst j; simpl.
              erewrite <- nth_pol_n with (c := c₁) (f₁ := f₂);
               try eassumption; [  | reflexivity ].
              rewrite <- Hfb₁; assumption.

          eapply multiplicity_pos; eassumption.

         eapply multiplicity_pos; eassumption.

        subst c m₁ q₀; eapply f₁_in_K_1_mq₀; try eassumption.

      intros n.
      pose proof (Hri 1%nat (Nat.le_refl 1)) as HH; simpl in HH.
      rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in HH.
      rewrite HH.
      eapply Nat.le_trans; [ apply Hrle with (n := S n) | simpl ].
      rewrite <- Hc, <- Hf₁, HL₁; apply Nat.le_refl.

      pose proof (Hri O Nat.le_0_1) as H₁; simpl in H₁.
      rewrite <- Hc in H₁; rewrite H₁.
      pose proof (Hreq O (Nat.le_0_l b₁)) as H₂; simpl in H₂.
      rewrite <- Hc₁ in H₂.
      symmetry; assumption.

      reflexivity.

     intros i Hib.
     destruct i; [ apply Hri, Nat.le_0_1 | simpl ].
     rewrite <- Hc, <- Hf₁, <- HL₁.
     apply Hreq, Nat.succ_le_mono, Hib.
Qed.

Theorem a₀_neq_0 : ∀ f L αj,
  newton_segments f = Some L
  → ini_pt L = (0%nat, αj)
  → (ps_poly_nth 0 f ≠ 0)%ps.
Proof.
intros f L αj HL Hini.
intros H₁.
unfold ps_poly_nth, ps_lap_nth in H₁.
remember HL as H; clear HeqH.
remember (List.nth 0 (al f) 0%ps) as jps eqn:Hjps .
eapply ord_coeff_non_zero_in_newt_segm with (hps := jps) in H; try eassumption.
 apply order_inf in H₁.
 unfold order in H₁; simpl in H₁.
 unfold order_coeff in H; simpl in H.
 remember (series_order (ps_terms jps) 0) as v eqn:Hv .
 destruct v as [v| ].
  discriminate H₁.

  exfalso; apply H; reflexivity.

 left; symmetry; try eassumption; eauto with Arith.
Qed.

Theorem zerop_1st_n_const_coeff_more : ∀ f L n,
  zerop_1st_n_const_coeff n f L = false
  → (ps_poly_nth 0 (nth_pol (S n) f L) ≠ 0)%ps
  → zerop_1st_n_const_coeff (S n) f L = false.
Proof.
intros f L n Hz Hn.
rewrite zerop_1st_n_const_coeff_succ2.
rewrite Hz, Bool.orb_false_l.
remember (S n) as sn; simpl; subst sn.
destruct (ps_zerop K (ps_poly_nth 0 (nth_pol (S n) f L))); auto with Arith.
contradiction.
Qed.

Theorem root_tail_sep_1st_monom : ∀ f L f₁ L₁ c m q₀ n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i f₁ L₁) ≠ 0)%ps)
  → (∀ j : nat, r ≤ nth_r j f₁ L₁)
  → (∀ i : nat, i ≤ S n → nth_r i f L = r)
  → zerop_1st_n_const_coeff (S n) f L = false
  → (root_tail (m * q₀) n f₁ L₁ =
     ps_monom (nth_c n f₁ L₁) (nth_γ n f₁ L₁) +
     ps_monom 1%K (nth_γ n f₁ L₁) * root_tail (m * q₀) (S n) f₁ L₁)%ps.
Proof.
intros f L f₁ L₁ c m q₀ n r.
intros HL Hm Hq₀ Hc Hf₁ HL₁ Hpsi₁ Hrle₁ Hri Hz.
remember Hz as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_succ in H.
apply Bool.orb_false_iff in H; simpl in H.
rewrite <- Hc, <- Hf₁, <- HL₁ in H.
destruct H as (H, Hz₁).
remember (ps_poly_nth 0 f) as x.
destruct (ps_zerop K x) as [Hnz| Hnz]; [ discriminate H | clear H ].
subst x.
remember (m * q₀)%positive as m₁.
remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
move Hc₁ before HL₁.
move c₁ before c.
pose proof (Hri 0%nat (Nat.le_0_l (S n))) as Hr₀; simpl in Hr₀.
assert (1 ≤ S n)%nat as Hr₁ by apply le_n_S, Nat.le_0_l.
apply Hri in Hr₁; simpl in Hr₁.
rewrite <- Hc in Hr₀.
rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in Hr₁.
assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; eauto with Arith).
pose proof (Hpsi₁ 0%nat (Nat.le_0_l n)) as H; simpl in H.
rename H into Hnz₁.
remember HL₁ as H; clear HeqH.
eapply r_n_next_ns in H; try eassumption.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember HL₁ as HL₁i; clear HeqHL₁i.
eapply hd_newton_segments in HL₁i; try eassumption.
remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
remember HL as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; try eassumption.
rewrite <- Heqm₁ in H.
rename H into HK₁; move HK₁ before HL₁i.
remember (nth_pol n f₁ L₁) as fn₁ eqn:Hfn₁ .
remember (nth_ns n f₁ L₁) as Ln₁ eqn:HLn₁ .
remember (ac_root (Φq fn₁ Ln₁)) as cn₁ eqn:Hcn₁ .
remember (nth_pol n f₂ L₂) as fn₂ eqn:Hfn₂ .
remember (nth_ns n f₂ L₂) as Ln₂ eqn:HLn₂ .
remember Hr₀ as H; clear HeqH.
erewrite <- nth_r_n with (n := O) in H; simpl; eauto with Arith.
rename H into Hr₀₁.
remember HL as H; clear HeqH.
eapply all_L_in_newton_segments with (n := S n) in H; eauto with Arith.
 erewrite nth_ns_succ2 in H; eauto with Arith.
 erewrite nth_pol_succ2 in H; eauto with Arith.
 rewrite <- HLn₁, <- Hfn₁ in H.
 rename H into HLn₁i; move HLn₁i before HLn₁.
 remember Hfn₂ as H; clear HeqH.
 erewrite nth_pol_n with (c := c₁) in H; eauto with Arith.
 rename H into Hfn₂₁; move Hfn₂₁ before Hfn₂.
 remember HL as H; clear HeqH.
 eapply r_n_nth_ns with (fn := fn₁) in H; try eassumption.
 destruct H as (αjn₁, (αkn₁, H)).
 destruct H as (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁))).
 remember HLn₁ as H; clear HeqH.
 erewrite nth_ns_n with (c := c) in H; eauto with Arith.
 erewrite <- nth_pol_n with (c := c) in H; try eassumption; eauto with Arith.
 rewrite <- Hfn₁ in H.
 rename H into HLn₁h.
 remember HLn₁h as H; clear HeqH.
 eapply newton_segments_not_nil in H; try eassumption.
 rename H into HL₁nz.
 pose proof (Hri (S n) (Nat.le_refl (S n))) as Hrn₁; simpl in Hrn₁.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hrn₁.
 erewrite nth_r_n in Hrn₁; try eassumption; auto with Arith.
 erewrite nth_c_n in Hrn₁; try eassumption.
 rewrite <- Hcn₁ in Hrn₁.
 remember HL₁i as H; clear HeqH.
 eapply nth_pol_in_K_1_m in H; try eassumption.
 rename H into HKn₁.
 remember (S n) as sn.
 unfold root_tail, ps_monom; simpl.
 do 2 rewrite fold_series_const.
 subst sn.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁.
 rewrite Bool.orb_false_l; simpl.
 rewrite <- Hc₁, <- Hf₂, <- HL₂.
 rewrite <- Hfn₂, <- HLn₂.
 rewrite <- Hfn₁, <- HLn₁.
 erewrite nth_c_n; try eassumption.
 rewrite <- Hcn₁.
 destruct (ps_zerop K (ps_poly_nth 0 fn₂)) as [H₂| H₂].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list; simpl.
  rewrite Hinin₁, Hfinn₁; simpl.
  rewrite Hαkn₁; simpl.
  rewrite Qnum_inv_Qnat_sub; [ | assumption ].
  rewrite Qden_inv_Qnat_sub; [ | assumption ].
  rewrite Z.mul_1_r, Z.add_0_r, Nat.sub_0_r.
  rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
  do 2 rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; simpl; auto with Arith.
  erewrite αj_m_eq_p_r with (L₁ := Ln₁); try eassumption; eauto with Arith.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_shuffle0, Zposnat2Znat; auto with Arith.
  rewrite <- Zposnat2Znat; auto with Arith.
  rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto with Arith.
  remember (Qden (nth_γ n f₁ L₁)) as d₁ eqn:Hd₁ .
  rewrite ps_adjust_eq with (n := O) (k := d₁); symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
  unfold adjust_ps; simpl.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  do 2 rewrite Z.sub_0_r.
  rewrite Pos.mul_comm.
  apply mkps_morphism; auto with Arith.
   rewrite <- series_stretch_const with (k := d₁).
   apply stretch_morph; auto with Arith.
   constructor; intros i; simpl.
   unfold root_tail_series_from_cγ_list; simpl.
   destruct (ps_zerop K (ps_poly_nth 0 fn₁)) as [H₁| H₁].
    exfalso; revert H₁.
    eapply a₀_neq_0; try eassumption.

    rewrite <- Hcn₁.
    erewrite <- nth_ns_n with (c := c₁); try eassumption; auto with Arith.
    erewrite <- nth_pol_n with (c := c₁); try eassumption.
    rewrite <- Hfn₂, <- HLn₂.
    destruct i; simpl; [ rewrite Hcn₁; eauto with Arith | idtac ].
    destruct (ps_zerop K (ps_poly_nth 0 fn₂)); auto with Arith; contradiction.

   subst d₁.
   erewrite nth_γ_n; try eassumption; simpl.
   rewrite Hαkn₁; simpl.
   rewrite Qnum_inv_Qnat_sub; [ | assumption ].
   rewrite Qden_inv_Qnat_sub; [ | assumption ].
   rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
   rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.mul_assoc.
   apply Z.mul_cancel_r; auto with Arith.
   erewrite αj_m_eq_p_r; try eassumption; eauto with Arith.
   rewrite Zposnat2Znat; auto with Arith.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   reflexivity.

  rename H₂ into Hnzn₂; move Hnzn₂ before HLn₂.
  remember Hfn₂ as H; clear HeqH.
  erewrite <- nth_pol_succ2 with (c := c₁) in H; try eassumption.
  rename H into Hfn₂₂; move Hfn₂₂ before Hfn₂₁.
  remember HLn₂ as H; clear HeqH.
  erewrite <- nth_ns_succ2 with (c := c₁) in H; try eassumption.
  rename H into HLn₂₁; move HLn₂₁ before HLn₂.
  remember Hpsi₁ as H; clear HeqH.
  apply zerop_1st_n_const_coeff_false_iff in H.
  remember Hnzn₂ as HH; clear HeqHH.
  rewrite Hfn₂₂ in HH.
  apply zerop_1st_n_const_coeff_more in H; auto with Arith; clear HH.
  rewrite zerop_1st_n_const_coeff_false_iff in H.
  clear Hpsi₁; rename H into Hpsi₁; move Hpsi₁ after Hri.
  assert (∀ i, i ≤ S (S n) → nth_r i f L = r) as H.
   apply non_decr_imp_eq; auto with Arith.
    rewrite zerop_1st_n_const_coeff_succ2, Hz.
    remember (S n) as sn; simpl.
    rewrite <- Hc, <- Hf₁, <- HL₁.
    subst sn; simpl.
    rewrite <- Hc₁, <- Hf₂, <- HL₂.
    remember (ps_poly_nth 0 (nth_pol n f₂ L₂)) as x.
    destruct (ps_zerop K x) as [H₁| ]; auto with Arith; subst x.
    pose proof (Hpsi₁ (S n) (Nat.le_refl (S n))) as H; simpl in H.
    rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
    contradiction.

    intros i.
    destruct i; [ rewrite Hr₀₁; auto with Arith | simpl ].
    rewrite <- Hc, <- Hf₁, <- HL₁.
    apply Hrle₁.

   clear Hri; rename H into Hri.
   remember HL as H; clear HeqH.
   eapply r_n_nth_ns with (fn := fn₂) (n := S n) in H; eauto with Arith.
   destruct H as (αjn₂, (αkn₂, H)).
   destruct H as (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂))).
   unfold ps_add, ps_mul; simpl.
   unfold cm; simpl.
   unfold ps_terms_add, ps_ordnum_add; simpl.
   unfold root_tail_from_cγ_list; simpl.
   erewrite nth_γ_n; try eassumption; simpl.
   rewrite Hinin₁, Hfinn₁, Hinin₂, Hfinn₂; simpl.
   rewrite Hαkn₁, Hαkn₂; simpl.
   rewrite Qnum_inv_Qnat_sub; [ | assumption ].
   rewrite Qden_inv_Qnat_sub; [ | assumption ].
   do 2 rewrite Z.add_0_r, Z.mul_1_r.
   rewrite Nat.sub_0_r.
   remember (Qnum αjn₁ * Zpos (Qden αkn₁))%Z as nd₁ eqn:Hnd₁ .
   remember (Qden αjn₁ * Qden αkn₁ * Pos.of_nat r)%positive as dd₁ eqn:Hdd₁ .
   remember (Qnum αjn₂ * Zpos (Qden αkn₂))%Z as nd₂ eqn:Hnd₂ .
   remember (Qden αjn₂ * Qden αkn₂ * Pos.of_nat r)%positive as dd₂ eqn:Hdd₂ .
   rewrite Z.mul_add_distr_r.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc.
   remember (nd₁ * Zpos m₁ * Zpos dd₁)%Z as x.
   remember (nd₂ * Zpos m₁ / Zpos dd₂ * Zpos dd₁ * Zpos dd₁)%Z as y.
   assert (x <= x + y)%Z as Hle; subst x y.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.mul_nonneg_nonneg; auto with Arith.
    apply Z.mul_nonneg_nonneg; auto with Arith.
    apply Z.div_pos; [ subst nd₂ | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto with Arith.
    apply Z.mul_nonneg_nonneg; auto with Arith.
    apply Z.lt_le_incl; auto with Arith.

    pose proof (Hpsi₁ n (Nat.le_succ_diag_r n)) as H.
    rewrite <- Hfn₁ in H.
    rename H into Hnzn₁; move Hnzn₁ before HLn₁.
    remember HLn₂ as H; clear HeqH.
    erewrite nth_ns_n with (c := c₁) in H; try eassumption.
    rename H into HLn₂h; move HLn₂h before Hαkn₂.
    remember HLn₂h as H; clear HeqH.
    eapply newton_segments_not_nil in H; try eassumption.
    rename H into HL₂nz; move HL₂nz before Hnzn₂.
    remember HLn₂h as H; clear HeqH.
    eapply hd_newton_segments in H; try eassumption.
    rename H into HLn₂i; move HLn₂i before HLn₂h.
    remember Hfn₂₂ as H; clear HeqH.
    eapply nth_pol_in_K_1_m in H; try eassumption.
    rename H into HKn₂; move HKn₂ before HLn₂i.
    remember (ac_root (Φq fn₂ Ln₂)) as cn₂ eqn:Hcn₂ .
    move Hcn₂ before HLn₂.
    pose proof (Hri (S (S n)) (Nat.le_refl (S (S n)))) as H.
    erewrite nth_r_succ2 in H; eauto with Arith.
    erewrite nth_r_n in H; try eassumption; eauto with Arith.
    erewrite nth_c_n in H; try eassumption; eauto with Arith.
    rewrite <- Hcn₂ in H.
    rename H into Hrn₂; move Hrn₂ after Hcn₂.
    rewrite Z.min_l; auto with Arith.
    rewrite Z.min_r; auto with Arith.
    rewrite Z.sub_diag; simpl.
    rewrite Z.add_simpl_l.
    unfold adjust_series at 1.
    rewrite series_shift_0, series_stretch_const.
    rewrite series_stretch_const, series_mul_1_l.
    rewrite Pos.mul_comm.
    rewrite ps_adjust_eq with (n := O) (k := (dd₁ * dd₁)%positive).
    unfold adjust_ps; simpl.
    rewrite series_shift_0, Z.sub_0_r, Pos.mul_assoc.
    apply mkps_morphism; auto with Arith.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     unfold adjust_series; simpl.
     rewrite <- series_stretch_stretch.
     rewrite Z2Nat_inj_mul_pos_r.
     rewrite <- stretch_shift_series_distr.
     rewrite <- series_stretch_const.
     rewrite <- series_stretch_add_distr.
     apply stretch_morph; auto with Arith.
     constructor; simpl; intros i.
     rewrite Hnd₂, Hdd₂.
     rewrite Z.mul_shuffle0, Pos_mul_mul_swap.
     rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto with Arith.
     erewrite αj_m_eq_p_r; try eassumption; eauto with Arith.
     rewrite <- Zposnat2Znat; try eassumption.
     rewrite Z.mul_shuffle0, <- Z.mul_assoc.
     rewrite <- Pos2Z.inj_mul.
     rewrite Z.div_mul; auto with Arith.
     remember (p_of_m m₁ (γ Ln₂)) as pn₂ eqn:Hpn₂ .
     destruct i.
      simpl.
      destruct (lt_dec 0 (Z.to_nat pn₂)) as [H₁| H₁].
       rewrite rng_add_0_r.
       unfold root_tail_series_from_cγ_list; simpl.
       destruct (ps_zerop K (ps_poly_nth 0 fn₁)) as [H₂| H₂].
        contradiction.

        rewrite Hcn₁; reflexivity.

       exfalso; apply H₁; rewrite Hpn₂.
       rewrite <- Z2Nat.inj_0.
       apply Z2Nat.inj_lt;
        [ reflexivity | idtac | eapply p_is_pos; try eassumption ].
       apply Z.lt_le_incl.
       eapply p_is_pos; try eassumption.

      remember minus as g; simpl; subst g.
      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list.
      remember (S i) as si.
      remember (si - Z.to_nat pn₂)%nat as id eqn:Hid .
      symmetry in Hid.
      destruct (lt_dec si (Z.to_nat pn₂)) as [H₁| H₁].
       simpl.
       destruct (ps_zerop K (ps_poly_nth 0 fn₁)) as [H₂| H₂].
        contradiction.

        clear H₂.
        rewrite <- Hcn₁.
        erewrite <- nth_pol_n with (c := c₁); try eassumption.
        rewrite <- Hfn₂.
        erewrite nth_pol_n with (c := c₁) in Hfn₂; try eassumption.
        erewrite <- nth_ns_n with (c := c₁) (n := n); try eassumption.
        erewrite <- nth_pol_n with (c := c₁) in Hfn₂; try eassumption.
        rewrite <- HLn₂.
        subst si; simpl.
        destruct (ps_zerop K (ps_poly_nth 0 fn₂)) as [H₂| H₂].
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
       remember HLn₁i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption; eauto with Arith.
       rename H into Hqn₁; move Hqn₁ before HKn₁.
       symmetry in Hrn₂.
       remember HLn₂i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption; eauto with Arith.
       rename H into Hqn₂; move Hqn₂ before HKn₂.
       symmetry in Hrn₁.
       rewrite Hcn₁ in Hrn₁.
       assert (∀ j, r ≤ nth_r j fn₁ Ln₁) as H.
        intros j.
        rewrite Hfn₁, HLn₁.
        rewrite <- nth_r_add.
        apply Hrle₁.

        rename H into Hrlen₁.
        move Hrlen₁ before Hrle₁.
        rewrite find_coeff_iter_succ with (r := r); auto with Arith.
        symmetry.
        rewrite Hcn₂ in Hrn₂.
        assert (∀ j, r ≤ nth_r j fn₂ Ln₂) as H.
         eapply all_r_le_next with (c := cn₁); eauto with Arith.

         rename H into Hrlen₂.
         move Hrlen₂ before Hrlen₁.
         rewrite find_coeff_iter_succ with (r := r); auto with Arith.
         symmetry.
         remember (S (S si)) as ssi.
         remember (S id) as sid; simpl.
         rewrite <- Hcn₂.
         remember (next_pol fn₂ (β Ln₂) (γ Ln₂) cn₂) as fn₃ eqn:Hfn₃ .
         remember (option_get phony_ns (newton_segments fn₃)) as Ln₃.
         rename HeqLn₃ into HLn₃h.
         destruct (ps_zerop K (ps_poly_nth 0 fn₂)) as [H₂| H₂].
          contradiction.

          clear H₂.
          destruct id.
           subst sid.
           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 fn₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption.
            rewrite <- Hfn₂.
            remember Hfn₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption.
            erewrite <- nth_ns_n with (c := c₁) (fn := fn₁);
             try eassumption.
            clear H.
            subst ssi; remember (S i) as si; simpl; subst si.
            rewrite <- HLn₂, <- Hcn₂, <- Hfn₃, <- HLn₃h.
            destruct (ps_zerop K (ps_poly_nth 0 fn₂)) as [H₂| H₂].
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
             destruct cmp₁; auto with Arith.
              apply nat_compare_lt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

              apply nat_compare_gt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop K (ps_poly_nth 0 fn₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption.
            rewrite <- Hfn₂.
            remember Hfn₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption.
            erewrite <- nth_ns_n with (c := c₁) (fn := fn₁); try eassumption.
            clear H.
            rewrite <- HLn₂.
            subst ssi; remember (S i) as si; simpl.
            rewrite <- Hcn₂, <- Hfn₃, <- HLn₃h.
            destruct (ps_zerop K (ps_poly_nth 0 fn₂)) as [H₂| H₂].
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
              replace (Z.to_nat pn₂) with (0 + Z.to_nat pn₂)%nat by auto with Arith.
              rewrite next_pow_add.
              apply Nat.add_sub_eq_nz in Hid.
               rewrite Nat.add_comm in Hid.
               rewrite <- Hid.
               rewrite find_coeff_add, Hid.
               subst si sid; symmetry.
               destruct (ps_zerop K (ps_poly_nth 0 fn₃)) as [H₂| H₂].
                remember (S id) as sid; simpl.
                destruct (ps_zerop K (ps_poly_nth 0 fn₃)) as [H₃| H₃].
                 reflexivity.

                 contradiction.

                rename H₂ into Hnzn₃; move Hnzn₃ before HLn₃h.
                remember HLn₂i as H; clear HeqH.
                eapply next_has_root_0_or_newton_segments in H; eauto with Arith.
                simpl in H.
                rewrite <- Hcn₂, <- Hfn₃ in H.
                destruct H as [| H]; [ contradiction | idtac ].
                rename H into HL₃nz; move HL₃nz before Hnzn₃.
                remember Hpsi₁ as H; clear HeqH.
                apply zerop_1st_n_const_coeff_false_iff in H.
                remember Hnzn₃ as HH; clear HeqHH.
                rewrite Hfn₃ in HH.
                erewrite <- nth_pol_n with (c := c₁) in HH; try eassumption.
                erewrite <- nth_pol_succ2 with (c := c₁) in HH;
                 try eassumption.
                apply zerop_1st_n_const_coeff_more in H; auto with Arith; clear HH.
                rewrite zerop_1st_n_const_coeff_false_iff in H.
                rename H into Hpsi; move Hpsi before Hri.
                remember HL₁i as H; clear HeqH.
                eapply nth_pol_in_K_1_m with (c := c₁) in H; eauto with Arith.
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
                subst sn.
                erewrite nth_pol_n with (c := c₁) in H; try eassumption.
                rewrite <- Hfn₃ in H.
                rename H into HKn₃; move HKn₃ before HL₃nz.
                assert (∀ i, i ≤ S (S (S n)) → nth_r i f L = r) as H.
                 apply non_decr_imp_eq; auto with Arith.
                  rewrite zerop_1st_n_const_coeff_succ2.
                  rewrite zerop_1st_n_const_coeff_succ2.
                  rewrite Hz.
                  remember (S (S n)) as sn; simpl.
                  rewrite <- Hc, <- Hf₁, <- HL₁.
                  subst sn; remember (S n) as sn; simpl.
                  rewrite <- Hc₁, <- Hf₂, <- HL₂.
                  rewrite <- Hc, <- Hf₁, <- HL₁.
                  subst sn; simpl.
                  rewrite <- Hc₁, <- Hf₂, <- HL₂.
                  remember (ps_poly_nth 0 (nth_pol n f₂ L₂)) as x.
                  destruct (ps_zerop K x) as [H₂| ]; auto with Arith; subst x.
                   pose proof (Hpsi₁ (S n) (Nat.le_refl (S n))) as H;
                    simpl in H.
                   rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
                   contradiction.

                   clear n0.
                   simpl.
                   erewrite <- nth_pol_succ2 with (L := L₂);
                    try eassumption; try reflexivity.
                   erewrite nth_pol_succ; try eassumption; try reflexivity.
                   erewrite nth_c_n; try eassumption.
                   rewrite <- Hcn₂, <- Hfn₃.
                   remember (ps_poly_nth 0 fn₃) as x.
                   destruct (ps_zerop K x) as [H₂| H₂]; auto with Arith; subst x.
                   contradiction.

                  intros j.
                  destruct j; [ rewrite Hr₀₁; auto | simpl ].
                  rewrite <- Hc, <- Hf₁, <- HL₁.
                  apply Hrle₁.

                 clear Hri; rename H into Hri.
                 remember HL as H; clear HeqH.
                 eapply r_n_nth_ns in H; try eassumption; try reflexivity.
                 remember (S n) as sn in H; simpl in H.
                 rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
                 subst sn.
                 erewrite nth_ns_n with (c := c₁) in H; try eassumption.
                 rewrite <- HLn₃h in H.
                 destruct H as (αjn₃, (αkn₃, H)).
                 destruct H as (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃))).
                 remember (ac_root (Φq fn₃ Ln₃)) as cn₃ eqn:Hcn₃ .
                 move Hcn₃ before HKn₃.
                 pose proof (Hri (S (S (S n))) (Nat.le_refl (S (S (S n)))))
                  as H.
                 remember (S (S n)) as sn in H; simpl in H.
                 rewrite <- Hc, <- Hf₁, <- HL₁ in H.
                 subst sn; remember (S n) as sn in H; simpl in H.
                 rewrite <- Hc₁, <- Hf₂, <- HL₂ in H.
                 subst sn.
                 erewrite nth_r_n in H; try eassumption; eauto with Arith.
                 erewrite nth_c_n in H; try eassumption; eauto with Arith.
                 erewrite nth_ns_succ in H; try eassumption; eauto with Arith.
                 erewrite nth_pol_n with (c := c₁) in H; try eassumption.
                 rewrite <- Hfn₃, <- HLn₃h, <- Hcn₃ in H.
                 rename H into Hrn₃.
                 move Hrn₃ before Hcn₃.
                 symmetry in Hrn₃.
                 remember HLn₃h as H; clear HeqH.
                 eapply hd_newton_segments in H; try eassumption.
                 rename H into HLn₃i.
                 move HLn₃i before HLn₃h.
                 remember HLn₃i as H; clear HeqH.
                 eapply q_eq_1_any_r in H; try eassumption; eauto with Arith.
                 rename H into Hqn₃; move Hqn₃ before HKn₃.
                 symmetry in Hrn₃.
                 rewrite Hcn₃ in Hrn₃.
                 eapply find_coeff_more_iter with (r := r); auto with Arith.
                  intros j.
                  remember (S (S (S n))) as sn.
                  rewrite HLn₃h, Hfn₃.
                  rewrite Hcn₂.
                  erewrite <- nth_c_succ; eauto with Arith.
                  erewrite <- nth_pol_succ; eauto with Arith.
                  erewrite <- nth_ns_succ; eauto with Arith.
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

                   apply Z.lt_le_incl; auto with Arith.

               intros H; discriminate H.

              apply nat_compare_gt in Hcmp₁.
              apply Nat.nle_gt in Hcmp₁; contradiction.

     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     apply Z.mul_cancel_r; auto with Arith.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto with Arith.
      rewrite Z.mul_comm.
      rewrite Z.div_mul; auto with Arith.

      rewrite Hnd₁, Hdd₁.
      rewrite Pos_mul_mul_swap, Z.mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      apply Z.mul_divide_cancel_r; auto with Arith.
      erewrite αj_m_eq_p_r with (L₁ := Ln₁); try eassumption; eauto with Arith.
      rewrite <- Zposnat2Znat; try eassumption.
      rewrite Z.mul_shuffle0, <- Z.mul_assoc.
      rewrite <- Pos2Z.inj_mul.
      apply Z.divide_factor_r.

 intros i.
 destruct i; [ rewrite Hr₀₁; auto | simpl ].
 rewrite <- Hc, <- Hf₁, <- HL₁.
 apply Hrle₁.
Qed.

Theorem root_tail_sep_1st_monom_any_r : ∀ f L f₁ L₁ c m q₀ n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i, (i ≤ S n)%nat → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
  → (∀ i, i ≤ 1%nat → nth_r i f L = r)
  → (∀ i, r ≤ nth_r i f L)
  → (root_tail (m * q₀) n f₁ L₁ =
       ps_monom (nth_c n f₁ L₁) (nth_γ n f₁ L₁) +
       ps_monom 1%K (nth_γ n f₁ L₁) *
       root_tail (m * q₀) (S n) f₁ L₁)%ps.
Proof.
intros f L f₁ L₁ c m q₀ n r HL Hm Hq₀ Hc Hf₁ HL₁ Hpsi Hri Hrle.
remember (zerop_1st_n_const_coeff (S n) f L) as z₁ eqn:Hz .
symmetry in Hz.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz.
 discriminate Hz.

 assert (∀ i, i ≤ S n → nth_r i f L = r) as H.
  apply non_decr_imp_eq; auto with Arith.

  clear Hri; rename H into Hri; move Hri before Hrle.
  assert (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i f₁ L₁) ≠ 0)%ps) as H.
   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hpsi in Hin; simpl in Hin.
   rewrite <- Hc, <- Hf₁, <- HL₁ in Hin; assumption.

   rename H into Hpsi₁; move Hpsi₁ before Hpsi.
   assert (∀ j, r ≤ nth_r j f₁ L₁) as H.
    intros j.
    pose proof (Hrle (S j)) as H; simpl in H.
    rewrite <- Hc, <- Hf₁, <- HL₁ in H; assumption.

    rename H into Hrle₁; move Hrle₁ before Hrle.
    eapply root_tail_sep_1st_monom; eauto with Arith.
Qed.

Theorem root_tail_when_r_r : ∀ f L f₁ L₁ m q₀ b r n,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i, i ≤ 1%nat → nth_r i f L = r)
  → (∀ n, r ≤ nth_r n f L)
  → zerop_1st_n_const_coeff (S n) f L = false
  → (root_tail (m * q₀) b f₁ L₁ =
     root_head b n f₁ L₁ +
       ps_monom 1%K (γ_sum b n f₁ L₁) *
       root_tail (m * q₀) (b + S n) f₁ L₁)%ps.
Proof.
intros f L f₁ L₁ m q₀ b r n.
intros HL Hm Hq₀ Hf₁ HL₁ Hri Hrle Hnz.
remember (ac_root (Φq f L)) as c eqn:Hc.
revert f L f₁ L₁ c m q₀ b HL Hm Hq₀ Hc Hf₁ HL₁ Hri Hrle Hnz.
induction n; intros.
 unfold root_head; simpl.
 remember (zerop_1st_n_const_coeff b f₁ L₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  rewrite rng_add_0_l.
  unfold root_tail.
  rewrite Hz₁, Nat.add_1_r.
  rewrite zerop_1st_n_const_coeff_succ2.
  rewrite Hz₁, Bool.orb_true_l.
  rewrite rng_mul_0_r; reflexivity.

  rewrite Nat.add_0_r, rng_add_0_r.
  rewrite root_tail_from_0_const_r; try eassumption; auto with Arith.
  unfold root_head.
  rewrite Hz₁.
  unfold root_head_from_cγ_list.
  rewrite Nat.add_0_r, rng_add_0_r.
  rewrite Nat.add_1_r; reflexivity.

 remember (zerop_1st_n_const_coeff b f₁ L₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  unfold root_head, root_tail.
  rewrite Hz₁.
  rewrite zerop_1st_n_const_coeff_true_if; auto with Arith.
  rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

  rewrite root_head_succ; auto with Arith.
  remember (zerop_1st_n_const_coeff (b + S n) f₁ L₁) as z eqn:Hz .
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
    rewrite zerop_1st_n_const_coeff_true_if; auto with Arith.
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
    rewrite <- Hc, <- Hf₁, <- HL₁.
    rewrite Hz; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁]; auto with Arith.
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l (S (S n)))) as H.
    contradiction.

    rewrite zerop_1st_n_const_coeff_succ2 in Hnz.
    apply Bool.orb_false_iff in Hnz.
    destruct Hnz; assumption.
Qed.

Theorem β_lower_bound_r_const : ∀ f L f₁ L₁ m r η,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (0 < r)%nat
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i, r ≤ nth_r i f L)
  → η = 1 # (2 * m * q_of_m m (γ L))
  → ∀ n Ln,
    zerop_1st_n_const_coeff n f₁ L₁ = false
    → (∀ i, i ≤ S n → nth_r i f L = r)
    → Ln = nth_ns n f₁ L₁
    → η < β Ln.
Proof.
intros f L f₁ L₁ m r η.
intros HL Hm Hr Hf₁ HL₁ Hrle Hη n Ln Hnz Hri HLn.
remember HL as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
eapply r_n_nth_ns in H; try eassumption; eauto with Arith.
destruct H as (αjn, (αkn, H)).
destruct H as (Hinin, (Hfinn, (Hαjn, Hαkn))).
unfold β.
rewrite Hinin; simpl.
unfold Qnat; simpl.
rewrite rng_mul_0_l, rng_add_0_r.
remember Hf₁ as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; try eassumption; eauto with Arith.
rename H into HK₁.
pose proof (Hnz O (Nat.le_0_l n)) as Hnz₀.
simpl in Hnz₀.
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
apply Hri in H; simpl in H.
rename H into Hr₀.
assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
apply Hri in H; simpl in H.
rewrite <- Hf₁, <- HL₁ in H.
rename H into Hr₁.
remember HL₁ as H; clear HeqH.
eapply r_n_next_ns in H; try eassumption; auto with Arith.
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember HL₁ as H; clear HeqH.
eapply hd_newton_segments in H; try eassumption.
rename H into HL₁i.
remember HK₁ as H; clear HeqH.
eapply first_n_pol_in_K_1_m_any_r with (L := L₁) in H; eauto with Arith.
 rename H into HKn.
 remember (nth_pol n f₁ L₁) as fn eqn:Hfn .
 remember HL₁i as H; clear HeqH.
 eapply nth_in_newton_segments_any_r with (n := n) in H; eauto with Arith.
 rename H into HLni.
 remember HKn as H; clear HeqH.
 eapply pol_ord_of_ini_pt in H; try eassumption; eauto with Arith.
 rewrite Hη, H.
 rewrite <- Pos.mul_assoc.
 remember (m * q_of_m m (γ L))%positive as m₁ eqn:Hm₁ .
 unfold mh_of_m.
 erewrite <- qden_αj_is_ps_polydo; try eassumption; eauto with Arith.
 remember (2 * m₁)%positive as m₂.
 unfold Qlt; simpl; subst m₂.
 clear H.
 assert (0 < Qnum αjn * Zpos m₁ / Zpos (Qden αjn))%Z as H.
  apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
   apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
   apply Z.mul_nonneg_nonneg; auto with Arith.
   apply Z.lt_le_incl; assumption.

   eapply num_m_den_is_pos with (L := Ln); try eassumption.

  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  replace (Zpos m₁)%Z with (1 * Zpos m₁)%Z at 1 by reflexivity.
  apply Z.mul_lt_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
  rewrite Z.mul_comm.
  apply Z.lt_1_mul_pos; auto with Arith.
  apply Z.lt_1_2.

 eapply q_eq_1_any_r with (L := L₁); try eassumption; eauto with Arith.

 intros i.
 rewrite HL₁, Hf₁.
 erewrite <- nth_pol_succ with (n := O); try eassumption; try reflexivity.
 erewrite <- nth_ns_succ with (n := O); try eassumption; try reflexivity.
 rewrite <- nth_r_add.
 apply Hrle.
Qed.

Theorem r₁_le_r₀ : ∀ f L f₁,
  newton_segments f = Some L
  → f₁ = nth_pol 1 f L
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → nth_r 1 f L ≤ nth_r 0 f L.
Proof.
intros f L f₁ HL Hf₁ Hnz₀; simpl.
simpl in Hf₁; rewrite <- Hf₁.
remember (ac_root (Φq f L)) as c eqn:Hc .
remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
remember HL₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember HL₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember HL as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ in H; try eassumption; eauto with Arith.
destruct H as (Hj₁, (Hr₁, (Hr, _))).
transitivity k₁; auto with Arith.
Qed.

Theorem r_le_eq_incl : ∀ f L r n,
  newton_segments f = Some L
  → nth_r 0 f L = r
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
  → (∀ i, i ≤ n → r ≤ nth_r i f L)
  → (∀ i, i ≤ n → r = nth_r i f L).
Proof.
intros f L r n HL Hr₀ Hnz Hri i Hin.
remember Hin as H; clear HeqH.
apply Hri in H.
apply Nat.le_antisymm; auto with Arith.
clear H.
revert f L r n HL Hr₀ Hnz Hri Hin.
induction i; intros; [ rewrite <- Hr₀; reflexivity | idtac ].
destruct n; [ exfalso; revert Hin; apply Nat.nle_succ_0 | idtac ].
remember Hin as H; clear HeqH.
apply Hri in H.
simpl in H; simpl.
remember (ac_root (Φq f L)) as c eqn:Hc .
remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
eapply IHi; try eassumption; eauto with Arith.
 clear H.
 remember HL as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; try eassumption; eauto with Arith.
 destruct H as [H₁| H₁].
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hnz in H; contradiction.

  simpl in H₁.
  rewrite <- Hc, <- Hf₁ in H₁; auto with Arith.
  destruct (newton_segments f₁) as [L'₁| ]; [ | easy ].
  now subst L₁.

 apply Nat.le_antisymm.
  clear H.
  remember HL as H; clear HeqH.
  eapply r₁_le_r₀ in H; try eassumption; eauto with Arith.
   rewrite Hr₀ in H; simpl in H.
   rewrite <- Hc, <- Hf₁, <- HL₁ in H; auto with Arith.

   clear H.
   assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
   apply Hnz in H; auto with Arith.

  clear H.
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hf₁, <- HL₁ in H; auto with Arith.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption.
 apply Hnz in Hin; simpl in Hin.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hin; auto with Arith.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption.
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hin; auto with Arith.
Qed.

End theorems.
