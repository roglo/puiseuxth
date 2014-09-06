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
Require Import RootWhenR1.

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
  split; [ fast_omega Hin | idtac ].
  split; assumption.

  apply Nat.nlt_ge in H.
  exists (S n).
  split; [ reflexivity | idtac ].
  split; [ idtac | assumption ].
  right; rewrite Nat.pred_succ; assumption.
Qed.

Theorem nth_r_n : ∀ pol ns pol₁ ns₁ c₁ n,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_r n pol ns = root_multiplicity acf c₁ (Φq pol₁ ns₁).
Proof.
intros pol ns pol₁ ns₁ c₁ n Hpol₁ Hns₁ Hc₁.
revert pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁.
induction n; intros; [ subst; reflexivity | simpl ].
apply IHn; subst; reflexivity.
Qed.

(* see pouet *)
(*
Theorem pouet2 : ∀ f ffo ms a₀ a₁ la v₀ v₁ j k αj αk r,
  f = pair_rec (λ pow ps, (Qnat pow, ps))
  → ffo = filter_finite_ord R (List.map f (power_list 2 la))
  → ms = minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo
  → (∀ i : nat, (order (List.nth i [a₀; a₁ … la] 0%ps) ≥ 0)%Qbar)
  → (order (List.nth r la 0%ps) = 0)%Qbar
  → 0 < v₁
  → 0 < v₀
  → (Qnat 0, v₀) = (Qnat j, αj)
  → end_pt ms = (Qnat k, αk)
  → (j = 0)%nat ∧ (0 < k)%nat ∧ (k ≤ S (S r))%nat ∧ 0 < αj ∧ αk >= 0 ∧
    seg ms = [].
Proof.
intros f ffo ms a₀ a₁ la v₀ v₁ j k αj αk r.
intros Heqf Heqffo Heqms Hnneg Hz Hpos₀ Hpos₁ Hini Hfin.
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
  split; [ apply Nat.lt_0_1 | idtac ].
  split; [ fast_omega | idtac ].
  split; [ assumption | idtac ].
  split; [ apply Qlt_le_weak; assumption | idtac ].
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
ggg.
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
*)

Theorem multiplicity_lt_length : ∀ cpol c,
  (al cpol ≠ [])%lap
  → (root_multiplicity acf c cpol < length (al cpol))%nat.
Proof.
intros cpol c Hnz.
unfold root_multiplicity.
remember (al cpol) as la; clear Heqla.
remember (length la) as len.
assert (length la ≤ len) as Hlen by omega.
clear Heqlen.
revert la Hnz Hlen.
induction len; intros.
 apply Nat.le_0_r in Hlen.
 destruct la as [| a]; [ exfalso; apply Hnz; reflexivity | idtac ].
 discriminate Hlen.

 simpl.
 destruct (ac_zerop (lap_mod_deg_1 la c)) as [H₁| H₁].
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
    apply IHla with (a := b); auto.
    intros H.
    rewrite H in Hnz.
    apply Hnz; rewrite H₁.
    constructor; reflexivity.

   rewrite length_lap_mod_div_deg_1; auto.

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
 rewrite slope_slope_expr in H; eauto .
 rewrite <- Hfin₁ in H.
 rewrite Hfin₁ in H; simpl in H.
 unfold slope_expr in H; simpl in H.
 rewrite Hz in H.
 rewrite Q_sub_0_r in H.
 unfold Qle in H; simpl in H.
 rewrite Qnum_inv_Qnat_sub in H; eauto .
 rewrite Z.mul_1_r in H.
 rewrite Qnum_inv_Qnat_sub in H; [ idtac | fast_omega Hrk ].
 rewrite Z.mul_1_r in H.
 rewrite Qden_inv_Qnat_sub in H; [ idtac | fast_omega Hrk ].
 rewrite Qden_inv_Qnat_sub in H; [ idtac | fast_omega Hrk ].
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

     fast_omega Hrk.

   apply Z.mul_nonneg_nonneg; auto.
   apply Z.mul_nonneg_nonneg; auto.
   unfold Qle in Hnnegk; simpl in Hnnegk.
   rewrite Z.mul_1_r in Hnnegk; assumption.

  apply -> Pos.compare_lt_iff.
  rewrite <- Nat2Pos.inj_compare.
   apply nat_compare_lt; assumption.

   intros HH; discriminate HH.

   fast_omega Hrk.

 rename H into Hsl.
 subst pts.
 remember Heqms as H; clear HeqH.
 symmetry in H.
 destruct Hsr as [Hsr| Hsr].
  subst pt.
  eapply minimise_slope_expr_le in H; eauto .
   apply Qle_not_lt in H; contradiction.

   simpl; apply Qnat_lt; assumption.

  eapply min_slope_le with (pt₃ := (Qnat (S r), v)) in H; eauto .
   apply Qle_not_lt in H; contradiction.

   apply List.in_or_app; left; assumption.

   simpl; apply Qnat_lt; assumption.
Qed.

(* more general than r_1_j_0_k_1 which could be simplified perhaps *)
Theorem r_n_j_0_k_n : ∀ pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ k₁ = r ∧ αj₁ > 0 ∧ αk₁ == 0.
Proof.
intros pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ m r.
intros Hns Hm Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁ Hini₁ Hfin₁.
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
     apply multiplicity_lt_length with (c := c₁) in H.
     rewrite Hr₁ in H.
     rewrite al_Φq in H.
     rewrite <- Hpl in H.
     erewrite length_char_pol with (ns := ns₁) in H; eauto .
      Focus 2.
      rewrite Hini₁; simpl.
      rewrite nat_num_Qnat; reflexivity.

      rewrite Hini₁ in H; simpl in H.
      rewrite nat_num_Qnat in H.
      apply lt_S_n in H.
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
       apply Nat.nle_gt in H.
       exfalso; apply H, Nat.le_0_l.

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
       rewrite and_comm, and_assoc.
       unfold ps_poly_nth, ps_lap_nth in Hpos₀.
       rewrite <- Heqla in Hpos₀; simpl in Hpos₀.
       rewrite Heqv₀ in Hpos₀.
       apply Qbar.qfin_lt_mono in Hpos₀.
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
        rename H into Hnnegk.
        rewrite minimised_slope_beg_pt in Hns₁.
        rewrite Hfin₁ in Hns₁.
        remember (minimise_slope (Qnat 0, αj₁) pt pts) as ms.
        remember Heqms as H; clear HeqH.
        symmetry in H.
        apply end_pt_in in H.
        apply List.in_split in H.
        destruct H as (pts₁, (pts₂, Hpts)).
        destruct (eq_nat_dec k₁ (S r)) as [H₁| H₁]; [ idtac | exfalso ].
         subst k₁.
         split; [ idtac | reflexivity ].
         remember Heqpts as H; clear HeqH.
         symmetry in H.
         rewrite Heqf in H.
         rewrite fold_qpower_list in H.
         remember Heqms as HH; clear HeqHH.
         symmetry in HH.
         apply end_pt_in in HH.
         rewrite Hfin₁ in HH.
         eapply in_pts_in_psl with (def := 0%ps) in H; eauto .
         unfold Qnat, Qnum in H.
         rewrite Nat2Z.id, Nat_sub_succ_1 in H.
         destruct H as (_, H).
         simpl in Hz.
         rewrite H in Hz.
         apply Qbar.qfin_inj in Hz.
         assumption.

         apply Nat.neq_sym in H₁.
         apply le_neq_lt in Hrk; auto; clear H₁.
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
            rewrite <- H₂ in Hrk.
            revert Hrk; apply Nat.lt_irrefl.

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
             eapply Nat.lt_trans in H; eauto .
             revert H; apply Nat.lt_irrefl.

             apply IHpts₂; auto.
             eapply Sorted_minus_2nd; eauto .
             intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

           destruct pts₁ as [| pt₁]; [ contradiction | idtac ].
           simpl in Hpts.
           injection Hpts; clear Hpts; intros Hpts H₁.
           subst pt₁.
           apply Nat.nle_gt in Hrk.
           apply Hrk.
           eapply k_le_r; eauto .
Qed.

(* more general than r_1_next_ns which could be simplified perhaps *)
Theorem r_n_next_ns : ∀ pol ns c pol₁ ns₁ c₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
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
intros pol ns c pol₁ ns₁ c₁ m r.
intros Hns Hm Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁.
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns₁ as H; clear HeqH.
eapply r_n_j_0_k_n in H; eauto .
destruct H as (Hj₁, (Hk₁, (Hαj₁, Hαk₁))).
subst j₁ k₁.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
exists αj₁, αk₁; auto.
Qed.

(* more general than r_1_nth_ns which could be simplified perhaps *)
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
   Focus 2.
   assert (0 ≤ S (S n)) as H₁ by apply Nat.le_0_l.
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc in H₁; assumption.

   Focus 2.
   assert (1 ≤ S (S n)) as H₁ by fast_omega .
   apply Hri in H₁; simpl in H₁.
   rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H₁; assumption.

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
     Focus 2.
     intros i Hin.
     apply le_n_S in Hin.
     apply Hri in Hin; simpl in Hin.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
     assumption.

     Focus 2.
     intros i Hin.
     apply le_n_S in Hin.
     apply Hpsi in Hin; simpl in Hin.
     rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
     assumption.

     Focus 2.
     clear H.
     intros H; rewrite H in Hns₁; subst ns₁.
     simpl in Hini₁, Hfin₁.
     injection Hfin₁; intros H₁ H₂.
     rewrite <- Nat2Z.inj_0 in H₂.
     apply Nat2Z.inj in H₂.
     subst r.
     revert Hrnz; apply Nat.lt_irrefl.

    eapply next_pol_in_K_1_mq with (ns := ns); eauto .
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
 apply multiplicity_neq_0; auto.

 pose proof (Hpos O (Nat.lt_0_succ r)) as H₂.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
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
    assert (1 ≤ pow)%nat as Hpow by fast_omega Heqpow.
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
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
   exists 0%nat.
   split; [ apply Nat.le_0_l | idtac ].
   split; [ left; reflexivity | simpl ].
   destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

   exists 1%nat.
   split; [ apply le_n_S, Nat.le_0_l | idtac ].
   split.
    right; simpl.
    destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
    contradiction.

    simpl.
    destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
    rewrite <- Hc, <- Hpol₁.
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.

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
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)); eauto .
     destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₂| H₂].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

      exists 1%nat.
      split; [ apply le_n_S, Nat.le_0_l | idtac ].
      split.
       right; simpl.
       destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
       contradiction.

       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
       rewrite <- Hc, <- Hpol₁.
       destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.

     discriminate Hinz.

    destruct i.
     rewrite Nat.pred_0 in Hiz.
     rewrite Hinz in Hiz; discriminate Hiz.

     rewrite Nat.pred_succ in Hiz.
     destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
      exists 0%nat.
      split; [ apply Nat.le_0_l | idtac ].
      split; [ left; reflexivity | simpl ].
      destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

      exists (S (S i)).
      split; [ fast_omega Hin | idtac ].
      split.
       right; rewrite Nat.pred_succ.
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 pol)).
        contradiction.

        rewrite <- Hc, <- Hpol₁, <- Hns₁.
        assumption.

       remember (S i) as si; simpl; subst si.
       destruct (ps_zerop R (ps_poly_nth 0 pol)).
        reflexivity.

        rewrite <- Hc, <- Hpol₁, <- Hns₁.
        assumption.

   eapply List_hd_in; eauto .
Qed.

(* don't know if it is useful *)
Theorem q_divides_r : ∀ pol ns c pol₁ ns₁ c₁ m q₀ r q,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → pol_in_K_1_m pol₁ (m * q₀)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → root_multiplicity acf c (Φq pol ns) = r
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = r
  → q = Pos.to_nat (q_of_m (m * q₀) (γ ns₁))
  → (q | r)%nat.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ r q.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁ Hq.
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_n_j_0_k_n in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, Hαk₁))).
subst j₁ k₁; simpl.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
eapply List_hd_in in Hns₁.
 Focus 2.
 intros H; rewrite H in Hns₁; subst ns₁; simpl in Hfin₁.
 injection Hfin₁; clear Hfin₁; intros H₁ H₂.
 rewrite <- Nat2Z.inj_0 in H₂.
 apply Nat2Z.inj in H₂.
 move H₂ at top; subst r.
 revert Hr.
 apply multiplicity_neq_0; auto.

 remember Hns₁ as Hqhj; clear HeqHqhj.
 eapply q_is_factor_of_h_minus_j in Hqhj; eauto .
  2: apply List.in_or_app; right; left; symmetry; eauto .

  rewrite Nat.sub_0_r in Hqhj.
  assumption.
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

Theorem lap_app_add : ∀ la lb,
  (la ++ lb = la + list_pad (length la) 0%K lb)%lap.
Proof.
intros la lb.
induction la as [| a]; [ reflexivity | simpl ].
rewrite rng_add_0_r.
constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_add_map2 : ∀ β (f g : β → α) la,
  (List.map f la + List.map g la = List.map (λ b, (f b + g b)%K) la)%lap.
Proof.
intros β f g la.
induction la as [| b]; [ reflexivity | simpl ].
constructor; auto.
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
    exfalso; fast_omega H₁ H₂ Hnb.

    apply Nat.nle_gt in H₂.
    replace (n - S b)%nat with O by fast_omega H₂.
    replace (n - b)%nat with O by fast_omega H₂; simpl.
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
rewrite Nat.sub_0_r, minus_Sn_n in HeqΨ.
rename H into Hcp.
remember Hns as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk) in H; eauto .
 2: apply List.in_or_app; right; left; assumption.

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
  destruct (ac_zerop a) as [H₁| H₁].
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
     rewrite rng_mul_nat_assoc2 in HH.
     rewrite rng_mul_comm in HH.
     rewrite <- rng_mul_nat_assoc2 in HH.
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
eapply q_mj_mk_eq_p_h_j in H; eauto .
 2: apply List.in_or_app.
 2: right; left; eauto .

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
  Focus 2.
  rewrite Hr₁; assumption.

  rewrite H in HH₃.
  rewrite Z.mul_1_l in HH₃.
  rewrite <- HH₃.
  rewrite Heqmj'.
  symmetry.
  rewrite Z.mul_comm.
  rewrite <- Z.divide_div_mul_exact; auto.
   rewrite Z.mul_comm.
   rewrite Z.div_mul; auto.

   eapply den_αj_divides_num_αj_m; eauto .
Qed.

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

(* cf root_tail_split_1st *)
Theorem root_tail_split_1st_any_r : ∀ pol ns pol₁ ns₁ c m q₀ r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) 0 pol₁ ns₁ =
     root_head 0 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum 0 0 pol₁ ns₁) *
       root_tail (m * q₀) 1 pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri H₀.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 pose proof (Hri O) as Hr₀; simpl in Hr₀.
 rewrite <- Hc in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 pose proof (Hri 2%nat) as Hr₂.
 remember 1%nat as one in Hr₂; simpl in Hr₂.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₂.
 subst one; simpl in Hr₂.
 rename H₁ into Hnz₁.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 assert (0 < r)%nat as Hrpos.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀.
  apply multiplicity_neq_0; auto.

  assert (0 < Z.of_nat r)%Z as Hrpos₁ by fast_omega Hrpos.
  assert (r ≠ 0)%nat as Hrpos₂ by fast_omega Hrpos.
  assert (Z.of_nat r ≠ 0%Z)%nat as Hrpos₃ by fast_omega Hrpos.
  eapply List_hd_in in Hns₁₁; eauto .
   remember Hns₁₁ as HK₂; clear HeqHK₂.
   eapply next_pol_in_K_1_mq in HK₂; eauto .
   remember Hns₁₁ as H; clear HeqH.
   eapply q_eq_1_any_r in H; eauto .
    rewrite H in HK₂; clear H.
    rewrite Pos.mul_1_r, <- Heqm₁ in HK₂.
    unfold γ_sum; simpl.
    unfold summation; simpl.
    do 2 rewrite rng_add_0_r.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
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
     remember (Pos.of_nat r) as pr.
     remember (Qden αj₁ * pr * Qden αk₁)%positive as x.
     rewrite ps_adjust_eq with (n := O) (k := x); subst x.
     symmetry.
     rewrite ps_adjust_eq with (n := O) (k := m₁).
     symmetry.
     unfold adjust_ps; simpl.
     do 2 rewrite series_shift_0.
     rewrite series_stretch_const.
     do 2 rewrite Z.sub_0_r.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto.
      rewrite Pos2Z.inj_mul, <- Z.mul_assoc, Z.mul_comm, Z.mul_assoc.
      rewrite Z.div_mul; auto.
      apply mkps_morphism.
       remember (Qden αj₁ * pr * Qden αk₁)%positive as x.
       symmetry.
       rewrite <- series_stretch_const with (k := x); subst x.
       apply stretch_morph; auto.
       constructor; intros i; simpl.
       unfold root_tail_series_from_cγ_list; simpl.
       rewrite <- Hc₁, <- Hpol₂.
       rewrite <- Hns₂.
       destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
        contradiction.

        destruct i; [ reflexivity | simpl ].
        destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₃| H₃]; auto.
        contradiction.

       rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0.
       rewrite <- Z.mul_assoc, Z.mul_comm; reflexivity.

       rewrite Pos.mul_comm; reflexivity.

      rewrite Pos2Z.inj_mul.
      remember HK₁ as H; clear HeqH.
      rewrite <- Heqm₁ in H.
      apply any_in_K_1_m with (h := O) (αh := αj₁) in H.
       destruct H as (mj, Hmj).
       unfold Qeq in Hmj; simpl in Hmj.
       rewrite Hmj, Z.mul_comm.
       apply Z.mul_divide_cancel_r; auto.
       subst pr.
       remember Hns₁₁ as H; clear HeqH.
       eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk₁) in H; eauto .
        remember (q_of_m (m * q₀) (γ ns₁)) as q₁.
        remember (mh_of_m (m * q₀) αj₁ (ps_poly_nth 0 pol₁)) as mj'.
        remember (mh_of_m (m * q₀) αk₁ (ps_poly_nth r pol₁)) as mk.
        remember (p_of_m (m * q₀) (γ ns₁)) as p₁.
        rewrite Nat.sub_0_r in H.
        destruct H as (H₂, H₃).
        unfold Qeq in H₂; simpl in H₂.
        rewrite Hαk₁ in H₂; simpl in H₂.
        symmetry in H₂.
        apply Z.eq_mul_0_l in H₂; auto.
        move H₂ at top; subst mk.
        rewrite Z.sub_0_r in H₃.
        rewrite positive_nat_Z in H₃.
        unfold mh_of_m in Heqmj'.
        rewrite <- Heqm₁ in Heqmj'.
        erewrite <- qden_αj_is_ps_polord in Heqmj'; eauto .
        rewrite Hmj in Heqmj'.
        rewrite Z.div_mul in Heqmj'; auto; subst mj'.
        remember Heqq₁ as H; clear HeqH.
        eapply q_eq_1_any_r in H; eauto .
         rewrite H in H₃.
         rewrite Z.mul_1_l in H₃.
         exists p₁.
         rewrite Zposnat2Znat; [ assumption | idtac ].
         destruct r; [ idtac | apply Nat.lt_0_succ ].
         exfalso; revert Hr₀.
         apply multiplicity_neq_0; auto.

         rewrite Hr₁; assumption.

        apply List.in_or_app; right; left; assumption.

       clear H.
       remember Hns₁₁ as H; clear HeqH.
       unfold newton_segments in H.
       unfold points_of_ps_polynom in H.
       apply ini_fin_ns_in_init_pts in H.
       rewrite <- Hini₁; destruct H; assumption.

     remember Hns₁₁ as H; clear HeqH.
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
     do 2 rewrite Z.add_0_r.
     rewrite Qnum_inv_Qnat_sub; auto.
     rewrite Qden_inv_Qnat_sub; auto.
     rewrite Nat.sub_0_r.
     rewrite Z.mul_1_r.
     rewrite Z.mul_1_r.
     remember (Pos.of_nat r) as rq eqn:Hrq .
     remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
     remember (Qden αj₁ * Qden αk₁ * rq)%positive as dd.
     remember (dd * m₁)%positive as x.
     rewrite Z.mul_shuffle0, Pos_mul_shuffle0, Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     subst x.
     do 2 rewrite fold_series_const.
     rewrite series_stretch_const.
     rewrite series_mul_1_l.
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
       remember Hns₂ as Hns₂₁; clear HeqHns₂₁.
       eapply List_hd_in in Hns₂₁; eauto .
        remember Hns₂₁ as H; clear HeqH.
        eapply den_αj_divides_num_αj_m in H; eauto .
        remember Hns₂₁ as HH; clear HeqHH.
        eapply num_m_den_is_pos in HH; eauto .
        destruct H as (mj₂, Hmj₂).
        rewrite Hmj₂ in HH.
        rewrite Z.div_mul in HH; auto.
        rewrite Hmj₂.
        remember (Qden αj₂ * rq)%positive as x.
        rewrite Pos.mul_comm in Heqx; subst x.
        rewrite Pos2Z.inj_mul.
        rewrite Z.div_mul_cancel_r; auto.
        destruct mj₂ as [| mj₂| mj₂]; [ exfalso | idtac | exfalso ].
         revert HH; apply Nat.lt_irrefl.

         clear HH; simpl.
         assert (0 <= ' mj₂ / ' rq)%Z as Hdr by apply Z_div_pos_is_nonneg.
         assert (Z.to_nat (- (' mj₂ / ' rq * ' dd * ' dd)) = 0)%nat as H.
          remember (' mj₂ / ' rq)%Z as x.
          symmetry in Heqx.
          destruct x as [| x| x]; try reflexivity.
          apply Z.nlt_ge in Hdr.
          exfalso; apply Hdr, Zlt_neg_0.

          rewrite H; clear H.
          unfold adjust_series; simpl.
          rewrite series_shift_0.
          rewrite series_stretch_const.
          rewrite <- series_stretch_stretch.
          rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
          rewrite Z2Nat.inj_mul; auto; simpl.
          rewrite <- stretch_shift_series_distr.
          rewrite <- series_stretch_const with (k := (dd * dd)%positive).
          rewrite <- series_stretch_add_distr.
          apply stretch_morph; [ reflexivity | idtac ].
          unfold series_add; simpl.
          constructor; intros i; simpl.
          rename H₁ into Hz₂.
          destruct (lt_dec i (Z.to_nat (' mj₂ / ' rq))) as [H₁| H₁].
           destruct (zerop i) as [H₂| H₂].
            subst i; simpl.
            rewrite rng_add_0_r.
            unfold root_tail_series_from_cγ_list; simpl.
            rewrite <- Hc₁.
            destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
            contradiction.

            rewrite rng_add_0_l.
            assert (next_pow 0 ns₂ m₁ = Z.to_nat (' mj₂ / ' rq)) as Hnpow.
             unfold next_pow; simpl.
             rewrite Hini₂, Hfin₂; simpl.
             rewrite Hαk₂; simpl.
             rewrite Qnum_inv_Qnat_sub; auto.
             rewrite Qden_inv_Qnat_sub; auto.
             rewrite Z.add_0_r, Z.mul_1_r.
             rewrite Nat.sub_0_r, Pos.mul_1_r.
             rewrite Z.mul_shuffle0, Pos_mul_shuffle0, Pos2Z.inj_mul.
             rewrite Z.div_mul_cancel_r; auto.
             rewrite Hmj₂.
             rewrite Pos.mul_comm, Pos2Z.inj_mul.
             rewrite Z.div_mul_cancel_r; auto.
             rewrite <- Hrq; reflexivity.

             remember (next_pow 0 ns₂ m₁) as p₂.
             rewrite <- Hnpow in H₁.
             unfold root_tail_series_from_cγ_list; simpl.
             destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [| H₃]; auto.
             destruct i; [ exfalso; fast_omega H₂ | clear H₂ ].
             rewrite <- Hc₁, <- Hpol₂, <- Hns₂; simpl.
             destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [| H₅]; auto.
             rewrite <- Heqp₂.
             remember (Nat.compare p₂ (S i)) as cmp; symmetry in Heqcmp.
             destruct cmp as [H₄| H₄| H₄]; auto.
              apply nat_compare_eq in Heqcmp.
              rewrite Heqcmp in H₁.
              exfalso; revert H₁; apply Nat.lt_irrefl.

              apply nat_compare_lt in Heqcmp.
              apply Nat.lt_le_incl, Nat.nlt_ge in Heqcmp.
              contradiction.

           apply Nat.nlt_ge in H₁.
           remember HK₂ as H; clear HeqH.
           apply any_in_K_1_m with (h := O) (αh := αj₂) in H.
            Focus 2.
            clear H.
            remember Hns₂₁ as H; clear HeqH.
            unfold newton_segments in H.
            unfold points_of_ps_polynom in H.
            apply ini_fin_ns_in_init_pts in H.
            rewrite <- Hini₂; destruct H; assumption.

            destruct H as (mj, Hmj).
            unfold Qeq in Hmj; simpl in Hmj.
            remember Hns₂₁ as H; clear HeqH.
            eapply q_mj_mk_eq_p_h_j with (h := r) (αh := αk₂) in H; eauto .
             Focus 2.
             apply List.in_or_app; right; left; assumption.

             remember (q_of_m m₁ (γ ns₂)) as q₂.
             remember (mh_of_m m₁ αj₂ (ps_poly_nth 0 pol₂)) as mj'.
             remember (mh_of_m m₁ αk₂ (ps_poly_nth r pol₂)) as mk.
             remember (p_of_m m₁ (γ ns₂)) as p₂.
             rewrite Nat.sub_0_r in H.
             destruct H as (H₂, H₃).
             unfold Qeq in H₂; simpl in H₂.
             rewrite Hαk₂ in H₂; simpl in H₂.
             symmetry in H₂.
             apply Z.eq_mul_0_l in H₂; auto.
             move H₂ at top; subst mk.
             rewrite Z.sub_0_r in H₃.
             rewrite positive_nat_Z in H₃.
             unfold mh_of_m in Heqmj'.
             erewrite <- qden_αj_is_ps_polord in Heqmj'; eauto .
             rewrite Hmj in Heqmj'.
             rewrite Z.div_mul in Heqmj'; auto; subst mj'.
             remember Heqq₂ as H; clear HeqH.
             eapply q_eq_1_any_r in H; eauto .
              2: rewrite Hr₂; assumption.

              rewrite H in H₃.
              rewrite Z.mul_1_l in H₃.
              rewrite Hmj₂ in Hmj.
              apply Z.mul_cancel_r in Hmj; auto.
              subst mj.
              rewrite H₃, Hrq in H₁; simpl in H₁.
              rewrite <- positive_nat_Z in H₁.
              rewrite Nat2Pos.id in H₁; auto.
              rewrite Z.div_mul in H₁; auto.
              rewrite H₃ in Hmj₂.
              rewrite H₃, Hrq.
              rewrite <- positive_nat_Z.
              rewrite Nat2Pos.id; auto.
              rewrite Z.div_mul; auto.
              rename H into Hq₂.
              assert (0 < p₂)%Z as Hp₂pos.
               destruct p₂ as [| p₂| p₂].
                exfalso; revert H₃; apply Pos2Z_ne_0.

                apply Pos2Z.is_pos.

                pose proof (Pos2Z.is_nonneg mj₂) as H.
                rewrite H₃ in H.
                apply Z.nlt_ge in H.
                exfalso; apply H.
                apply Z.mul_neg_pos; [ apply Pos2Z.neg_is_neg | idtac ].
                rewrite <- Nat2Z.inj_0.
                apply Nat2Z.inj_lt; assumption.

               destruct (zerop i) as [H₂| H₂].
                subst i.
                apply Nat.le_0_r in H₁.
                rewrite <- Z2Nat.inj_0 in H₁.
                apply Z2Nat.inj in H₁; try reflexivity.
                 rewrite H₁ in H₃; simpl in H₃.
                 exfalso; revert H₃; apply Pos2Z_ne_0.

                 apply Z.lt_le_incl; auto.

                rewrite rng_add_0_l.
                remember (Z.to_nat p₂) as n₂ eqn:Hn₂ .
                assert (next_pow 0 ns₂ m₁ = n₂) as Hnpow.
                 unfold next_pow; simpl.
                 rewrite Hini₂, Hfin₂; simpl.
                 rewrite Hαk₂; simpl.
                 rewrite Qnum_inv_Qnat_sub; auto.
                 rewrite Qden_inv_Qnat_sub; auto.
                 rewrite Z.add_0_r, Z.mul_1_r.
                 rewrite Nat.sub_0_r, Pos.mul_1_r.
                 rewrite Z.mul_shuffle0, Pos_mul_shuffle0, Pos2Z.inj_mul.
                 rewrite Hmj₂, Pos.mul_comm, Pos2Z.inj_mul.
                 rewrite <- Zposnat2Znat; auto.
                 do 3 rewrite <- Z.mul_assoc.
                 rewrite Z.div_mul; auto.
                 do 2 rewrite <- Pos2Z.inj_mul; auto.

                 remember (i - n₂)%nat as id.
                 unfold root_tail_series_from_cγ_list.
                 remember (S id) as x; simpl; subst x.
                 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₄| H₄].
                  contradiction.

                  destruct i; [ fast_omega H₂ | clear H₂ H₄ ].
                  rewrite <- Hc₁, <- Hpol₂, <- Hns₂, Hnpow; symmetry.
                  rewrite <- find_coeff_add with (dp := n₂).
                  rewrite Heqid.
                  rewrite Nat.add_0_l, Nat.sub_add; auto.
                  rewrite <- Heqid; simpl.
                  destruct (ps_zerop R (ps_poly_nth 0 pol₂)); auto; clear n.
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
                  rewrite Heqq₂ in Hq₂.
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

(* cf nth_in_newton_segments *)
Theorem nth_in_newton_segments_any_r : ∀ pol₁ ns₁ c₁ poln nsn n m r,
  ns₁ ∈ newton_segments pol₁
  → pol_in_K_1_m pol₁ m
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → (∀ i, nth_r i pol₁ ns₁ = r)
  → nsn ∈ newton_segments poln.
Proof.
intros pol₁ ns₁ c₁ poln nsn n m r Hns₁ Hm Hc₁ Hpsi Hpoln Hnsn Hri.
subst poln nsn.
revert pol₁ ns₁ c₁ m Hns₁ Hm Hc₁ Hpsi Hri.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
assert (1 ≤ S n) as H₁ by apply le_n_S, Nat.le_0_l.
apply Hpsi in H₁; simpl in H₁.
rewrite <- Hc₁, <- Hpol₂ in H₁.
remember (q_of_m m (γ ns₁)) as q₀ eqn:Hq₀ .
eapply IHn with (m := (m * q₀)%positive); eauto .
 pose proof (Hri 0%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc₁ in Hr₁.
 pose proof (Hri 1%nat) as Hr₂; simpl in Hr₂.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hr₂.
 remember Hns₂ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₂, (αj₂, Hini₂)).
 remember Hns₂ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₂, (αk₂, Hfin₂)).
 eapply hd_newton_segments₉; eauto .
 remember Hns₁ as H; clear HeqH.
 eapply r_n_j_0_k_n in H; eauto .
 destruct H as (Hj₂, (Hk₂, (Hαj₂, Hαk₂))).
 subst j₂ k₂.
 destruct r; [ idtac | apply Nat.lt_0_succ ].
 exfalso; revert Hr₁; apply multiplicity_neq_0; auto.

 eapply next_pol_in_K_1_mq; eauto .

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hpsi in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
 assumption.

 intros i.
 pose proof (Hri (S i)) as H; simpl in H.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
 assumption.
Qed.

(* cf first_n_pol_in_K_1_m *)
Theorem first_n_pol_in_K_1_m_any_r : ∀ pol ns poln m c r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → q_of_m m (γ ns) = 1%positive
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → ∀ n,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
    → poln = nth_pol n pol ns
    → pol_in_K_1_m poln m.
Proof.
intros pol ns poln m c r Hns HK Hc Hq Hri H₀ n Hnz Hpoln.
revert pol ns poln m c r Hns HK Hc Hq Hri H₀ Hnz Hpoln.
induction n; intros.
 simpl in Hpoln; subst poln; assumption.

 simpl in Hpoln.
 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
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

     intros i.
     pose proof (Hri (S i)) as H; simpl in H.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

     intros i Hin.
     apply Nat.succ_le_mono in Hin.
     apply Hnz in Hin; simpl in Hin.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
     assumption.

   clear H.
   assert (1 ≤ S n) as H by omega.
   apply Hnz in H; simpl in H.
   rewrite <- Hc, <- Hpol₁ in H.
   assumption.

  clear H.
  remember Hns as H; clear HeqH.
  eapply next_has_root_0_or_newton_segments in H; eauto .
  simpl in H.
  rewrite <- Hc, <- Hpol₁ in H.
  destruct H as [H| H]; auto.
  assert (1 ≤ S n)%nat as HH by fast_omega .
  apply Hnz in HH; simpl in HH.
  rewrite <- Hc, <- Hpol₁ in HH.
  contradiction.
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

Theorem find_coeff_iter_succ : ∀ pol ns pow m i n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → (∀ j, nth_r j pol ns = r)
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

 pose proof (Hri O) as Hr₀; simpl in Hr₀.
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
  pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₂| H₂].
   subst sn; simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
    destruct n; [ exfalso; fast_omega Hin | simpl ].
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

      intros j.
      pose proof (Hri (S j)) as H; simpl in H.
      rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
      assumption.

    intros j Hjn.
    destruct j; auto.
    destruct j; [ simpl; rewrite <- Hc, <- Hpol₁; auto | idtac ].
    exfalso; fast_omega Hjn.
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
   destruct j; [ simpl | exfalso; fast_omega Hj ].
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
    destruct j; [ simpl | exfalso; fast_omega Hj ].
    rewrite <- Hc, <- Hpol₁; assumption.

    simpl; rewrite <- Hc; auto.

   rewrite Hr₁; auto.

  intros j.
  pose proof (Hri (S j)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.
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

(* cf root_tail_from_0 *)
Theorem root_tail_from_0_const_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
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
     eapply r_n_j_0_k_n with (ns₁ := nsb₂) (m := m₁) in H; eauto .
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

End theorems.