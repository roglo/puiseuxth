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

Set Implicit Arguments.

Axiom exists_or_not_forall : ∀ P : nat → Prop, (∃ n, P n) ∨ (∀ n, ¬P n).

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

(* try and try again...
Theorem q_eq_1₄₂ : ∀ pol ns c pol₁ ns₁ c₁ m q₀ r,
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
  → q_of_m (m * q₀) (γ ns₁) = 1%positive.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁.
remember Hns as H; clear HeqH.
eapply r_n_next_ns in H; eauto .
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
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
 remember (Pos.to_nat (q_of_m (m * q₀) (γ ns₁))) as q.
 eapply q_is_factor_of_h_minus_j in Hqhj; eauto .
  2: apply List.in_or_app; right; left; symmetry; eauto .

  rewrite Nat.sub_0_r in Hqhj.
  destruct Hqhj as (d, Hd).
  symmetry in Hd.
  remember (q_of_m (m * q₀) (γ ns₁)) as qn eqn:Hqn .
  subst q.
  unfold q_of_m in Hqn; simpl in Hqn.
  rewrite Hini₁, Hfin₁ in Hqn; simpl in Hqn.
  rewrite Hαk₁ in Hqn; simpl in Hqn.
  rewrite Qden_inv_Qnat_sub in Hqn.
   rewrite Qnum_inv_Qnat_sub in Hqn.
    rewrite Nat.sub_0_r, Z.add_0_r, Z.mul_1_r in Hqn.
    remember (m * q₀)%positive as m₁ eqn:Hm₁ .
    rewrite Z.mul_shuffle0 in Hqn.
    do 2 rewrite Pos2Z.inj_mul in Hqn.
    remember (Qnum αj₁ * ' m₁ * ' Qden αk₁)%Z as x.
    rewrite Z.mul_shuffle0 in Hqn; subst x.
    rewrite Z.gcd_mul_mono_r_nonneg in Hqn; auto.
    rewrite Z.div_mul_cancel_r in Hqn; auto.
bbb.
  Hd : (d * Pos.to_nat qn)%nat = r
  Hqn : qn =
        Z.to_pos
          (' Qden αj₁ * ' Pos.of_nat r /
           Z.gcd (Qnum αj₁ * ' m₁) (' Qden αj₁ * ' Pos.of_nat r))
  ============================
   qn = 1%positive
*)

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

(* isn't it similar to multiplicity_lt_length? *)
(*
Theorem uuu : ∀ pol ns c j αj k αk m q r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → r = root_multiplicity acf c (Φq pol ns)
  → ini_pt ns = (Qnat j, αj)
  → fin_pt ns = (Qnat k, αk)
  → (Pos.to_nat q * r ≤ k - j)%nat.
Proof.
intros pol ns c j αj k αk m q r Hns Hm Hq Hc Hr Hini Hfin.
unfold root_multiplicity in Hr.
rewrite al_Φq in Hr.
erewrite length_char_pol in Hr; eauto .
 remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
 remember (List.map (term_of_point pol) pl) as tl eqn:Htl .
 rewrite Hini in Hr.
 remember S as s; simpl in Hr; subst s.
 rewrite nat_num_Qnat in Hr.
 remember (make_char_pol R j tl) as cpol eqn:Hcpol .
 unfold γ in Hq.
 rewrite Hini, Hfin in Hq; simpl in Hq.
 unfold q_of_m in Hq.
 simpl in Hq.
 rewrite Qden_inv_Qnat_sub in Hq.
  rewrite Qnum_inv_Qnat_sub in Hq.
   rewrite Z.mul_1_r in Hq.
   rewrite Z.mul_opp_l, Z.add_opp_r in Hq.
bbb.

intros pol ns c j αj k αk m q r Hns Hm Hq Hc Hr Hini Hfin.
assert (j < k)%nat as Hjk.
 eapply j_lt_k; eauto .
  rewrite Hini; simpl.
  rewrite nat_num_Qnat; reflexivity.

  rewrite Hfin; simpl.
  rewrite nat_num_Qnat; reflexivity.

 revert pol ns c j αj k αk m q Hns Hm Hq Hc Hr Hini Hfin Hjk.
 induction r; intros.
  symmetry in Hr.
  exfalso; revert Hr.
  apply multiplicity_neq_0; assumption.
  rewrite Hr.
  unfold root_multiplicity; simpl.
  rewrite Hini, Hfin; simpl.
  rewrite skipn_pad; simpl.
  rewrite Nat.sub_diag; simpl.
  rewrite nat_num_Qnat; simpl.
  rewrite fold_char_pol with (αj := αj).
  rewrite <- Hini, <- Hfin.
  remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
  remember (List.map (term_of_point pol) pl) as tl eqn:Htl .
  remember (make_char_pol R j tl) as cpol eqn:Hcpol .
  assert (cpol = al (Φq pol ns)) as Hphi.
   rewrite Φq_pol.
   rewrite <- Hpl, <- Htl.
   rewrite Hini; simpl.
   rewrite nat_num_Qnat, <- Hcpol.
   reflexivity.

   destruct (ac_zerop (lap_mod_deg_1 cpol c)) as [H₁| H₁].
    2: rewrite Nat.mul_0_r; apply Nat.le_0_l.

    rewrite List.map_app; simpl.
    rewrite length_char_pol_succ.
     rewrite Hfin; simpl.
     rewrite nat_num_Qnat.
     symmetry in Hr.
     remember Hr as H; clear HeqH.
     eapply list_root_mult_succ_if in H; eauto .
     destruct H as (Hlen, (Hz, Hlrm)).
     rewrite <- Hphi in Hlrm.
     rewrite Hcpol in Hlrm.
     erewrite length_char_pol in Hlrm; eauto .
     rewrite Nat.pred_succ in Hlrm.
     rewrite <- Hcpol in Hlrm.
     rewrite Hlrm.
bbb.
*)

(*
Theorem find_coeff_step₄₂ : ∀ pol ns m c pol₁ ns₁ i di p dp np,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
(*
  → root_multiplicity acf c (Φq pol ns) = 1%nat
*)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (0 < p ≤ i)%nat
  → (di ≤ dp + 1)%nat
  → np = next_pow (p + dp) ns₁ m
  → (find_coeff i np m pol₁ ns₁ (i + di) =
     find_coeff (S i - p) np m pol₁ ns₁ (i + di))%K.
Proof.
intros pol ns m c pol₁ ns₁ i di p dp np.
intros Hns HK Hq Hc (*Hr*) Hpol₁ Hns₁ (Hp, Hpi) Hdip Hnp.
bbb.
Check find_coeff_step₄₂.
*)

Theorem root_tail_split_1st₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ r,
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

 rename H₁ into Hnz₁.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
  rewrite Nat.add_0_r in H.
  pose proof (Hri O) as Hr₀; simpl in Hr₀.
  rewrite <- Hc in Hr₀.
  rewrite Hr₀ in H.
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

          clear H.
          pose proof (Hri 1%nat) as H; simpl in H.
          rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
          rewrite <- Hc₁ in H.
          rewrite H; assumption.

         apply List.in_or_app; right; left; assumption.

        clear H.
        remember Hns₁₁ as H; clear HeqH.
        unfold newton_segments in H.
        unfold points_of_ps_polynom in H.
        apply ini_fin_ns_in_init_pts in H.
        rewrite <- Hini₁; destruct H; assumption.

      remember Hns₁₁ as H; clear HeqH.
      eapply r_n_next_ns in H; eauto .
       rewrite Nat.add_0_r in H.
       destruct H as (αj₂, (αk₂, H)).
       destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
       pose proof (Hri 1%nat) as H; simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
       rewrite H in Hfin₂; clear H.
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
               unfold mh_of_m in Heqmj'.
               erewrite <- qden_αj_is_ps_polord in Heqmj'; eauto .
               rewrite Hmj in Heqmj'.
               rewrite Z.div_mul in Heqmj'; auto; subst mj'.
               remember Heqq₂ as H; clear HeqH.
               eapply q_eq_1_any_r in H; eauto .
                Focus 2.
                clear H.
                pose proof (Hri 2%nat) as H.
                remember 1%nat as one in H; simpl in H.
                rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
                subst one; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                rewrite H; assumption.

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
                destruct (zerop i) as [H₂| H₂].
                 subst i.
                 apply Nat.le_0_r in H₁.
                 rewrite <- Z2Nat.inj_0 in H₁.
                 apply Z2Nat.inj in H₁; try reflexivity.
                  rewrite H₁ in H₃; simpl in H₃.
                  exfalso; revert H₃; apply Pos2Z_ne_0.

                  destruct p₂ as [| p₂| p₂]; auto; [ reflexivity | idtac ].
                  pose proof (Pos2Z.is_nonneg mj₂) as H.
                  rewrite H₃ in H.
                  apply Z.nlt_ge in H.
                  exfalso; apply H.
                  apply Z.mul_neg_pos; [ apply Pos2Z.neg_is_neg | idtac ].
                  rewrite <- Nat2Z.inj_0.
                  apply Nat2Z.inj_lt; assumption.

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
bbb.
                 eapply find_coeff_step₄₂; eauto .
                  split; [ idtac | fast_omega Hcmp ].
                  rewrite Hnpow.
bbb.
  Hdr : (0 <= ' mj₂ / ' rq)%Z
  ============================
   (0 < Z.to_nat (' mj₂ / ' rq))%nat


continuing using RootHeadTail.v around line 2279
*)

(*
Theorem root_tail_from_0₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
remember (m * q₀)%positive as m₁.
bbb.
destruct b; [ subst m₁; eapply root_tail_split_1st; eauto  | idtac ].
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
