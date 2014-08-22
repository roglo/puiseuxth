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

Fixpoint nth_r α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_r n₁ pol₁ ns₁
  end.

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

Lemma lowest_i_such_that_ri_lt_r₀ : ∀ pol ns r n,
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

Lemma nth_r_n : ∀ pol ns pol₁ ns₁ c₁ n,
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
Lemma pouet2 : ∀ f ffo ms a₀ a₁ la v₀ v₁ j k αj αk r,
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

(* more general than r_1_j_0_k_1 which could be simplified if this
   lemma works *)
Lemma r_n_j_0_k_n : ∀ pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ m r,
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
  → j₁ = 0%nat ∧ k₁ = r ∧ αj₁ > 0 ∧ αk₁ == 0 ∧ oth_pts ns₁ = [].
Proof.
intros pol ns c pol₁ ns₁ c₁ j₁ αj₁ k₁ αk₁ m r.
intros Hns Hm Hc Hpol₁ Hns₁ Hc₁ Hps₀ Hr Hr₁ Hini₁ Hfin₁.
bbb.
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
 apply Hpos in H; clear Hpos; rename H into Hpos.
 unfold newton_segments in Hns₁; simpl in Hns₁.
 unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
 unfold ps_poly_nth in Hnneg, Hz, Hpos.
 remember (al pol₁) as la.
 destruct la as [| a₀].
  unfold ps_lap_nth in Hz; simpl in Hz.
  rewrite order_0 in Hz; inversion Hz.

  unfold ps_lap_nth in Hnneg, Hz, Hpos.
  simpl in Hz, Hpos.
  unfold points_of_ps_lap in Hns₁.
  unfold points_of_ps_lap_gen in Hns₁.
  simpl in Hns₁.
  remember (order a₀) as v₀.
  symmetry in Heqv₀.
  destruct v₀ as [v₀| ].
bbb.
  destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].

(* more general than r_1_next_ns which could be simplified if this
   lemma works *)
Lemma r_n_next_ns : ∀ pol ns c pol₁ ns₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → root_multiplicity acf c (Φq pol ns) = r
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ∃ αj αk,
    oth_pts ns₁ = [] ∧
    ini_pt ns₁ = (Qnat 0, αj) ∧
    fin_pt ns₁ = (Qnat r, αk) ∧
    (0 < Qnum αj)%Z ∧
    Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ m r Hns Hm Hr Hc Hpol₁ Hns₁ Hpnz.
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns₁ as H; clear HeqH.
bbb.
eapply r_1_j_0_k_1 in H; eauto .

(* more general than r_1_nth_ns which could be simplified if this
   lemma works *)
(*
Lemma r_n_nth_ns : ∀ pol ns c pol₁ ns₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n poln nsn,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → poln = nth_pol n pol₁ ns₁
    → nsn = nth_ns n pol₁ ns₁
    → ∃ αj αk k,
      (0 < k)%nat ∧ (k ≤ r)%nat ∧
      oth_pts nsn = [] ∧
      ini_pt nsn = (Qnat 0, αj) ∧
      fin_pt nsn = (Qnat k, αk) ∧
      (0 < Qnum αj)%Z ∧
      Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ m r Hns Hm Hc Hr Hpol₁ Hns₁.
intros n poln nsn Hpsi Hpoln Hnsn.
remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
revert poln nsn Hpsi Hpoln Hnsn.
revert pol ns c pol₁ ns₁ m q₀ r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
induction n; intros.
 pose proof (Hpsi O (Nat.le_0_l O)) as H; simpl in H.
 rename H into Hnz₁.
 simpl in Hpoln, Hnsn; subst poln nsn.
 remember Hns as H; clear HeqH.
bbb.
 eapply r_1_next_ns in H; eauto .
bbb.
*)

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

Lemma root_tail_split_1st₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (root_tail (m * q₀) 0 pol₁ ns₁ =
     root_head 0 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum 0 0 pol₁ ns₁) *
       root_tail (m * q₀) 1 pol₁ ns₁)%ps.
Proof.
root_tail_split_1st₄₂ < Show Script.
intros pol ns pol₁ ns₁ c m q₀ r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 rename H₁ into Hnz₁.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 remember Hns as H; clear HeqH.
bbb.
 eapply r_1_next_ns in H; eauto .

Lemma root_tail_from_0₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ b r,
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

Lemma root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
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
