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
Require Import Puiseux.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma root_tail_when_r_1 : ∀ pol ns pol₁ ns₁ c m q₀ b,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n,
    (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b n pol₁ ns₁ +
       ps_monom 1%K (γ_sum b n pol₁ ns₁) *
       root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n.
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
  rewrite root_tail_from_0; eauto .
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
   eapply root_tail_sep_1st_monom; eauto .
   rewrite <- Nat.add_succ_r.
   apply zerop_1st_n_const_coeff_false_iff.
   assumption.
Qed.

Lemma β_lower_bound : ∀ pol ns pol₁ ns₁ m η,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → η = 1 # (2 * m * q_of_m m (γ ns))
  → ∀ n nsn,
    zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → nsn = nth_ns n pol₁ ns₁
    → η < β nsn.
Proof.
intros pol ns pol₁ ns₁ m η Hns Hm Hr Hpol₁ Hns₁ Hη n nsn Hnz Hnsn.
remember Hns as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
eapply r_1_nth_ns in H; eauto .
destruct H as (αjn, (αkn, H)).
destruct H as (_, (Hinin, (Hfinn, (Hαjn, Hαkn)))).
unfold β.
rewrite Hinin; simpl.
unfold Qnat; simpl.
rewrite rng_mul_0_l, rng_add_0_r.
remember Hpol₁ as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; eauto .
rename H into HK₁.
pose proof (Hnz O (Nat.le_0_l n)) as Hnz₀.
simpl in Hnz₀.
remember Hns₁ as H; clear HeqH.
eapply r_1_next_ns in H; eauto .
destruct H as (αj₁, (αk₁, H)).
destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
remember Hns₁ as H; clear HeqH.
eapply List_hd_in in H; eauto .
 rename H into Hns₁i.
 remember HK₁ as H; clear HeqH.
 eapply lap_forall_nth with (ns := ns₁) in H; eauto .
  rename H into HKn.
  remember (nth_pol n pol₁ ns₁) as poln eqn:Hpoln .
  remember Hns₁i as H; clear HeqH.
  eapply nth_in_newton_segments with (n := n) in H; eauto .
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

   eapply multiplicity_1_remains with (ns := ns); eauto .

  eapply multiplicity_1_remains with (ns := ns); eauto .

  remember (m * q_of_m m (γ ns))%positive as m₁ eqn:Hm₁ .
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  eapply q_eq_1 with (ns := ns); eauto .
   subst m₁.
   apply ps_lap_forall_forall.
    clear H.
    intros a b Hab H.
    rewrite <- Hab; assumption.

    intros a Ha.
    apply in_K_1_m_lap_mul_r_compat.
    revert a Ha.
    apply ps_lap_forall_forall; auto.
    clear H.
    intros a b Hab H.
    rewrite <- Hab; assumption.

   rewrite Pos.mul_1_r; assumption.

 clear H.
 intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.
Qed.

Theorem eq_Qbar_eq : ∀ a b, a = b → (a = b)%Qbar.
Proof. intros a b Hab; subst a; reflexivity. Qed.

Theorem eq_Qbar_qinf : ∀ a, (a = ∞)%Qbar → a = ∞%Qbar.
Proof. intros a H; destruct a; auto; inversion H. Qed.

Lemma root_head_from_cγ_list_succ_r : ∀ pol ns pol₁ ns₁ c n i,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → zerop_1st_n_const_coeff n pol₁ ns₁ = false
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → (root_head_from_cγ_list pol ns 0 n (S i) =
      ps_monom 1%K (γ ns) * root_head_from_cγ_list pol₁ ns₁ 0 n i)%ps.
Proof.
intros pol ns pol₁ ns₁ c n i Hc Hpol₁ Hns₁ Hnz Hnz₁.
revert pol ns pol₁ ns₁ c i Hc Hpol₁ Hns₁ Hnz Hnz₁.
induction n; intros.
 simpl.
 unfold γ_sum; simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite summation_shift; [ idtac | fast_omega  ].
 rewrite Nat_sub_succ_1.
 do 2 rewrite rng_add_0_r.
 simpl.
 rewrite <- Hc, <- Hpol₁, <- Hns₁.
 rewrite rng_add_comm.
 rewrite ps_monom_add_r.
 apply ps_mul_comm.

 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz.

  remember (S i) as si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  subst si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂.
  unfold γ_sum; simpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | fast_omega  ].
  rewrite Nat_sub_succ_1.
  destruct (ps_zerop R (ps_poly_nth 0 (nth_pol i pol₂ ns₂))) as [H₂| H₂].
   do 2 rewrite rng_add_0_r.
   rewrite rng_add_comm.
   rewrite ps_monom_add_r.
   simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   apply ps_mul_comm.

   simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   rewrite ps_mul_add_distr_l.
   apply rng_add_compat.
    rewrite rng_add_comm; simpl.
    rewrite ps_monom_add_r.
    apply ps_mul_comm.

    apply IHn with (c := c); auto.
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    apply zerop_1st_n_const_coeff_false_iff.
    clear i H₂.
    intros i Hin.
    destruct i; [ assumption | simpl ].
    rewrite <- Hc₁, <- Hpol₂, <- Heqns₂.
    apply Hnz.
    fast_omega Hin.
Qed.

Lemma apply_nth_pol : ∀ pol ns y n,
  let qr := Q_ring in
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_pol_apply pol
       (root_head 0 n pol ns + ps_monom 1%K (γ_sum 0 n pol ns) * y) =
     ps_monom 1%K (Σ (i = 0, n), β (nth_ns i pol ns)) *
     ps_pol_apply (nth_pol (S n) pol ns) y)%ps.
Proof.
intros; revert H; intros Hnz.
revert pol ns y Hnz.
induction n; intros.
 unfold root_head; simpl.
 unfold γ_sum, summation; simpl.
 unfold next_pol; simpl.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 unfold next_lap; simpl.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 rewrite apply_lap_mul; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite rng_mul_assoc; simpl.
 rewrite <- ps_monom_add_r.
 rewrite rng_add_opp_r; simpl.
 rewrite ps_mul_1_l.
 rewrite apply_lap_compose; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  do 2 rewrite rng_add_0_r.
  rewrite rng_add_comm; reflexivity.

 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | fast_omega  ].
  rewrite Nat_sub_succ_1.
  remember (S n) as sn in |- *; simpl.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite ps_monom_add_r.
  rewrite <- rng_mul_assoc.
  subst sn; simpl.
  erewrite <- nth_pol_n with (pol₁ := pol₁) (ns₁ := ns₁); eauto .
  erewrite <- nth_pol_succ; eauto ; [ idtac | erewrite nth_c_root; eauto  ].
  remember (S n) as sn in |- *; simpl.
  unfold root_head; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₂| H₂].
   contradiction.

   clear H₂.
   rewrite Heqsn in |- * at 1; simpl.
   rewrite <- Hc, <- Hpol₁.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l n)) as H; contradiction.

    subst sn.
    rewrite <- IHn; auto.
    unfold root_head; simpl.
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
     contradiction.

     clear H₃.
     unfold γ_sum at 1, summation; simpl.
     rewrite rng_add_0_r.
     unfold γ_sum.
     rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
     rewrite summation_shift; [ idtac | fast_omega  ].
     rewrite Nat_sub_succ_1; simpl.
     rewrite <- Hc, <- Hpol₁, <- Hns₁.
     rewrite ps_monom_add_r.
     remember Σ (i = 0, n), nth_γ i pol₁ ns₁ as sγ eqn:Hsγ .
     rewrite <- ps_mul_assoc.
     remember (ps_monom 1%K sγ * y)%ps as u eqn:Hu .
     rewrite Hpol₁ in |- * at 1; simpl.
     unfold next_pol; simpl.
     unfold ps_pol_apply; simpl.
     unfold apply_poly; simpl.
     unfold next_lap; simpl.
     rewrite apply_lap_mul; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     rewrite rng_mul_assoc; simpl.
     rewrite <- ps_monom_add_r.
     rewrite rng_add_opp_r; simpl.
     rewrite ps_mul_1_l.
     rewrite apply_lap_compose; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     symmetry; rewrite ps_add_comm; symmetry.
     rewrite ps_mul_add_distr_l.
     rewrite ps_add_assoc.
     rewrite root_head_from_cγ_list_succ_r; eauto .
     reflexivity.
Qed.

Lemma Qnat_succ : ∀ n x, x * Qnat (S n) == x * Qnat n + x.
Proof.
intros n x.
unfold Qnat.
setoid_replace x with (x * 1) at 3.
 rewrite <- rng_mul_add_distr_l.
 apply rng_mul_compat_l; simpl.
 unfold Qeq; simpl.
 do 2 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r, Z.add_1_r.
 apply Zpos_P_of_succ_nat.

 rewrite rng_mul_1_r; reflexivity.
Qed.

Lemma summation_all_lt : ∀ f n x,
  let qr := Q_ring in
  (∀ i : nat, i ≤ n → x < f i)
  → x * Qnat (S n) < Σ (i = 0, n), f i.
Proof.
intros f n x qr Hi.
induction n.
 unfold Qnat, summation; simpl.
 rewrite rng_add_0_r.
 rewrite rng_mul_1_r.
 apply Hi; reflexivity.

 rewrite summation_split_last; [ simpl | apply Nat.le_0_l ].
 rewrite Qnat_succ.
 apply Qplus_lt_le_compat.
  apply IHn.
  intros i Hin; apply Hi.
  fast_omega Hin.

  apply Qlt_le_weak.
  apply Hi; reflexivity.
Qed.

Lemma series_0_ps_0 : ∀ p,
  (∀ i, ((ps_terms p) .[i] = 0)%K)
  → (p = 0)%ps.
Proof.
intros p Hi.
apply order_inf.
remember (order p) as op eqn:Hop .
symmetry in Hop.
unfold order in Hop.
remember (null_coeff_range_length R (ps_terms p) 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; auto.
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv; simpl in Hv.
destruct Hv as (Hiv, Hv).
rewrite Hi in Hv.
exfalso; apply Hv; reflexivity.
Qed.

Lemma order_root_tail_nonneg : ∀ pol ns c pol₁ ns₁ m q₀ n,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (0 ≤ order (root_tail (m * q₀) n pol₁ ns₁))%Qbar.
Proof.
intros pol ns c pol₁ ns₁ m q₀ n Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
unfold root_tail.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁; [ rewrite order_0; constructor | idtac ].
revert pol ns c pol₁ ns₁ m q₀ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hz₁.
induction n; intros.
 simpl.
 unfold order; simpl.
 remember Hns₁ as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
  remember (root_tail_series_from_cγ_list (m * q₀) pol₁ ns₁) as t.
  remember (null_coeff_range_length R {| terms := t |} 0) as v eqn:Hv .
  symmetry in Hv.
  destruct v; [ idtac | constructor ].
  apply Qbar.qfin_le_mono.
  unfold Qle; simpl.
  rewrite Z.mul_1_r.
  remember (m * q₀)%positive as m₁.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_shuffle0.
  rewrite Z.div_mul_cancel_r; auto.
  apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
  apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
  apply Z.mul_nonneg_nonneg; auto.
  apply Z.lt_le_incl; assumption.

  rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
  apply (Hz₁ O); reflexivity.

 simpl in Hz₁; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hz₁.

  remember (m * q₀)%positive as m₁.
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  eapply IHn with (ns := ns₁) (pol := pol₁); eauto .
   remember Hns₁ as H; clear HeqH.
   eapply r_1_next_ns in H; eauto .
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
   eapply List_hd_in; eauto .
   intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

   rewrite Heqm₁.
   eapply next_pol_in_K_1_mq; eauto .

   symmetry.
   rewrite Heqm₁.
   eapply q_eq_1; eauto .
   eapply next_pol_in_K_1_mq; eauto .

   eapply multiplicity_1_remains; eauto .
Qed.

Lemma order_pol_apply_nonneg : ∀ pol y,
  (∀ a, a ∈ al pol → (0 ≤ order a)%Qbar)
  → (0 ≤ order y)%Qbar
  → (0 ≤ order (ps_pol_apply pol y))%Qbar.
Proof.
intros pol y Ha Hy.
unfold ps_pol_apply, apply_poly.
remember (al pol) as la; clear Heqla.
induction la as [| a]; intros; simpl.
 rewrite order_0; constructor.

 eapply Qbar.le_trans; [ idtac | apply order_add ].
 rewrite order_mul; auto.
 apply Qbar.min_glb.
  eapply Qbar.le_trans; eauto .
  rewrite Qbar.add_comm.
  apply Qbar.le_sub_le_add_l.
  rewrite Qbar.sub_diag.
  apply IHla.
  intros b Hb.
  apply Ha; right; assumption.

  apply Ha; left; reflexivity.
Qed.

Theorem eq_1_0_ps_0 : (1 = 0)%K → ∀ a, (a = 0)%ps.
Proof.
intros H a.
apply order_inf.
unfold order.
remember (null_coeff_range_length R (ps_terms a) 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; auto.
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv.
destruct Hv as (_, Hv).
exfalso; apply Hv; simpl.
apply eq_1_0_all_0; assumption.
Qed.

Lemma lowest_zerop_1st_n_const_coeff : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = true
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ zerop_1st_n_const_coeff (pred i) pol ns = false) ∧
    zerop_1st_n_const_coeff i pol ns = true.
Proof.
intros pol ns n Hz.
revert pol ns Hz.
induction n; intros.
 exists O.
 split; [ reflexivity | idtac ].
 split; [ left; reflexivity | assumption ].

 simpl in Hz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  exists O.
  split; [ apply Nat.le_0_l | idtac ].
  split; [ left; reflexivity | simpl ].
  destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

  apply IHn in Hz.
  destruct Hz as (i, (Hin, (Hji, Hz))).
  destruct Hji as [Hji| Hji].
   subst i.
   simpl in Hz.
   remember (ac_root (Φq pol ns)) as c eqn:Hc .
   remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    exists 1%nat.
    split; [ fast_omega  | simpl ].
    destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | idtac ].
    split; [ right; reflexivity | idtac ].
    rewrite <- Hc, <- Hpol₁.
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.

    discriminate Hz.

   destruct i.
    simpl in Hji, Hz.
    rewrite Hji in Hz.
    discriminate Hz.

    simpl in Hji.
    exists (S (S i)).
    split; [ fast_omega Hin | idtac ].
    split.
     right; simpl.
     destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
     contradiction.

     remember (S i) as si; simpl; subst si.
     destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Lemma first_null_coeff : ∀ pol₁ ns₁ i a₁ la₁,
  zerop_1st_n_const_coeff i pol₁ ns₁ = false
  → zerop_1st_n_const_coeff (S i) pol₁ ns₁ = true
  → al (nth_pol (S i) pol₁ ns₁) = [a₁ … la₁]
  → (a₁ = 0)%ps.
Proof.
intros pol₁ ns₁ i a₁ la₁ Hnz₁ Hz₁ Hla₁.
revert pol₁ ns₁ a₁ la₁ Hnz₁ Hz₁ Hla₁.
induction i; intros.
 simpl in Hnz₁, Hz₁, Hla₁.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₂| H₂].
   unfold ps_poly_nth, ps_lap_nth in H₂; simpl in H₂.
   unfold next_pol in Hpol₂.
   rewrite Hla₁ in Hpol₂.
   rewrite Hpol₂ in H₂; simpl in H₂.
   assumption.

   discriminate Hz₁.

 remember (S i) as si; simpl in Hz₁, Hla₁; subst si.
 simpl in Hnz₁.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  eapply IHi; eauto .
Qed.

Theorem List_In_nth : ∀ α a la (d : α),
  a ∈ la
  → ∃ n, a = List.nth n la d.
Proof.
intros u a la d Ha.
revert a Ha.
induction la as [| b]; intros; [ contradiction | idtac ].
simpl in Ha.
destruct Ha as [Ha| Ha].
 subst b.
 exists O; reflexivity.

 apply IHla in Ha.
 destruct Ha as (n, Ha).
 exists (S n); simpl.
 assumption.
Qed.

Theorem root_after_r_eq_1 : ∀ pol ns pol₁ c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns pol₁ c Hns Hc Hr Hpol₁.
pose proof (exists_pol_ord R pol) as H.
destruct H as (m, Hm).
destruct (ac_zerop 1%K) as [H₀| H₀].
 exists 0%ps.
 unfold ps_pol_apply, apply_poly.
 unfold apply_lap; simpl.
 remember (al pol₁) as la; clear Heqla.
 destruct la as [| a]; [ reflexivity | simpl ].
 rewrite rng_mul_0_r, rng_add_0_l.
 apply eq_1_0_ps_0; assumption.

 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  exists 0%ps.
  unfold ps_pol_apply, apply_poly.
  unfold apply_lap.
  unfold ps_poly_nth in H₁.
  destruct (al pol₁) as [| a la]; [ reflexivity | simpl ].
  unfold ps_lap_nth in H₁; simpl in H₁.
  rewrite rng_mul_0_r, rng_add_0_l; assumption.

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
   rewrite root_tail_when_r_1 with (n := N) in Hofs; eauto .
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
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
      discriminate Hz.

      exists (root_head 0 (pred i) pol₁ ns₁).
      destruct i.
       rewrite Nat.pred_0 in Hpi.
       rewrite Hpi in Hz; discriminate Hz.

       rewrite Nat.pred_succ in Hpi.
       rewrite Nat.pred_succ.
       remember Hpi as H; clear HeqH.
       eapply apply_nth_pol with (y := 0%ps) in H.
       rewrite rng_mul_0_r, rng_add_0_r in H.
       rewrite H.
       unfold ps_pol_apply, apply_poly.
       remember (S i) as si.
       unfold apply_lap; simpl.
       remember (al (nth_pol si pol₁ ns₁)) as la₁ eqn:Hla₁ .
       symmetry in Hla₁.
       destruct la₁ as [| a₁].
        simpl.
        rewrite rng_mul_0_r; reflexivity.

        simpl.
        rewrite rng_mul_0_r, rng_add_0_l.
        subst si.
        rewrite first_null_coeff with (a₁ := a₁); eauto .
        rewrite rng_mul_0_r; reflexivity.

    simpl.
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
      assert (zerop_1st_n_const_coeff i pol₁ ns₁ = false).
       rewrite zerop_1st_n_const_coeff_false_iff in Hz.
       apply zerop_1st_n_const_coeff_false_iff.
       intros j Hj.
       apply Hz.
       transitivity i; assumption.

       eapply β_lower_bound with (n := i); eauto .

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
     apply order_pol_apply_nonneg.
      Focus 2.
      eapply order_root_tail_nonneg; eauto .

      intros a Ha.
      remember (nth_pol N pol₁ ns₁) as polN eqn:HpolN .
      remember (nth_ns N pol₁ ns₁) as nsN eqn:HnsN .
      assert (List.In nsN (newton_segments polN)) as HnsNi.
       Focus 2.
       rename H into Huofs.
       remember HnsNi as H; clear HeqH.
       eapply f₁_orders in H; eauto .
       erewrite <- nth_pol_succ in H; eauto .
        destruct H as (H, _).
        apply List_In_nth with (d := 0%ps) in Ha.
        destruct Ha as (n, Hn).
        rewrite Hn.
        apply H.

        symmetry.
        apply nth_c_root; eauto .

       rewrite zerop_1st_n_const_coeff_false_iff in Hz.
       remember (m * q₀)%positive as m₁.
       eapply nth_in_newton_segments with (ns₁ := ns₁) (m := m₁); eauto .
        clear H.
        remember Hns₁ as H; clear HeqH.
        eapply r_1_next_ns in H; eauto .
        destruct H as (αj₁, (αk₁, H)).
        destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
        eapply List_hd_in; eauto .
        intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

        rewrite Heqm₁.
        eapply next_pol_in_K_1_mq; eauto .

        eapply multiplicity_1_remains; eauto .

   exists s.
   apply order_inf; assumption.
Qed.

Theorem root_when_r_eq_1_at_once : ∀ pol ns c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → ∃ s, (ps_pol_apply pol s = 0)%ps.
Proof.
intros pol ns c Hns Hc Hr.
remember (zerop_1st_n_const_coeff 0 pol ns) as z eqn:Hz .
symmetry in Hz.
destruct z.
 simpl in Hz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₂| H₂].
  exists 0%ps.
  unfold ps_pol_apply, apply_poly, apply_lap; simpl.
  unfold ps_poly_nth, ps_lap_nth in H₂.
  destruct (al pol) as [| a la]; [ reflexivity | idtac ].
  simpl in H₂; simpl.
  rewrite rng_mul_0_r, rng_add_0_l; assumption.

  discriminate Hz.

 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember Hns as H; clear HeqH.
 eapply root_after_r_eq_1 with (pol₁ := pol₁) in H; eauto .
 destruct H as (s₁, Hs₁).
 exists (root_head 0 0 pol ns + ps_monom 1%K (γ_sum 0 0 pol ns) * s₁)%ps.
 rewrite apply_nth_pol; auto.
 erewrite nth_pol_succ; eauto .
 simpl; rewrite <- Hpol₁, Hs₁.
 rewrite rng_mul_0_r; reflexivity.
Qed.

Lemma no_newton_segments : ∀ pol,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → newton_segments pol = []
  → (∀ i, (0 < i)%nat → (ps_poly_nth i pol = 0)%ps).
Proof.
(* perhaps simplifiable *)
intros pol Hnz Hns i Hi.
destruct i; [ exfalso; revert Hi; apply Nat.lt_irrefl | idtac ].
clear Hi.
unfold newton_segments in Hns.
unfold lower_convex_hull_points in Hns.
unfold points_of_ps_polynom in Hns.
unfold points_of_ps_lap in Hns.
remember (al pol) as la eqn:Hla .
symmetry in Hla.
unfold ps_poly_nth.
unfold ps_poly_nth in Hnz.
rewrite Hla in Hnz; rewrite Hla.
clear pol Hla.
unfold points_of_ps_lap_gen in Hns.
unfold qpower_list in Hns.
remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
unfold ps_lap_nth in Hnz.
unfold ps_lap_nth.
revert la Hnz Hns.
induction i; intros.
 destruct la as [| a].
  exfalso; apply Hnz; reflexivity.

  simpl in Hnz; simpl.
  simpl in Hns.
  remember (f (O, a)) as fa.
  rewrite Heqf in Heqfa.
  simpl in Heqfa.
  unfold pair_rec in Heqfa; simpl in Heqfa.
  subst fa; simpl in Hns.
  apply order_fin in Hnz.
  remember (order a) as oa.
  symmetry in Heqoa.
  destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
  simpl in Hns.
  remember (filter_finite_ord R (List.map f (power_list 1 la))) as pts.
  symmetry in Heqpts.
  destruct pts; [ idtac | discriminate Hns ].
  clear Hns Hnz.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (1%nat, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb.
  simpl in Heqfb.
  subst fb; simpl in Heqpts.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; auto.
   discriminate Heqpts.

   apply order_inf; assumption.

 destruct la as [| a]; [ reflexivity | simpl ].
 simpl in Hnz.
 simpl in Hns.
 remember (f (O, a)) as fa.
 rewrite Heqf in Heqfa.
 simpl in Heqfa.
 unfold pair_rec in Heqfa; simpl in Heqfa.
 subst fa; simpl in Hns.
 apply order_fin in Hnz.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
 simpl in Hns.
 remember (filter_finite_ord R (List.map f (power_list 1 la))) as pts.
 symmetry in Heqpts.
 destruct pts; [ idtac | discriminate Hns ].
 clear Hns.
 clear Hnz.
 revert Heqf Heqpts; clear; intros.
 remember 1%nat as pow; clear Heqpow.
 revert i pow Heqpts.
 induction la as [| a]; intros; [ reflexivity | idtac ].
 simpl in Heqpts.
 remember (f (pow, a)) as fa.
 rewrite Heqf in Heqfa.
 unfold pair_rec in Heqfa.
 simpl in Heqfa.
 subst fa; simpl in Heqpts.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ discriminate Heqpts | simpl ].
 destruct i.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (S pow, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb; simpl in Heqfb.
  subst fb.
  apply order_inf.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; [ discriminate Heqpts | reflexivity ].

  eapply IHla; eauto .
Qed.

Theorem zzz : ∀ pol ns,
  ns ∈ newton_segments pol
  → (∃ n, ∀ poln nsn cn,
     poln = nth_pol n pol ns
     → nsn = nth_ns n pol ns
     → cn = nth_c n pol ns
     → root_multiplicity acf cn (Φq poln nsn) = 1%nat)
  → ∃ s, (ps_pol_apply pol s = 0)%ps.
Proof.
intros pol ns Hns Hr.
destruct Hr as (n, Hr).
remember (nth_pol n pol ns) as poln eqn:Hpoln  in |- *.
remember (nth_ns n pol ns) as nsn eqn:Hnsn  in |- *.
remember (nth_c n pol ns) as cn eqn:Hcn  in |- *.
remember Hpoln as H; clear HeqH.
eapply Hr in H; eauto ; clear Hr.
rename H into Hr.
revert pol ns poln nsn cn Hns Hpoln Hnsn Hcn Hr.
induction n; intros.
 simpl in Hpoln, Hnsn, Hcn.
 subst poln nsn.
 eapply root_when_r_eq_1_at_once; eauto .

 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  exists 0%ps.
  unfold ps_pol_apply, apply_poly, apply_lap; simpl.
  unfold ps_poly_nth, ps_lap_nth in H₁.
  destruct (al pol) as [| a la]; [ reflexivity | idtac ].
  simpl in H₁; simpl.
  rewrite rng_mul_0_r, rng_add_0_l; assumption.

  simpl in Hpoln, Hnsn, Hcn.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
   pose proof (exists_pol_ord R pol) as H.
   destruct H as (m, Hm).
   exists (ps_monom c (γ ns)).
   eapply f₁_root_f_root with (y₁ := 0%ps); eauto .
    rewrite rng_mul_0_r, rng_add_0_r.
    reflexivity.

    unfold ps_pol_apply, apply_poly, apply_lap; simpl.
    unfold ps_poly_nth, ps_lap_nth in H₂.
    destruct (al pol₁) as [| a la]; [ reflexivity | idtac ].
    simpl in H₂; simpl.
    rewrite rng_mul_0_r, rng_add_0_l; assumption.

   remember (root_multiplicity acf c (Φq pol ns)) as r₁ eqn:Hr₁ .
   symmetry in Hr₁.
   destruct (eq_nat_dec r₁ 1%nat) as [H₃| H₃].
    remember Hpoln as H; clear HeqH.
    eapply IHn in H; eauto .
     destruct H as (s₁, Hs₁).
     exists (root_head 0 0 pol ns + ps_monom 1%K (γ_sum 0 0 pol ns) * s₁)%ps.
     rewrite apply_nth_pol; auto.
      erewrite nth_pol_succ; eauto .
      simpl; rewrite <- Hpol₁, Hs₁.
      rewrite rng_mul_0_r; reflexivity.

      simpl.
      destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₄| H₄]; auto.
      contradiction.

     eapply List_hd_in; eauto .
     clear H; subst r₁.
     pose proof (exists_pol_ord R pol) as H.
     destruct H as (m, Hm).
     remember Hns as H; clear HeqH.
     eapply r_1_next_ns with (m := m) in H; eauto .
     destruct H as (αj₁, (αk₁, H)).
     destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
     intros H; rewrite H in Hns₁; rewrite Hns₁ in Hfin₁; discriminate Hfin₁.

    pose proof (exists_pol_ord R pol) as H.
    destruct H as (m, Hm).
    remember Hpoln as H; clear HeqH.
    remember (newton_segments pol₁) as nsl₁ eqn:Hnsl₁ .
    symmetry in Hnsl₁.
    destruct nsl₁ as [| ns₂ nsl₁].
     Focus 2.
     eapply IHn in H; eauto .
      destruct H as (s₁, Hs₁).
      exists (ps_monom c (γ ns) + ps_monom 1%K (γ ns) * s₁)%ps.
      eapply f₁_root_f_root; eauto .
      reflexivity.

      rewrite <- Hnsl₁ in Hns₁.
      eapply List_hd_in; eauto .
      clear H.
      rewrite Hnsl₁; intros H; discriminate H.

     simpl in Hns₁.
     subst ns₁.
     simpl in Hpoln, Hnsn, Hcn; clear H.
     remember Hns as H; clear HeqH.
     eapply f₁_orders in H; eauto .
     rewrite Hr₁ in H.
     destruct H as (Hall, (Hlt, Heq)).
     remember H₂ as H; clear HeqH.
     destruct r₁.
      Focus 2.
      eapply no_newton_segments with (i := S r₁) in H; eauto .
       apply order_inf in H.
       rewrite H in Heq.
       contradiction.

       apply Nat.lt_0_succ.

      clear H₃ Hlt H.
bbb.

intros pol ns Hns Hr.
destruct Hr as (n, Hr).
remember (nth_pol n pol ns) as poln eqn:Hpoln  in |- *.
remember (nth_ns n pol ns) as nsn eqn:Hnsn  in |- *.
remember (nth_c n pol ns) as cn eqn:Hcn  in |- *.
remember (zerop_1st_n_const_coeff n pol ns) as z eqn:Hz .
symmetry in Hz.
pose proof (exists_pol_ord R pol) as H.
destruct H as (m, Hm).
remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
remember Hpoln as H; clear HeqH.
eapply Hr in H; eauto .
clear Hr.
rename H into Hrn.
remember (next_pol poln (β nsn) (γ nsn) cn) as polSn eqn:HpolSn .
destruct z.
 Focus 2.
 remember Hrn as H; clear HeqH.
bbb.
 eapply root_after_r_eq_1 with (pol₁ := polSn) in H; eauto .
  destruct H as (s, Hs).
  exists (root_head 0 n pol ns + ps_monom 1%K (γ_sum 0 n pol ns) * s)%ps.
  rewrite apply_nth_pol; eauto ; simpl.
  erewrite <- nth_pol_n; eauto .
  erewrite <- nth_c_root; eauto .
  rewrite <- Hcn, <- HpolSn, Hs.
  rewrite rng_mul_0_r; reflexivity.

  rewrite zerop_1st_n_const_coeff_false_iff in Hz.
  destruct n; [ subst poln nsn; auto | idtac ].
  eapply List_hd_in.
   rewrite Hnsn; simpl.
   eapply nth_ns_n; eauto .
   subst poln; simpl; symmetry.
   eapply nth_pol_n; eauto .

   clear H.
   remember (m * q₀)%positive as m₁.
   remember (nth_pol n pol ns) as poln₁ eqn:Hpoln₁ .
   remember Hpoln as H; clear HeqH; simpl in H.
   erewrite <- nth_pol_n with (pol₁ := pol) in H; eauto .
   eapply r_1_next_ns with (m := m₁) in H; eauto .
    destruct H as (αjn₁, (αkn₁, H)).
    destruct H as (_, (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁)))).
    intros H; rewrite H in Hfinn₁; discriminate Hfinn₁.
bbb.

   clear H.
   pose proof (Hz (S n) (Nat.le_refl (S n))) as H.
   rewrite <- Hpoln in H.
   unfold root_multiplicity in Hrn; simpl in Hrn.
   rewrite Nat.sub_diag in Hrn; simpl in Hrn.
   rewrite skipn_pad in Hrn.
   erewrite nth_ns_succ in Hnsn; eauto .
   rename H into Hnz.
   intros H; rewrite H in Hnsn.
   simpl in Hnsn.
   subst nsn.
   simpl in Hrn.
   unfold nat_num in Hrn; simpl in Hrn.
   unfold ps_poly_nth, ps_lap_nth in Hnz.
   remember (List.nth 0 (al poln) 0%ps) as a₀ eqn:Ha₀ .
   remember [order_coeff a₀; order_coeff a₀ … []] as v eqn:Hv .
   destruct (ac_zerop (lap_mod_deg_1 v cn)) as [H₁| H₁].
    destruct (ac_zerop (lap_mod_deg_1 (lap_div_deg_1 v cn) cn)) as [H₂| H₂].
     discriminate Hrn.

     clear Hrn.
     subst v.
     unfold lap_mod_deg_1 in H₁.
     unfold lap_mod_div_deg_1 in H₁.
     simpl in H₁.
     rewrite rng_mul_0_l, rng_add_0_l in H₁.
     unfold lap_mod_deg_1, lap_div_deg_1 in H₂.
     simpl in H₂.
     rewrite rng_mul_0_l, rng_add_0_l, rng_add_0_l in H₂.
     erewrite nth_c_root in Hcn; eauto .
     remember (nth_ns (S n) pol ns) as nsn eqn:Hnsn .
     assert (degree ac_zerop (Φq poln nsn) ≥ 1)%nat as Hd.
      unfold degree; simpl.
      rewrite Nat.sub_diag; simpl.
      rewrite skipn_pad; simpl.
bbb.
... parti en couille, mais y a quequ'chose à vouar e'd'dans...

End theorems.
