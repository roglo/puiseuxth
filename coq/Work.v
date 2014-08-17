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
eapply hd_newton_segments in H; eauto .
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
   eapply hd_newton_segments; eauto .

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
    (∀ j, (j < i)%nat → zerop_1st_n_const_coeff j pol ns = false) ∧
    zerop_1st_n_const_coeff i pol ns = true.
Proof.
intros pol ns n Hz.
revert pol ns Hz.
induction n; intros.
 exists O.
 split; [ reflexivity | idtac ].
 split; [ idtac | assumption ].
 intros j Hj.
 exfalso; revert Hj; apply Nat.nlt_0_r.

 simpl in Hz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  exists O.
  split; [ apply Nat.le_0_l | idtac ].
  split.
   intros j Hj.
   exfalso; revert Hj; apply Nat.nlt_0_r.

   simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

  apply IHn in Hz.
  destruct Hz as (i, (Hin, (Hji, Hz))).
  exists (S i).
  split.
   apply Nat.succ_le_mono in Hin; assumption.

   split.
    intros j Hj.
    destruct j; simpl.
     destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
     contradiction.

     destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | idtac ].
     apply Hji, Nat.succ_lt_mono; assumption.

    simpl.
    destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Theorem zzz : ∀ pol ns pol₁ c m,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns pol₁ c m Hns Hm Hc Hr Hpol₁.
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
    apply lowest_zerop_1st_n_const_coeff in Hz.
    destruct Hz as (i, (Hin, (Hji, Hz))).
bbb.
     Focus 2.
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
bbb.
     clear Hu Hofs HN Hη Hz.
(**)
clear H₁.
revert m pol ns c pol₁ ns₁ q₀ Hns Hm Hc Hr Hpol₁ Hns₁ Hq₀ Ha.
(*
     revert m pol ns c pol₁ ns₁ q₀ Hns Hm Hc Hr Hpol₁ H₁ Hns₁ Hq₀ Ha.
*)
     induction N; intros.
      simpl in Ha.
      remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
      remember (next_lap (al pol₁) (β ns₁) (γ ns₁) c₁) as la₂ eqn:Hla₂ .
      apply List.In_split in Ha.
      destruct Ha as (l₁, (l₂, Ha)).
      remember (ps_lap_nth (List.length l₁) la₂) as b eqn:Hb .
      rename H into Huofs.
      remember Hb as H; clear HeqH.
      rewrite Ha in H; simpl in H.
      unfold ps_lap_nth in H; simpl in H.
      rewrite List.app_nth2 in H; auto.
      rewrite Nat.sub_diag in H; simpl in H.
      move H at top; subst b.
      subst a.
(**)
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       unfold ps_poly_nth, apply_poly in H₁.
       destruct l₁ as [| x₁].
        simpl in Ha; simpl.
        unfold next_lap in Hla₂.
bbb.
      remember Hns₁ as H; clear HeqH.
      eapply r_1_next_ns in H; eauto .
      destruct H as (αj₁, (αk₁, H)).
      destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
      remember Hns₁ as H; clear HeqH.
      eapply hd_newton_segments in H; eauto .
      rename H into Hns₁i.
      remember Hns₁i as H; clear HeqH.
      eapply f₁_orders in H; eauto .
      destruct H as (Hall, (Haftr, Hforr)).
      unfold ps_poly_nth in Hall.
      unfold next_pol in Hall; simpl in Hall.
      rewrite <- Hla₂ in Hall.
      apply Hall.

      remember (S N) as SN in Ha; simpl in Ha; subst SN.
      remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
      remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
      remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
      remember (m * q₀)%positive as m₁.
      destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₂| H₂].
       Focus 2.
       eapply IHN with (pol := pol₁) (ns := ns₁) (m := m₁); eauto .
        rename H into Huofs.
        remember Hns₁ as H; clear HeqH.
        eapply r_1_next_ns in H; eauto .
        destruct H as (αj₁, (αk₁, H)).
        destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
        remember Hns₁ as H; clear HeqH.
        eapply hd_newton_segments in H; eauto .

        rewrite Heqm₁.
        eapply next_pol_in_K_1_mq with (ns := ns); eauto .

        eapply multiplicity_1_remains with (ns := ns); eauto .
bbb.

    unfold ps_pol_apply.
    unfold apply_poly.
    remember (S N) as SN.
    unfold apply_lap.
    simpl.
    subst SN; simpl.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
bbb.
   ============================
    (0
     ≤ order
         (ps_pol_apply (nth_pol (S N) pol₁ ns₁)
            (root_tail (m * q₀) (S N) pol₁ ns₁)))%Qbar

(*
intros pol ns pol₁ c m Hns Hm Hc Hr Hpol₁.
destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 exists 0%ps.
 Focus 2.
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
 remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
 exists s; intros i.
 remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
 symmetry in Hofs.
 destruct ofs as [ofs| ].
  Focus 2.
  exists (ps_pol_apply pol₁ s).
  split; [ rewrite rng_sub_0_r; reflexivity | idtac ].
  unfold order in Hofs.
  remember (ps_terms (ps_pol_apply pol₁ s)) as t eqn:Ht .
  remember (null_coeff_range_length R t 0) as v eqn:Hv .
  symmetry in Hv.
  destruct v; [ discriminate Hofs | idtac ].
  apply null_coeff_range_length_iff in Hv.
  unfold null_coeff_range_length_prop in Hv.
  simpl in Hv; apply Hv.
bbb.
*)

End theorems.
