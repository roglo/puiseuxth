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

Theorem zzz : ∀ pol ns pol₁ c m,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns pol₁ c m Hns Hm Hc Hr Hpol₁.
unfold ps_pol_apply.
destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 exists 0%ps.
 Focus 2.
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
 remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
 exists s.
 apply order_inf.
 remember (order (apply_poly pol₁ s)) as ofs eqn:Hofs .
 symmetry in Hofs.
 destruct ofs as [ofs| ]; [ exfalso | reflexivity ].
 subst s.
 remember (1 # 2 * m * q_of_m m (γ ns)) as η eqn:Hη .
 remember (Z.to_nat (Qnum (ofs * η))) as N eqn:HN .
 assert (ofs * η < Qnat N).
bbb.
  subst N; simpl.
  unfold Qnat.
  rewrite Z2Nat.id.
   unfold Qlt; simpl.
   rewrite Z.mul_1_r.
   remember (Qnum ofs * Qnum η)%Z as qq.
   replace qq with (qq * 1)%Z at 1 by fast_omega .
   apply Z.mul_lt_mono_pos_l.
    subst η; simpl in Heqqq; simpl.
    rewrite Z.mul_1_r in Heqqq; subst qq.
    Focus 2.
    subst η; simpl in Heqqq.
    remember (2 * m)%positive as mm; simpl; subst mm.
    rewrite Pos2Z.inj_mul.
    rewrite Pos2Z.inj_mul.
    rewrite Pos2Z.inj_mul.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_assoc, <- Z.mul_assoc, Z.mul_comm.
    apply Z.lt_mul_r.
     apply Z.lt_0_1.

     apply Z.lt_1_2.

     Unfocus.
bbb.
(* choose N so that Σ (j=0,n) βj > ofs *)

intros pol ns pol₁ c m Hns Hm Hc Hr Hpol₁.
unfold ps_pol_apply.
destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 exists 0%ps.
 Focus 2.
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁.
 remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀.
 exists (root_tail (m * q₀) 0 pol₁ ns₁).
 rewrite root_tail_when_r_1 with (n := O); eauto .
 unfold γ_sum, summation; simpl.
 rewrite rng_add_0_r.
 unfold root_head; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
  contradiction.

  clear H₂.
  unfold γ_sum, summation; simpl.
  do 2 rewrite rng_add_0_r.
  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  rewrite Hpol₁.
  unfold next_pol, next_lap.
  unfold apply_poly; simpl.
bbb.

End theorems.
