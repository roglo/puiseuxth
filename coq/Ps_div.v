(* $Id: Ps_div.v,v 1.23 2013-12-19 10:16:57 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_mul.

Set Implicit Arguments.

Definition ps_inv ps :=
  match null_coeff_range_length rng (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_inv (series_left_shift n (ps_terms ps));
         ps_valnum := - ps_valnum ps - Z.of_nat n;
         ps_comden := ps_comden ps |}
  | ∞ =>
      ps
  end.

Definition ps_left_adjust ps :=
  match null_coeff_range_length rng (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_left_shift n (ps_terms ps);
         ps_valnum := ps_valnum ps + Z.of_nat n;
         ps_comden := ps_comden ps |}
  | ∞ =>
      ps
  end.

Lemma null_coeff_range_length_left_adjust : ∀ n ps,
  null_coeff_range_length rng (ps_terms ps) 0 = fin n
  → null_coeff_range_length rng (ps_terms (ps_left_adjust ps)) 0 = 0%Nbar.
Proof.
intros n ps Hn.
unfold ps_left_adjust; simpl.
rewrite Hn; simpl.
apply null_coeff_range_length_iff.
apply null_coeff_range_length_iff in Hn.
simpl in Hn |- *.
destruct Hn as (Hz, Hnz).
split.
 intros i Hi.
 exfalso; revert Hi; apply Nat.nlt_0_r.

 unfold series_nth in Hnz |- *.
 remember (series_left_shift n (ps_terms ps)) as x eqn:Hx .
 destruct (Nbar.lt_dec 0 (stop x)) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin n) (stop (ps_terms ps))) as [H₂| H₂].
   subst x.
   simpl.
   rewrite Nat.add_0_r; assumption.

   exfalso; apply Hnz; reflexivity.

  exfalso; apply H₁; subst x.
  simpl.
  destruct (Nbar.lt_dec (fin n) (stop (ps_terms ps))) as [H₂| H₂].
   remember (stop (ps_terms ps)) as st eqn:Hst .
   symmetry in Hst.
   destruct st as [st| ].
    apply Nbar.fin_lt_mono.
    apply Nbar.fin_lt_mono in H₂.
    fast_omega H₂.

    constructor.

   exfalso; apply Hnz; reflexivity.
Qed.

Lemma ps_left_adjust_eq : ∀ ps, (ps = ps_left_adjust ps)%ps.
Proof.
intros ps.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 constructor; constructor; simpl.
  erewrite ps_valnum_canonic; try reflexivity; try eassumption.
  erewrite ps_valnum_canonic with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as f; simpl; subst f.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply null_coeff_range_length_left_adjust; eassumption.

  erewrite ps_comden_canonic; try reflexivity; try eassumption.
  erewrite ps_comden_canonic with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as f; simpl; subst f.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply null_coeff_range_length_left_adjust; eassumption.
bbb.

Lemma series_left_shift_0 : ∀ s, (series_left_shift 0 s = s)%ser.
Proof.
intros s.
unfold series_left_shift.
rewrite Nbar.sub_0_r; simpl.
destruct s; reflexivity.
Qed.

Lemma series_shrink_1 : ∀ s, (series_shrink 1 s = s)%ser.
Proof.
intros s.
unfold series_shrink; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.add_sub; [ idtac | intros H; discriminate H ].
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 rewrite divmod_div.
 rewrite Nat.div_1_r.
 constructor; intros n.
 unfold series_nth; simpl.
 rewrite Nat.mul_1_r.
 rewrite Hst; reflexivity.

 constructor; intros n.
 unfold series_nth; simpl.
 rewrite Nat.mul_1_r.
 rewrite Hst; reflexivity.
Qed.

Lemma canonic_ps_1 : canonic_ps 1%ps ≐ 1%ps.
Proof.
remember (null_coeff_range_length rng (ps_terms 1%ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  Focus 2.
  apply null_coeff_range_length_iff in Hn; simpl in Hn.
  destruct Hn as (_, Hn).
  unfold series_nth in Hn.
  simpl in Hn.
  exfalso; apply Hn.
  destruct (Nbar.lt_dec (fin (S n)) 1) as [H₁| H₁].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁.
   apply Nbar.fin_le_mono.
   apply le_n_S, Nat.le_0_l.

   reflexivity.

  constructor; simpl.
   erewrite ps_valnum_canonic; try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   remember Z.gcd as f; simpl; subst f.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   rewrite Z.div_0_l; [ reflexivity | idtac ].
   intros H; discriminate H.

   erewrite ps_comden_canonic; try reflexivity; try eassumption.
   remember Z.gcd as f; simpl; subst f.
   rewrite Z.gcd_1_l.
   reflexivity.

   erewrite ps_terms_canonic; try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   remember Z.gcd as f; simpl; subst f.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   unfold canonify_series; simpl.
   rewrite series_shrink_1.
   rewrite series_left_shift_0; reflexivity.

 apply null_coeff_range_length_inf_iff in Hn.
 exfalso; revert Hn; apply ps_neq_1_0.
Qed.

Lemma series_inv_compat : ∀ a b,
  (a [0] ≠ 0)%rng
  → (a = b)%ser
    → (series_inv a = series_inv b)%ser.
Proof.
intros a b Ha Hab.
remember Ha as Hb; clear HeqHb.
rewrite Hab in Hb.
apply series_mul_compat_l with (c := series_inv a) in Hab.
apply series_mul_compat_r with (c := series_inv b) in Hab.
rewrite series_mul_inv_l in Hab; auto.
rewrite series_mul_1_l in Hab.
rewrite <- series_mul_assoc in Hab.
rewrite series_mul_inv_r in Hab; auto.
rewrite series_mul_1_r in Hab.
symmetry; assumption.
Qed.

Lemma null_coeff_range_length_series_1 :
  null_coeff_range_length rng 1%ser 0 = 0%Nbar.
Proof.
apply null_coeff_range_length_iff; simpl.
split.
 intros i Hi.
 apply Nat.nlt_ge in Hi.
 exfalso; apply Hi, Nat.lt_0_succ.

 unfold series_nth; simpl.
 rewrite if_lt_dec_0_1.
 apply Lfield.neq_1_0.
Qed.

Lemma greatest_series_x_power_series_1 :
  greatest_series_x_power rng 1%ser 0 = O.
Proof.
apply greatest_series_x_power_iff; simpl.
unfold is_the_greatest_series_x_power.
remember (null_coeff_range_length rng 1%ser 1) as n eqn:Hn .
symmetry in Hn.
apply null_coeff_range_length_iff in Hn.
unfold null_coeff_range_length_prop in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
destruct Hn as (Hz, Hnz).
unfold series_nth in Hnz.
simpl in Hnz.
destruct (Nbar.lt_dec (fin (S n)) 1) as [H₁| H₁].
 apply Nbar.fin_lt_mono in H₁.
 apply lt_S_n in H₁.
 exfalso; revert H₁; apply Nat.nlt_0_r.

 exfalso; apply Hnz; reflexivity.
Qed.

Theorem ps_mul_inv_l : ∀ ps, (ps ≠ 0)%ps → (ps_inv ps * ps = 1)%ps.
Proof.
intros ps Hps.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 assert (ps = ps_left_adjust ps)%ps as Hadj.
  Focus 2.
  rewrite ps_mul_comm.
  rewrite Hadj in |- * at 1.
  unfold ps_inv; simpl.
  unfold ps_left_adjust; simpl.
  rewrite Hn.
  unfold ps_mul; simpl.
  unfold cm_factor, cm; simpl.
  rewrite <- series_stretch_mul.
  rewrite series_mul_inv_r.
   rewrite stretch_series_1.
   rewrite <- Z.mul_add_distr_r.
   rewrite Z.add_sub_assoc.
   rewrite Z.add_opp_r.
   rewrite Z.add_comm.
   rewrite Z.add_simpl_r.
   rewrite Z.sub_diag, Z.mul_0_l.
   constructor.
   rewrite canonic_ps_1.
   unfold canonic_ps.
   simpl.
   rewrite null_coeff_range_length_series_1.
   simpl.
   unfold gcd_ps.
   remember Z.gcd as f; simpl; subst f.
   rewrite Z.gcd_0_l.
   rewrite Z.div_0_l.
    rewrite greatest_series_x_power_series_1.
    rewrite Z.gcd_0_r.
    simpl.
    rewrite Z.div_same; [ idtac | apply Pos2Z_ne_0 ].
    unfold canonify_series; simpl.
    rewrite series_left_shift_0.
    unfold series_shrink.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite Nat.div_same.
     reflexivity.

     apply Pos2Nat_ne_0.

    intros H.
    apply Z.gcd_eq_0_l in H.
    simpl in H.
    revert H; apply Pos2Z_ne_0.

   Unfocus.
bbb.

intros ps Hps.
unfold ps_inv; simpl.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  rewrite series_inv_compat with (b := ps_terms ps).
   unfold ps_mul; simpl.
   unfold cm_factor, cm; simpl.
   rewrite <- series_stretch_mul.
   rewrite series_mul_inv_l.
    rewrite Z.mul_opp_l, Z.add_opp_l, Z.sub_diag.
    constructor.
    rewrite canonic_ps_1.
    constructor; simpl.
     erewrite ps_valnum_canonic with (n := O); simpl; try reflexivity.
      rewrite stretch_series_1.
      rewrite Z.div_0_l; [ reflexivity | idtac ].
      rewrite Z.gcd_0_l.
      remember (Z.of_nat (greatest_series_x_power rng 1%ser 0)) as y.
      destruct y; simpl; apply Pos2Z_ne_0.

      rewrite stretch_series_1.
      apply null_coeff_range_length_series_1.

     erewrite ps_comden_canonic with (n := O); try reflexivity.
      remember Z.gcd as f; simpl; subst f.
      rewrite stretch_series_1.
      rewrite Z.gcd_0_r.
      rewrite greatest_series_x_power_series_1.
      rewrite Z.gcd_0_r; simpl.
      rewrite Z.div_same; [ reflexivity | idtac ].
      apply Pos2Z_ne_0.

      simpl.
      rewrite stretch_series_1.
      apply null_coeff_range_length_series_1.

     erewrite ps_terms_canonic with (n := O); try reflexivity.
      remember Z.gcd as f; simpl; subst f.
      rewrite stretch_series_1.
      rewrite Z.gcd_0_l.
      rewrite greatest_series_x_power_series_1.
      rewrite Z.gcd_0_r; simpl.
      unfold canonify_series.
      rewrite series_left_shift_0.
      constructor; intros i.
      unfold series_nth; simpl.
      rewrite Nat.sub_0_r.
      rewrite Nat.div_same; [ reflexivity | apply Pos2Nat_ne_0 ].

      simpl.
      rewrite stretch_series_1.
      apply null_coeff_range_length_series_1.

    apply null_coeff_range_length_iff in Hn.
    simpl in Hn.
    destruct Hn as (Hz, Hnz).
    assumption.

   rewrite series_shift_0.
   apply null_coeff_range_length_iff in Hn.
   simpl in Hn.
   destruct Hn as (Hz, Hnz).
   assumption.

   rewrite series_shift_0.
   reflexivity.
bbb.

intros ps Hps.
remember (ps_terms (ps_inv ps * ps)%ps) as s.
remember (null_coeff_range_length rng s 0) as n eqn:Hn ; subst s.
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  constructor; constructor; simpl.
   erewrite ps_valnum_canonic; try reflexivity; try eassumption.
   pose proof canonic_ps_1 as H.
   inversion H; subst.
   rewrite H0; simpl.
   clear H H0 H1 H2.
   rewrite Z.mul_opp_l, Z.add_opp_diag_l; simpl.
   rewrite Z.div_0_l; [ reflexivity | apply Pos2Z_ne_0 ].

   erewrite ps_comden_canonic; try reflexivity; try eassumption.
   pose proof canonic_ps_1 as H.
   inversion H; subst.
   rewrite H1.
   clear H H0 H1 H2.
   remember Z.gcd as f; simpl; subst f.
   unfold cm, cm_factor.
   remember Z.gcd as f; simpl; subst f.
bbb.
