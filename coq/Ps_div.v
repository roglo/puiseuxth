(* Ps_div.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Field.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Import Ps_mul.
Require Import Power_series.

Set Implicit Arguments.

Definition ps_inv α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_inv f (series_left_shift n (ps_terms ps));
         ps_valnum := - ps_valnum ps - Z.of_nat n;
         ps_polord := ps_polord ps |}
  | ∞ =>
      ps
  end.

Notation ".¹/ f a" := (ps_inv f a) : ps_scope.

Definition ps_left_adjust α (f : field α) ps :=
  match null_coeff_range_length f (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_left_shift n (ps_terms ps);
         ps_valnum := ps_valnum ps + Z.of_nat n;
         ps_polord := ps_polord ps |}
  | ∞ =>
      ps
  end.

Section theorems.

Variable α : Type.
Variable f : field α.

Lemma null_coeff_range_length_left_adjust : ∀ n ps,
  null_coeff_range_length f (ps_terms ps) 0 = fin n
  → null_coeff_range_length f (ps_terms (ps_left_adjust f ps)) 0 = 0%Nbar.
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

Lemma null_coeff_range_length_inf_left_adjust : ∀ ps,
  null_coeff_range_length f (ps_terms ps) 0 = ∞
  → null_coeff_range_length f (ps_terms (ps_left_adjust f ps)) 0 = ∞.
Proof.
intros ps Hn.
apply null_coeff_range_length_iff.
unfold ps_left_adjust; simpl.
rewrite Hn.
apply null_coeff_range_length_iff in Hn.
assumption.
Qed.

Lemma ps_left_adjust_eq : ∀ ps, (ps .= f ps_left_adjust f ps)%ps.
Proof.
intros ps.
remember (null_coeff_range_length f (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 constructor; constructor; simpl.
  erewrite ps_valnum_canonic; try reflexivity; try eassumption.
  erewrite ps_valnum_canonic with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply null_coeff_range_length_left_adjust; eassumption.

  erewrite ps_polord_canonic; try reflexivity; try eassumption.
  erewrite ps_polord_canonic with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply null_coeff_range_length_left_adjust; eassumption.

  erewrite ps_terms_canonic; try reflexivity; try eassumption.
  erewrite ps_terms_canonic with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r.
   unfold canonify_series.
   rewrite series_left_shift_0; reflexivity.

   eapply null_coeff_range_length_left_adjust; eassumption.

 constructor; constructor; simpl.
  unfold canonic_ps.
  rewrite Hn.
  rewrite null_coeff_range_length_inf_left_adjust; [ reflexivity | idtac ].
  assumption.

  unfold canonic_ps.
  rewrite Hn.
  rewrite null_coeff_range_length_inf_left_adjust; [ reflexivity | idtac ].
  assumption.

  unfold canonic_ps.
  rewrite Hn.
  rewrite null_coeff_range_length_inf_left_adjust; [ reflexivity | idtac ].
  assumption.
Qed.

Lemma series_left_shift_0 : ∀ s, (series_left_shift 0 s .= f s)%ser.
Proof.
intros s.
unfold series_left_shift.
rewrite Nbar.sub_0_r; simpl.
destruct s; reflexivity.
Qed.

Lemma series_shrink_1 : ∀ s, (series_shrink 1 s .= f s)%ser.
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

Lemma canonic_ps_1 : (canonic_ps f (.1 f) ≐ f (.1 f))%ps.
Proof.
remember (null_coeff_range_length f (ps_terms (.1 f %ps)) 0) as n eqn:Hn .
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
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   rewrite Z.div_0_l; [ reflexivity | idtac ].
   intros H; discriminate H.

   erewrite ps_polord_canonic; try reflexivity; try eassumption.
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_1_l.
   reflexivity.

   erewrite ps_terms_canonic; try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   unfold canonify_series; simpl.
   rewrite series_shrink_1.
   rewrite series_left_shift_0; reflexivity.

 apply null_coeff_range_length_inf_iff in Hn.
 exfalso; revert Hn; apply ps_neq_1_0.
Qed.

Lemma series_inv_compat : ∀ a b,
  (a [0]f .≠ f .0 f)%F
  → (a .= f b)%ser
    → (series_inv f a .= f series_inv f b)%ser.
Proof.
intros a b Ha Hab.
remember Ha as Hb; clear HeqHb.
rewrite Hab in Hb.
apply series_mul_compat_l with (c := series_inv f a) in Hab.
apply series_mul_compat_r with (c := series_inv f b) in Hab.
rewrite series_mul_inv_l in Hab; auto.
rewrite series_mul_1_l in Hab.
rewrite <- series_mul_assoc in Hab.
rewrite series_mul_inv_r in Hab; auto.
rewrite series_mul_1_r in Hab.
symmetry; assumption.
Qed.

Lemma null_coeff_range_length_series_1 :
  null_coeff_range_length f (.1 f)%ser 0 = 0%Nbar.
Proof.
apply null_coeff_range_length_iff; simpl.
split.
 intros i Hi.
 apply Nat.nlt_ge in Hi.
 exfalso; apply Hi, Nat.lt_0_succ.

 unfold series_nth; simpl.
 rewrite if_lt_dec_0_1.
 apply fld_neq_1_0.
Qed.

Lemma greatest_series_x_power_series_1 :
  greatest_series_x_power f (.1 f)%ser 0 = O.
Proof.
apply greatest_series_x_power_iff; simpl.
unfold is_the_greatest_series_x_power.
remember (null_coeff_range_length f (.1 f)%ser 1) as n eqn:Hn .
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

Theorem ps_mul_inv_l : ∀ ps,
  (ps .≠ f .0 f)%ps
  → (.¹/f ps .* f ps .= f .1 f)%ps.
Proof.
intros ps Hps.
remember (null_coeff_range_length f (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 assert (ps .= f ps_left_adjust f ps)%ps as Hadj.
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
   remember Z.gcd as g; simpl; subst g.
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
   apply ps_left_adjust_eq.

  apply null_coeff_range_length_iff in Hn.
  destruct Hn as (Hz, Hnz).
  rewrite Nat.add_0_l in Hnz.
  unfold series_nth in Hnz.
  destruct (Nbar.lt_dec (fin n) (stop (ps_terms ps))) as [H₁| H₁].
   unfold series_nth.
   destruct (Nbar.lt_dec 0 (stop (series_left_shift n (ps_terms ps))))
    as [H₂| H₂].
    simpl.
    rewrite Nat.add_0_r.
    assumption.

    exfalso; apply H₂.
    unfold series_left_shift.
    remember Nbar.sub as g; simpl; subst g.
    apply Nbar.lt_add_lt_sub_r.
    rewrite Nbar.add_0_l; assumption.

   exfalso; apply Hnz; reflexivity.

 apply null_coeff_range_length_inf_iff in Hn.
 contradiction.
Qed.

End theorems.

Definition ps_field α (f : field α) : field (puiseux_series α) :=
  {| fld_zero := ps_zero f;
     fld_one := ps_one f;
     fld_add := ps_add f;
     fld_mul := ps_mul f;
     fld_opp := ps_opp f;
     fld_eq := eq_ps f;
     fld_eq_refl := eq_ps_refl f;
     fld_eq_sym := eq_ps_sym (f := f);
     fld_eq_trans := eq_ps_trans (f := f);
     fld_neq_1_0 := ps_neq_1_0 (f := f);
     fld_add_comm := ps_add_comm f;
     fld_add_assoc := ps_add_assoc f;
     fld_add_0_l := ps_add_0_l f;
     fld_add_opp_l := ps_add_opp_l f;
     fld_add_compat_l := @ps_add_compat_l α f;
     fld_mul_comm := ps_mul_comm f;
     fld_mul_assoc := ps_mul_assoc f;
     fld_mul_1_l := ps_mul_1_l f;
     fld_mul_compat_l := @ps_mul_compat_l α f;
     fld_mul_add_distr_l := ps_mul_add_distr_l f;
     fld_inv := ps_inv f;
     fld_mul_inv_l := @ps_mul_inv_l α f |}.
