(* Ps_div.v *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import NbarM.
Require Import Field2.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Import Ps_mul.
Require Import Power_series.

Set Implicit Arguments.

Definition ps_inv {α} {r : ring α} {f : field r} ps :=
  match series_order (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_inv (series_left_shift n (ps_terms ps));
         ps_ordnum := - ps_ordnum ps - Z.of_nat n;
         ps_polydo := ps_polydo ps |}
  | ∞ =>
      ps
  end.

Notation "¹/ a" := (ps_inv a) : ps_scope.

Definition ps_left_adjust α {R : ring α} {K : field R} ps :=
  match series_order (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_left_shift n (ps_terms ps);
         ps_ordnum := ps_ordnum ps + Z.of_nat n;
         ps_polydo := ps_polydo ps |}
  | ∞ =>
      ps
  end.

Section theorems.

Variable α : Type.
Variable r : ring α.
Variable f : field r.

Theorem series_order_left_adjust : ∀ n ps,
  series_order (ps_terms ps) 0 = fin n
  → series_order (ps_terms (ps_left_adjust ps)) 0 = 0%Nbar.
Proof.
intros n ps Hn.
unfold ps_left_adjust; simpl.
rewrite Hn; simpl.
apply series_order_iff.
apply series_order_iff in Hn.
simpl in Hn |- *.
destruct Hn as (Hz, Hnz).
split.
 intros i Hi.
 exfalso; revert Hi; apply Nat.nlt_0_r.

 rewrite Nat.add_0_r; assumption.
Qed.

Theorem series_order_inf_left_adjust : ∀ ps,
  series_order (ps_terms ps) 0 = ∞
  → series_order (ps_terms (ps_left_adjust ps)) 0 = ∞.
Proof.
intros ps Hn.
apply series_order_iff.
unfold ps_left_adjust; simpl.
rewrite Hn.
apply series_order_iff in Hn.
assumption.
Qed.

Theorem ps_left_adjust_eq : ∀ ps, (ps = ps_left_adjust ps)%ps.
Proof.
intros ps.
remember (series_order (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 constructor; constructor; simpl.
  erewrite ps_ordnum_normalise; try reflexivity; try eassumption.
  erewrite ps_ordnum_normalise with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply series_order_left_adjust; eassumption.

  erewrite ps_polydo_normalise; try reflexivity; try eassumption.
  erewrite ps_polydo_normalise with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r; reflexivity.

   eapply series_order_left_adjust; eassumption.

  erewrite ps_terms_normalise; try reflexivity; try eassumption.
  erewrite ps_terms_normalise with (n := O); try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   unfold ps_left_adjust.
   rewrite Hn.
   remember Z.gcd as g; simpl; subst g.
   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r.
   unfold normalise_series.
   rewrite series_left_shift_0; reflexivity.

   eapply series_order_left_adjust; eassumption.

 constructor; constructor; simpl.
  unfold normalise_ps.
  rewrite Hn.
  rewrite series_order_inf_left_adjust; [ reflexivity | idtac ].
  assumption.

  unfold normalise_ps.
  rewrite Hn.
  rewrite series_order_inf_left_adjust; [ reflexivity | idtac ].
  assumption.

  unfold normalise_ps.
  rewrite Hn.
  rewrite series_order_inf_left_adjust; [ reflexivity | idtac ].
  assumption.
Qed.

Theorem series_left_shift_0 : ∀ s, (series_left_shift 0 s = s)%ser.
Proof.
intros s.
unfold series_left_shift.
destruct s; reflexivity.
Qed.

Theorem series_shrink_1 : ∀ s, (series_shrink 1 s = s)%ser.
Proof.
intros s.
unfold series_shrink; simpl.
constructor; intros n; simpl.
rewrite Nat.mul_1_r; reflexivity.
Qed.

Theorem normalise_ps_1 : (normalise_ps 1 ≐ 1)%ps.
Proof.
remember (series_order (ps_terms 1%ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  constructor; simpl.
   erewrite ps_ordnum_normalise; try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   rewrite Z.div_0_l; [ reflexivity | idtac ].
   intros H; discriminate H.

   erewrite ps_polydo_normalise; try reflexivity; try eassumption.
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_1_l.
   reflexivity.

   erewrite ps_terms_normalise; try reflexivity; try eassumption.
   rewrite Z.add_0_r.
   remember Z.gcd as g; simpl; subst g.
   rewrite Z.gcd_0_l.
   rewrite Z.gcd_1_l.
   unfold normalise_series; simpl.
   rewrite series_shrink_1.
   rewrite series_left_shift_0; reflexivity.

  apply series_order_iff in Hn; simpl in Hn.
  destruct Hn as (_, Hn).
  exfalso; apply Hn; reflexivity.

 unfold normalise_ps.
 rewrite Hn.
 constructor; try reflexivity.
 constructor; intros i; simpl.
 apply series_order_iff in Hn.
 simpl in Hn.
 symmetry; apply Hn.
Qed.

Theorem greatest_series_x_power_series_const : ∀ s c m,
  (s = series_const c)%ser
  → greatest_series_x_power f s m = 0%nat.
Proof.
intros s c m Hs.
rewrite Hs.
apply greatest_series_x_power_iff; simpl.
remember (series_order (series_const c) (S m)) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
apply series_order_iff in Hn; simpl in Hn.
destruct Hn as (Hz, Hnz).
exfalso; apply Hnz; reflexivity.
Qed.

Theorem greatest_series_x_power_series_1 :
  greatest_series_x_power f 1%ser 0 = O.
Proof.
apply greatest_series_x_power_series_const with (c := 1%K).
reflexivity.
Qed.

Theorem ps_mul_inv_l : ∀ ps,
  (ps ≠ 0)%ps
  → (¹/ ps * ps = 1)%ps.
Proof.
intros ps Hps.
remember (series_order (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 assert (ps = ps_left_adjust ps)%ps as H by apply ps_left_adjust_eq.
 rewrite ps_mul_comm.
 rewrite H in |- * at 1.
 unfold ps_inv; simpl.
 unfold ps_left_adjust; simpl.
 rewrite Hn.
 unfold ps_mul; simpl.
 unfold cm_factor, cm; simpl.
 rewrite <- series_stretch_mul.
 rewrite series_mul_inv_r.
  rewrite stretch_series_1.
  rewrite <- Z.mul_add_distr_r.
  rewrite Z.add_sub_assoc, Z.add_opp_r.
  rewrite Z.add_comm, Z.add_simpl_r.
  rewrite Z.sub_diag, Z.mul_0_l.
  constructor.
  rewrite normalise_ps_1.
  unfold normalise_ps; simpl.
  remember (series_order 1%ser 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   destruct m; simpl.
    unfold gcd_ps.
    remember Z.gcd as g; simpl; subst g.
    rewrite Z.gcd_0_l.
    rewrite Z.div_0_l.
     rewrite greatest_series_x_power_series_1.
     rewrite Z.gcd_0_r; simpl.
     rewrite Z.div_same; [ idtac | apply Pos2Z_ne_0 ].
     unfold normalise_series; simpl.
     rewrite series_left_shift_0.
     unfold series_shrink; simpl.
     constructor; try reflexivity; simpl.
     constructor; intros i; simpl.
     destruct i; [ reflexivity | idtac ].
     remember (S i * Pos.to_nat (ps_polydo ps * ps_polydo ps))%nat as x.
     symmetry in Heqx; simpl.
     destruct x; [ idtac | reflexivity ].
     apply Nat.eq_mul_0_l in Heqx; auto with Arith; discriminate Heqx.

     intros H₁.
     apply Z.gcd_eq_0_l in H₁.
     exfalso; revert H₁; apply Pos2Z_ne_0.

    apply series_order_iff in Hm; simpl in Hm.
    destruct Hm as (_, Hm).
    exfalso; apply Hm; reflexivity.

   apply series_order_iff in Hm; simpl in Hm.
   constructor; try reflexivity.
   constructor; intros i; simpl.
   symmetry; apply Hm.

  apply series_order_iff in Hn.
  destruct Hn as (Hz, Hnz).
  rewrite Nat.add_comm in Hnz; assumption.

 apply ps_series_order_inf_iff in Hn.
 contradiction.
Qed.

End theorems.

Definition ps_ring α (R : ring α) (K : field R) : ring (puiseux_series α) :=
  {| rng_zero := ps_zero;
     rng_one := ps_one;
     rng_add := ps_add;
     rng_mul := ps_mul;
     rng_opp := ps_opp;
     rng_eq := eq_ps;
     rng_eq_refl := eq_ps_refl K;
     rng_eq_sym := eq_ps_sym (K := K);
     rng_eq_trans := eq_ps_trans (K := K);
     rng_add_comm := ps_add_comm K;
     rng_add_assoc := ps_add_assoc K;
     rng_add_0_l := ps_add_0_l K;
     rng_add_opp_l := ps_add_opp_l K;
     rng_add_compat_l := @ps_add_compat_l α R K;
     rng_mul_comm := ps_mul_comm K;
     rng_mul_assoc := ps_mul_assoc K;
     rng_mul_1_l := ps_mul_1_l K;
     rng_mul_compat_l := @ps_mul_compat_l α R K;
     rng_mul_add_distr_l := ps_mul_add_distr_l K |}.

Canonical Structure ps_ring.

Fixpoint ps_power {α} {r : ring α} la n :=
  match n with
  | O => 1%ps
  | S m => ps_mul la (ps_power la m)
  end.

Notation "a ^ b" := (ps_power a b) : ps_scope.
