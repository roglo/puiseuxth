(* $Id: Ps_add_compat.v,v 2.40 2013-12-08 03:21:58 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Series.
Require Import Puiseux_series.
Require Import Nbar.
Require Import Ps_add.
Require Import Misc.

Lemma series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i, (series_nth_rng rng i s = 0)%rng)
  → ∀ i, (series_nth_rng rng i (series_shift n s) = 0)%rng.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite series_shift_0; apply H.

 destruct i.
  unfold series_nth_rng; simpl.
  destruct (Nbar.lt_dec 0 (stop s + fin (S n))); reflexivity.

  rewrite <- series_nth_shift_S; apply IHn.
Qed.

Lemma canonify_series_add_shift : ∀ s n m k,
  (canonify_series (n + m) k (series_shift m s) =
   canonify_series n k s)%ser.
Proof.
intros s n m k.
unfold canonify_series.
unfold series_shrink, series_left_shift.
constructor; intros i.
unfold series_nth_rng.
remember Nbar.div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
replace (stop s + fin m - fin (n + m))%Nbar with (stop s - fin n)%Nbar .
 remember (Nbar.div_sup (stop s - fin n) (fin (Pos.to_nat k))) as x eqn:Hx .
 destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
 subst x.
 remember (i * Pos.to_nat k)%nat as x.
 replace (n + m + x - m)%nat with (n + x)%nat by omega.
 subst x.
 destruct (lt_dec (n + m + i * Pos.to_nat k) m) as [H₂| H₂].
  rewrite Nat.add_shuffle0, Nat.add_comm in H₂.
  apply Nat.nle_gt in H₂.
  exfalso; apply H₂.
  apply Nat.le_add_r.

  reflexivity.

 simpl.
 destruct (stop s) as [st| ]; [ simpl | reflexivity ].
 apply Nbar.fin_inj_wd.
 omega.
Qed.

Lemma gcd_ps_add : ∀ ps n,
  gcd_ps (n + Z.to_nat (ps_valnum ps))
    (greatest_series_x_power rng
       (series_shift (Z.to_nat (ps_valnum ps)) (ps_terms ps))
       (n + Z.to_nat (ps_valnum ps))) (ps + 0)%ps =
  gcd_ps n (greatest_series_x_power rng (ps_terms ps) n) ps.
Proof.
intros ps n.
unfold gcd_ps; simpl.
unfold ps_valnum_add.
rewrite Z.mul_1_r.
rewrite Nat2Z.inj_add.
rewrite Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite <- Z.add_assoc.
rewrite Z.add_comm.
unfold cm; simpl.
rewrite Pos.mul_1_r.
remember (ps_valnum ps) as z eqn:Hz .
symmetry in Hz.
destruct z as [| z| z].
 simpl.
 rewrite Z.min_id.
 rewrite Z.add_0_r, Nat.add_0_r.
 rewrite series_shift_0.
 reflexivity.

 rewrite Z.min_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite greatest_series_x_power_shift.
 rewrite Z.add_0_r.
 rewrite Z2Nat.id; [ idtac | apply Pos2Z.is_nonneg ].
 reflexivity.

 rewrite Z.min_l; [ idtac | apply Pos2Z.neg_is_nonpos ].
 rewrite greatest_series_x_power_shift.
 f_equal.
 f_equal.
 symmetry; rewrite Z.add_comm.
 reflexivity.
Qed.

Lemma canonify_ps_add_0_r : ∀ ps,
  canonify_ps (ps + 0)%ps ≐ canonify_ps ps.
Proof.
intros ps.
unfold canonify_ps; simpl.
rewrite ps_terms_add_0_r.
rewrite null_coeff_range_length_shift.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
rewrite Nbar.add_comm.
destruct n₁ as [n₁| ]; [ simpl | reflexivity ].
constructor; simpl.
 unfold ps_valnum_add.
 rewrite Z.mul_1_r.
 rewrite ps_terms_add_0_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.add_assoc, Z.add_shuffle0.
 rewrite Z2Nat_id_max, Z.min_comm.
 f_equal; [ idtac | apply gcd_ps_add ].
 remember (ps_valnum ps) as z eqn:Hz .
 symmetry in Hz.
 destruct z; reflexivity.

 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 do 2 f_equal.
 rewrite ps_terms_add_0_r.
 apply gcd_ps_add.

 rewrite ps_terms_add_0_r.
 rewrite greatest_series_x_power_shift.
 constructor; intros i.
 rewrite canonify_series_add_shift.
 unfold gcd_ps; simpl.
 unfold cm; simpl.
 unfold ps_valnum_add.
 rewrite Z.mul_1_r, Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 destruct (ps_valnum ps) as [| p| p]; simpl.
  rewrite Z.add_0_r; reflexivity.

  rewrite positive_nat_Z.
  destruct (Z.of_nat n₁); try reflexivity.
  rewrite Pos.add_comm; reflexivity.

  rewrite Z.add_0_r; reflexivity.
Qed.

Lemma eq_canon_ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  eq_canon_ps ps₁ ps₂
  → eq_canon_ps (ps₁ + ps₃)%ps (ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
induction Heq.
unfold ps_add.
constructor; simpl.
 unfold ps_valnum_add.
 unfold cm_factor.
 rewrite H, H0.
 reflexivity.

 unfold cm.
 rewrite H0; reflexivity.

 unfold ps_terms_add.
 unfold cm_factor.
 unfold adjust_series.
 rewrite H, H0, H1.
 reflexivity.
Qed.

Lemma eq_canon_ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ ≐ ps₂)%ps
  → (ps₃ + ps₁ ≐ ps₃ + ps₂)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
rewrite eq_canon_ps_add_comm; symmetry.
rewrite eq_canon_ps_add_comm; symmetry.
apply eq_canon_ps_add_compat_r; assumption.
Qed.

Lemma ps_adjust_adjust : ∀ ps n₁ n₂ k₁ k₂,
  eq_canon_ps (adjust_ps n₁ k₁ (adjust_ps n₂ k₂ ps))
    (adjust_ps (n₁ + n₂ * Pos.to_nat k₁) (k₁ * k₂) ps).
Proof.
intros ps n₁ n₂ k₁ k₂.
unfold adjust_ps; simpl.
constructor; simpl.
 rewrite Z.mul_sub_distr_r.
 rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
 rewrite <- Z.sub_add_distr; f_equal.
 rewrite Nat2Z.inj_add, Z.add_comm; f_equal.
 rewrite Nat2Z.inj_mul, positive_nat_Z.
 reflexivity.

 rewrite Pos.mul_assoc, Pos_mul_shuffle0.
 reflexivity.

 rewrite stretch_shift_series_distr.
 rewrite series_shift_shift.
 rewrite series_stretch_stretch.
 reflexivity.
Qed.

Lemma ps_adjust_adjusted : ∀ ps₁ ps₂ n k,
  eq_canon_ps (adjust_ps n k (adjusted_ps_add ps₁ ps₂))
    (adjusted_ps_add (adjust_ps n k ps₁) (adjust_ps n k ps₂)).
Proof.
intros ps₁ ps₂ n k.
constructor; simpl; try reflexivity.
rewrite series_stretch_add_distr.
rewrite series_shift_add_distr.
reflexivity.
Qed.

Lemma adjust_ps_mul : ∀ ps n k u,
  eq_canon_ps
    (adjust_ps (n * Pos.to_nat u) (k * u) ps)
    (adjust_ps 0 u (adjust_ps n k ps)).
Proof.
intros ps n k u.
constructor; simpl.
 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 rewrite Z.mul_sub_distr_r.
 rewrite Z.sub_0_r.
 f_equal.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 reflexivity.

 rewrite Pos.mul_assoc; reflexivity.

 rewrite stretch_shift_series_distr.
 rewrite series_shift_0.
 rewrite Pos.mul_comm.
 rewrite series_stretch_stretch.
 reflexivity.
Qed.

Lemma eq_canon_ps_add_adjust_0_l : ∀ ps₁ ps₂ k,
  canonify_ps (ps₁ + ps₂)%ps ≐
  canonify_ps (adjust_ps 0 k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ k.
rewrite ps_canon_adjust_eq with (n := O) (k := k).
unfold ps_add; simpl.
unfold adjust_ps; simpl.
unfold ps_terms_add, ps_valnum_add, adjust_series, cm, cm_factor; simpl.
do 2 rewrite series_shift_0.
do 2 rewrite Z.sub_0_r.
rewrite series_stretch_add_distr.
do 2 rewrite stretch_shift_series_distr.
do 3 rewrite <- series_stretch_stretch.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
do 2 rewrite Z.mul_sub_distr_r.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
remember (ps_valnum ps₁ * ' ps_comden ps₂ * ' k)%Z as x eqn:Hx .
rewrite Z.mul_shuffle0 in Hx; rewrite <- Hx.
rewrite Pos.mul_comm.
remember (k * ps_comden ps₁)%positive as y eqn:Hy .
rewrite Pos.mul_comm in Hy; rewrite <- Hy.
rewrite Pos_mul_shuffle0, <- Hy.
reflexivity.
Qed.

Lemma canonify_ps_adjust : ∀ ps₁ ps₂ n,
  canonify_ps
    (adjusted_ps_add (adjust_ps n 1 ps₁) (adjust_ps n 1 ps₂))
  ≐ canonify_ps
      (adjusted_ps_add ps₁ ps₂).
Proof.
(* gros nettoyage à faire : factorisation, focus, etc. *)
intros ps₁ ps₂ n.
rewrite <- ps_adjust_adjusted.
unfold canonify_ps.
simpl.
rewrite null_coeff_range_length_shift.
rewrite series_stretch_1.
remember
 (null_coeff_range_length rng (series_add (ps_terms ps₁) (ps_terms ps₂))
    0)%Nbar as x.
rewrite Nbar.add_comm.
destruct x as [x| ]; [ simpl | reflexivity ].
constructor; simpl.
 rewrite Z.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 f_equal.
 rewrite series_stretch_1.
 remember (series_add (ps_terms ps₁) (ps_terms ps₂)) as s.
 symmetry in Heqx.
 apply null_coeff_range_length_iff in Heqx.
 simpl in Heqx.
 destruct Heqx as (Hz, Hnz).
 unfold gcd_ps.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite Pos.mul_1_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.

 rewrite Pos.mul_1_r.
 f_equal.
 f_equal.
 rewrite series_stretch_1.
 remember (series_add (ps_terms ps₁) (ps_terms ps₂)) as s.
 symmetry in Heqx.
 unfold gcd_ps.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.

 rewrite series_stretch_1.
 rewrite canonify_series_add_shift.
 remember (series_add (ps_terms ps₁) (ps_terms ps₂)) as s.
 unfold gcd_ps.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.
Qed.

Lemma canonify_ps_adjust_add : ∀ ps₁ ps₂ n n₁ n₂ k₁ k₂,
  canonify_ps
    (adjusted_ps_add
       (adjust_ps (n + n₁) k₁ ps₁)
       (adjust_ps (n + n₂) k₂ ps₂)) ≐
  canonify_ps
    (adjusted_ps_add
       (adjust_ps n₁ k₁ ps₁)
       (adjust_ps n₂ k₂ ps₂)).
Proof.
intros ps₁ ps₂ n n₁ n₂ k₁ k₂.
replace (n + n₁)%nat with (n + n₁ * Pos.to_nat 1)%nat .
 replace (n + n₂)%nat with (n + n₂ * Pos.to_nat 1)%nat .
  replace k₁ with (1 * k₁)%positive by reflexivity.
  rewrite <- ps_adjust_adjust.
  replace k₂ with (1 * k₂)%positive by reflexivity.
  rewrite <- ps_adjust_adjust.
  do 2 rewrite Pos.mul_1_l.
  rewrite canonify_ps_adjust; reflexivity.

  rewrite Nat.mul_1_r; reflexivity.

 rewrite Nat.mul_1_r; reflexivity.
Qed.

Lemma canonify_ps_add_adjust : ∀ ps₁ ps₂ n k m,
  canonify_ps (adjust_ps m k ps₁ + ps₂)%ps ≐
  canonify_ps (adjust_ps n k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ n k m.
do 2 rewrite eq_canon_ps_canon_add_add₂.
unfold ps_add₂; simpl.
unfold adjust_ps_from.
unfold cm_factor; simpl.
do 2 rewrite ps_adjust_adjust.
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
remember (ps_valnum ps₁) as v₁.
remember (ps_comden ps₂) as c₂.
remember (ps_valnum ps₂) as v₂.
remember (ps_comden ps₁) as c₁.
remember (Z.of_nat n) as nn.
remember (Z.of_nat m) as mm.
do 2 rewrite Z.mul_sub_distr_r.
replace n with (Z.to_nat nn) by (rewrite Heqnn, Nat2Z.id; reflexivity).
replace m with (Z.to_nat mm) by (rewrite Heqmm, Nat2Z.id; reflexivity).
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
rewrite <- Z2Nat.inj_add.
 rewrite <- Z2Nat.inj_add.
  do 2 rewrite <- Z.sub_add_distr.
  do 2 rewrite <- Z.add_sub_swap.
  do 2 rewrite Z.sub_add_distr.
  do 2 rewrite Z.add_simpl_r.
  rewrite Z.mul_shuffle0.
  remember (v₁ * Zpos c₂ * Zpos k)%Z as vc₁.
  remember (v₂ * Zpos c₁ * Zpos k)%Z as vc₂.
  rewrite <- Z2Nat_sub_min2.
  rewrite <- Z2Nat_sub_min1.
  rewrite Z.min_id, Z.sub_diag, Nat.add_0_r.
  rewrite <- Z2Nat_sub_min2.
  rewrite <- Z2Nat_sub_min1.
  rewrite Z.min_id, Z.sub_diag, Nat.add_0_r.
  do 4 rewrite Z.sub_sub_distr.
  rewrite Z.add_comm.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_sub_swap.
  rewrite <- Z.sub_sub_distr.
  symmetry.
  rewrite Z.add_comm.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_sub_swap.
  rewrite <- Z.sub_sub_distr.
  symmetry.
  rewrite Z2Nat.inj_sub.
   symmetry.
   rewrite Z2Nat.inj_sub.
    rewrite Z.add_comm.
    destruct (Z_le_dec vc₁ vc₂) as [H₁| H₁].
     Focus 1.
     rewrite Z2Nat.inj_add.
      rewrite Z.add_comm.
      rewrite Z2Nat.inj_add.
       rewrite Z.min_l; auto.
       rewrite Z.sub_diag.
       do 2 rewrite Nat.sub_0_r.
       rewrite <- Z2Nat_sub_min.
       rewrite Z.min_l; auto.
       rewrite Z.sub_diag, Nat.add_0_r.
       rewrite Nat.add_0_r.
       replace (Z.to_nat (nn * Zpos c₂)) with
        (Z.to_nat (nn * Zpos c₂) + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonify_ps_adjust_add.
       replace (Z.to_nat (mm * Zpos c₂)) with
        (Z.to_nat (mm * Zpos c₂) + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonify_ps_adjust_add.
       reflexivity.

       subst mm; simpl.
       destruct m; [ reflexivity | simpl ].
       apply Pos2Z.is_nonneg.

       apply Zle_minus_le_0; assumption.

      subst nn; simpl.
      destruct n; [ reflexivity | simpl ].
      apply Pos2Z.is_nonneg.

      apply Zle_minus_le_0; assumption.

     apply Z.nle_gt in H₁.
     rewrite Z.min_r; [ idtac | apply Z.lt_le_incl; assumption ].
     rewrite Z.add_sub_assoc.
     symmetry.
     rewrite Z.add_comm.
     rewrite Z.add_sub_assoc.
     rewrite Z.add_sub_swap.
     rewrite <- Z.sub_sub_distr.
     symmetry.
     rewrite Z.add_sub_swap.
     rewrite <- Z.sub_sub_distr.
     remember (vc₁ - vc₂)%Z as x.
     rewrite <- Z2Nat.inj_sub.
      rewrite <- Z2Nat.inj_sub.
       remember (Z.to_nat (nn * Zpos c₂ - x)) as y.
       replace y with (y + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonify_ps_adjust_add.
       clear y Heqy.
       remember (Z.to_nat (mm * Zpos c₂ - x)) as y.
       replace y with (y + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonify_ps_adjust_add.
       reflexivity.

       subst x.
       apply Zle_minus_le_0, Z.lt_le_incl; assumption.

      subst x.
      apply Zle_minus_le_0, Z.lt_le_incl; assumption.

    rewrite <- Z.sub_max_distr_l, Z.sub_diag.
    apply Z.le_max_l.

   rewrite <- Z.sub_max_distr_l, Z.sub_diag.
   apply Z.le_max_l.

  rewrite <- Z.sub_max_distr_l, Z.sub_diag.
  apply Z.le_max_r.

  subst nn.
  destruct n; [ reflexivity | simpl ].
  apply Pos2Z.is_nonneg.

 rewrite <- Z.sub_max_distr_l, Z.sub_diag.
 apply Z.le_max_r.

 subst mm.
 destruct m; [ reflexivity | simpl ].
 apply Pos2Z.is_nonneg.
Qed.

Lemma canonify_ps_add_adjust_l : ∀ ps₁ ps₂ n k,
  canonify_ps (ps₁ + ps₂)%ps ≐
  canonify_ps (adjust_ps n k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ n k.
rewrite eq_canon_ps_add_adjust_0_l with (k := k).
apply canonify_ps_add_adjust.
Qed.

Lemma null_coeff_range_length_succ2 : ∀ s m,
  null_coeff_range_length rng s (S m) =
  null_coeff_range_length rng (series_left_shift m s) 1.
Proof.
intros s m.
remember (null_coeff_range_length rng s (S m)) as n eqn:Hn .
symmetry in Hn |- *.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop in Hn |- *.
destruct n as [n| ].
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin.
  unfold series_nth_rng; simpl.
  rewrite Nbar.fold_sub.
  destruct (Nbar.lt_dec (fin (S i)) (stop s - fin m)) as [H₁| H₁].
   rewrite Nat.add_succ_r, <- Nat.add_succ_l.
   apply Hz in Hin.
   unfold series_nth_rng in Hin.
   destruct (Nbar.lt_dec (fin (S m + i)) (stop s)) as [H₂| H₂].
    assumption.

    exfalso; apply H₂.
    apply Nbar.lt_add_lt_sub_r in H₁.
    simpl in H₁.
    rewrite Nat.add_comm, <- Nat.add_succ_l in H₁.
    assumption.

   reflexivity.

  unfold series_nth_rng; simpl.
  rewrite Nbar.fold_sub.
  unfold series_nth_rng in Hnz; simpl in Hnz.
  destruct (Nbar.lt_dec (fin (S (m + n))) (stop s)) as [H₁| H₁].
   rewrite <- Nat.add_succ_r in Hnz.
   destruct (Nbar.lt_dec (fin (S n)) (stop s - fin m)) as [H₂| H₂].
    assumption.

    exfalso; apply H₂.
    apply Nbar.lt_add_lt_sub_r.
    simpl; rewrite Nat.add_comm; assumption.

   exfalso; apply Hnz; reflexivity.

 intros i.
 pose proof (Hn i) as Hi.
 unfold series_nth_rng; simpl.
 rewrite Nbar.fold_sub.
 unfold series_nth_rng in Hi; simpl in Hi.
 destruct (Nbar.lt_dec (fin (S (m + i))) (stop s)) as [H₁| H₁].
  rewrite <- Nat.add_succ_r in Hi.
  destruct (Nbar.lt_dec (fin (S i)) (stop s - fin m)) as [H₂| H₂].
   assumption.

   reflexivity.

  destruct (Nbar.lt_dec (fin (S i)) (stop s - fin m)) as [H₂| H₂].
   exfalso; apply H₁.
   apply Nbar.lt_add_lt_sub_r in H₂.
   simpl in H₂.
   rewrite Nat.add_comm, <- Nat.add_succ_l in H₂.
   assumption.

   reflexivity.
Qed.

Lemma series_left_shift_left_shift : ∀ (s : series α) m n,
  (series_left_shift m (series_left_shift n s) =
   series_left_shift (m + n) s)%ser.
Proof.
intros s m n.
constructor; intros i.
unfold series_nth_rng; simpl.
do 3 rewrite Nbar.fold_sub.
rewrite Nbar.fin_inj_add.
rewrite Nbar.add_comm.
rewrite Nbar.sub_add_distr.
rewrite Nat.add_comm, Nat.add_shuffle0.
reflexivity.
Qed.

Lemma nth_null_coeff_range_length_left_shift : ∀ s m n p,
  nth_null_coeff_range_length (series_left_shift m s) n p =
  nth_null_coeff_range_length s n (m + p).
Proof.
intros s m n p.
revert m p.
induction n; intros; simpl.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite series_left_shift_left_shift.
 rewrite Nat.add_comm; reflexivity.

 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite series_left_shift_left_shift.
 rewrite Nat.add_comm.
 remember (null_coeff_range_length rng (series_left_shift (m + p) s) 1) as q.
 symmetry in Heqq.
 destruct q as [q| ].
  symmetry.
  rewrite <- Nat.add_assoc, <- Nat.add_succ_r.
  symmetry.
  apply IHn.

  reflexivity.
Qed.

Lemma greatest_series_x_power_left_shift : ∀ s n p,
  greatest_series_x_power rng (series_left_shift n s) p =
  greatest_series_x_power rng s (n + p).
Proof.
intros s n p.
remember (greatest_series_x_power rng s (n + p)) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
destruct Hk as (Hxp, Hnxp).
split.
 unfold is_a_series_in_x_power in Hxp |- *.
 rename n into m.
 intros n.
 rewrite nth_null_coeff_range_length_left_shift.
 apply Hxp.

 intros k₁ Hk₁.
 apply Hnxp in Hk₁.
 destruct Hk₁ as (m, Hm).
 exists m.
 rewrite nth_null_coeff_range_length_left_shift.
 assumption.
Qed.

Lemma canonifyd_exists_adjust : ∀ ps ps₁,
  null_coeff_range_length rng (ps_terms ps) 0 ≠ ∞
  → canonify_ps ps = ps₁
    → ∃ n k, eq_canon_ps ps (adjust_ps n k ps₁).
Proof.
intros ps ps₁ Hnz Heq.
unfold canonify_ps in Heq.
remember (null_coeff_range_length rng (ps_terms ps) 0) as len₁.
symmetry in Heqlen₁.
destruct len₁ as [len₁| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
subst ps₁.
unfold adjust_ps; simpl.
remember (greatest_series_x_power rng (ps_terms ps) len₁) as k₁.
remember (gcd_ps len₁ k₁ ps) as g.
symmetry in Heqg.
destruct g as [| g| g]; simpl.
 unfold gcd_ps in Heqg.
 apply Z.gcd_eq_0_r in Heqg.
 exfalso; revert Heqg; apply Pos2Z_ne_0.

 exists len₁, g.
 constructor; simpl.
  unfold gcd_ps in Heqg.
  remember (ps_valnum ps + Z.of_nat len₁)%Z as v.
  remember (Zpos (ps_comden ps))%Z as c.
  pose proof (Z.gcd_divide_l (Z.gcd v c) (Zpos k₁)) as H₁.
  destruct H₁ as (a, Ha).
  rewrite Heqg in Ha.
  pose proof (Z.gcd_divide_l v c) as H₁.
  destruct H₁ as (b, Hb).
  rewrite Ha in Hb.
  rewrite Z.mul_assoc in Hb.
  rewrite Hb.
  rewrite Z.div_mul; [ idtac | apply Pos2Z_ne_0 ].
  rewrite <- Hb.
  rewrite Heqv.
  rewrite Z.add_simpl_r.
  reflexivity.

  unfold gcd_ps in Heqg.
  remember (ps_valnum ps + Z.of_nat len₁)%Z as v.
  remember (Zpos (ps_comden ps)) as c.
  pose proof (Z.gcd_divide_l (Z.gcd v c) (Zpos k₁)) as H₁.
  destruct H₁ as (a, Ha).
  rewrite Heqg in Ha.
  pose proof (Z.gcd_divide_r v c) as H₁.
  destruct H₁ as (b, Hb).
  rewrite Ha in Hb.
  rewrite Z.mul_assoc in Hb.
  rewrite Hb.
  rewrite Z.div_mul; [ idtac | apply Pos2Z_ne_0 ].
  replace g with (Z.to_pos (Zpos g)) by apply Pos2Z.id.
  rewrite <- Z2Pos.inj_mul.
   rewrite <- Hb.
   rewrite Heqc; simpl.
   reflexivity.

   apply Z.mul_lt_mono_pos_r with (p := Zpos g).
    apply Pos2Z.is_pos.

    rewrite <- Hb; simpl.
    rewrite Heqc; apply Pos2Z.is_pos.

   apply Pos2Z.is_pos.

  unfold canonify_series.
  rewrite series_stretch_shrink.
   rewrite series_shift_left_shift; [ reflexivity | assumption ].

   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r.
   rewrite <- Heqk₁.
   unfold gcd_ps in Heqg.
   apply Pos2Z.inj_divide.
   rewrite <- Heqg.
   apply Z.gcd_divide_r.

 exfalso.
 pose proof (Zlt_neg_0 g) as H.
 rewrite <- Heqg in H.
 unfold gcd_ps in H.
 apply Z.nle_gt in H.
 apply H, Z.gcd_nonneg.
Qed.

Definition ps_neg_zero :=
  {| ps_terms := 0%ser; ps_valnum := -1; ps_comden := 1 |}.

Lemma eq_canon_ps_adjust_zero_neg_zero : ∀ ps,
  null_coeff_range_length rng (ps_terms ps) 0 = ∞
  → ∃ n₁ n₂ k₁ k₂,
    eq_canon_ps (adjust_ps n₁ k₁ ps) (adjust_ps n₂ k₂ ps_neg_zero).
Proof.
intros ps Hz.
unfold canonify_ps in Hz.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n; [ discriminate Hz | clear Hz ].
apply null_coeff_range_length_iff in Hn.
simpl in Hn.
destruct (Z_le_dec 0 (ps_valnum ps)) as [H₁| H₁].
 exists (Z.to_nat (ps_valnum ps + Zpos (ps_comden ps))), O, xH, (ps_comden ps).
 constructor; simpl.
  rewrite Z2Nat.id.
   rewrite Z.mul_1_r.
   rewrite Z.sub_add_distr, Z.sub_diag; reflexivity.

   apply Z.add_nonneg_nonneg; [ assumption | idtac ].
   apply Pos2Z.is_nonneg.

  rewrite Pos.mul_1_r; reflexivity.

  rewrite series_stretch_series_0.
  rewrite series_shift_series_0.
  rewrite series_stretch_1.
  constructor; intros i.
  rewrite series_nth_0_series_nth_shift_0.
   rewrite series_nth_series_0; reflexivity.

   assumption.

 exists (Pos.to_nat (ps_comden ps)).
 exists (Z.to_nat (- ps_valnum ps)).
 exists xH, (ps_comden ps).
 constructor; simpl.
  rewrite Z.mul_1_r.
  rewrite Z2Nat.id; [ idtac | omega ].
  rewrite Z.opp_involutive.
  remember (ps_valnum ps) as v.
  rewrite positive_nat_Z.
  destruct v; [ reflexivity | reflexivity | simpl ].
  rewrite Pos.add_comm; reflexivity.

  rewrite Pos.mul_1_r; reflexivity.

  rewrite series_stretch_1.
  rewrite series_stretch_series_0.
  constructor; intros i.
  rewrite series_nth_0_series_nth_shift_0.
   rewrite series_shift_series_0.
   rewrite series_nth_series_0; reflexivity.

   assumption.
Qed.

Lemma gcd_ps_is_pos : ∀ n k ps, (0 < gcd_ps n k ps)%Z.
Proof.
intros n k ps.
unfold gcd_ps; simpl.
remember (ps_valnum ps + Z.of_nat n)%Z as x.
rewrite <- Z.gcd_assoc.
remember (Z.gcd (' ps_comden ps) (' k))%Z as y eqn:Hy .
pose proof (Z.gcd_nonneg x y) as Hp.
destruct (Z_zerop (Z.gcd x y)) as [H₁| H₁]; [ idtac | omega ].
apply Z.gcd_eq_0_r in H₁.
rewrite Hy in H₁.
apply Z.gcd_eq_0_r in H₁.
exfalso; revert H₁; apply Pos2Z_ne_0.
Qed.

Lemma series_null_power : ∀ s b p,
  is_a_series_in_x_power s b p
  → ∀ i,
    ((i - b) mod Pos.to_nat p)%nat ≠ O
    → (series_nth_rng rng i s = 0)%rng.
Proof.
intros s b p Hxp i Hip.
destruct (le_dec i b) as [H₁| H₁].
 apply Nat.sub_0_le in H₁.
 rewrite H₁, Nat.mod_0_l in Hip; auto.
 exfalso; apply Hip; reflexivity.

 apply Nat.nle_gt in H₁.
 remember (i - b)%nat as j eqn:Hj .
 replace i with (b + j)%nat in * by omega.
 clear i Hj.
 eapply series_nth_0_in_interval_from_any with (c := S j).
  apply Nat.lt_succ_r; reflexivity.

  eassumption.

  unfold is_a_series_in_x_power in Hxp.
  apply Hxp.

  assumption.
Qed.

Lemma null_coeff_range_length_inf_iff : ∀ ps,
  null_coeff_range_length rng (ps_terms ps) 0 = ∞
  ↔ (ps = 0)%ps.
Proof.
intros ps.
split; intros H.
 constructor.
 unfold canonify_ps; simpl.
 rewrite H.
 remember (null_coeff_range_length rng 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | reflexivity ].
 apply null_coeff_range_length_iff in Hn.
 simpl in Hn.
 destruct Hn as (_, Hn).
 rewrite series_nth_series_0 in Hn.
 exfalso; apply Hn; reflexivity.

 inversion H; subst.
 apply null_coeff_range_length_iff; simpl; intros i.
 unfold canonify_ps in H0; simpl in H0.
 remember (null_coeff_range_length rng 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ].
  exfalso; clear H0.
  apply null_coeff_range_length_iff in Hn.
  simpl in Hn.
  destruct Hn as (_, Hn).
  apply Hn.
  apply series_nth_series_0.

  remember (null_coeff_range_length rng (ps_terms ps) 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   Focus 2.
   apply null_coeff_range_length_iff in Hm.
   simpl in Hm.
   apply Hm.

   inversion_clear H0.
   simpl in H1, H2, H3.
   remember (greatest_series_x_power rng (ps_terms ps) m) as p eqn:Hp .
   remember (gcd_ps m p ps) as g eqn:Hg .
   unfold canonify_series in H3.
   inversion_clear H3.
   apply null_coeff_range_length_iff in Hm.
   simpl in Hm.
   destruct Hm as (Hz, Hnz).
   destruct (lt_dec i m) as [H₁| H₁]; [ apply Hz; assumption | idtac ].
   apply Nat.nlt_ge in H₁.
   destruct (zerop ((i - m) mod Z.to_nat g)) as [H₂| H₂].
    apply Nat.mod_divides in H₂.
     destruct H₂ as (c, Hc).
     pose proof (H0 c) as Hi.
     rewrite series_nth_series_0 in Hi.
     rewrite <- series_nth_mul_shrink in Hi.
     rewrite Pos2Nat_to_pos in Hi.
      rewrite <- Hc in Hi.
      rewrite <- series_nth_add_left_shift in Hi.
      rewrite Nat.sub_add in Hi; assumption.

      rewrite Hg; apply gcd_ps_is_pos.

     pose proof (gcd_ps_is_pos m p ps) as H₃.
     rewrite <- Hg in H₃.
     rewrite <- Z2Nat.inj_0.
     intros H₄.
     apply Z2Nat.inj in H₄; [ idtac | idtac | reflexivity ].
      rewrite H₄ in H₃; revert H₃; apply Z.lt_irrefl.

      apply Z.lt_le_incl; assumption.

    symmetry in Hp.
    apply greatest_series_x_power_iff in Hp.
    unfold is_the_greatest_series_x_power in Hp.
    destruct Hp as (Hxp, Hnxp).
    eapply series_null_power; [ eassumption | idtac ].
    apply Nat.sub_gt in H₂; rewrite Nat.sub_0_r in H₂.
    intros H₃; apply H₂; clear H₂.
    pose proof (gcd_ps_is_pos m p ps) as Hgp.
    rewrite <- Hg in Hgp.
    unfold gcd_ps in Hg.
    remember (ps_valnum ps + Z.of_nat m)%Z as x.
    remember (Z.gcd x (' ps_comden ps)) as z.
    pose proof (Z.gcd_divide_r z (Zpos p)) as H₄.
    rewrite <- Hg in H₄.
    apply Nat.mod_divide in H₃; auto.
    apply Nat.mod_divide; auto.
     intros H₅.
     rewrite <- Z2Nat.inj_0 in H₅.
     apply Z2Nat.inj in H₅.
      rewrite H₅ in Hgp; revert Hgp; apply Z.lt_irrefl.

      apply Z.lt_le_incl; assumption.

      reflexivity.

     eapply Nat.divide_trans; [ idtac | eassumption ].
     destruct H₄ as (c, Hc).
     rewrite <- Z2Nat.inj_pos.
     rewrite Hc; simpl.
     exists (Z.to_nat c).
     rewrite Z2Nat.inj_mul.
      reflexivity.

       apply <- Z.mul_le_mono_pos_r; [ idtac | eassumption ].
      rewrite <- Hc; apply Pos2Z.is_nonneg.

      apply Z.lt_le_incl; assumption.
Qed.

Lemma null_coeff_range_length_inf_compat : ∀ ps₁ ps₂,
  canonify_ps ps₁ ≐ canonify_ps ps₂
  → null_coeff_range_length rng (ps_terms ps₁) 0 = ∞
    → null_coeff_range_length rng (ps_terms ps₂) 0 = ∞.
Proof.
intros ps₁ ps₂ Heq Hinf.
apply null_coeff_range_length_inf_iff in Hinf.
apply null_coeff_range_length_inf_iff.
inversion Hinf; constructor.
rewrite <- Heq, H; reflexivity.
Qed.

Lemma ps_canon_add_compat_r : ∀ ps₁ ps₂ ps₃,
  canonify_ps ps₁ ≐ canonify_ps ps₂
  → canonify_ps (ps₁ + ps₃)%ps ≐ canonify_ps (ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
remember (null_coeff_range_length rng (ps_terms ps₁) 0) as m₁ eqn:Hm₁ .
remember (null_coeff_range_length rng (ps_terms ps₂) 0) as m₂ eqn:Hm₂ .
symmetry in Hm₁, Hm₂.
destruct m₁ as [m₁| ].
 destruct m₂ as [m₂| ].
  remember (canonify_ps ps₁) as nps₁ eqn:Hps₁ .
  remember (canonify_ps ps₂) as nps₂ eqn:Hps₂ .
  symmetry in Hps₁, Hps₂.
  apply canonifyd_exists_adjust in Hps₁.
   apply canonifyd_exists_adjust in Hps₂.
    destruct Hps₁ as (n₁, (k₁, Hps₁)).
    destruct Hps₂ as (n₂, (k₂, Hps₂)).
    apply eq_canon_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
    apply eq_canon_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
    rewrite Hps₁, Hps₂.
    rewrite <- canonify_ps_add_adjust_l.
    rewrite <- canonify_ps_add_adjust_l.
    apply eq_canon_ps_add_compat_r with (ps₃ := ps₃) in Heq.
    rewrite Heq; reflexivity.

    rewrite Hm₂; intros H; discriminate H.

   rewrite Hm₁; intros H; discriminate H.

  symmetry in Heq.
  eapply null_coeff_range_length_inf_compat in Hm₂; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

 destruct m₂ as [m₂| ].
  eapply null_coeff_range_length_inf_compat in Hm₁; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

  apply eq_canon_ps_adjust_zero_neg_zero in Hm₁.
  apply eq_canon_ps_adjust_zero_neg_zero in Hm₂.
  destruct Hm₁ as (n₁, (n₂, (k₁, (k₂, Hps₁)))).
  destruct Hm₂ as (n₃, (n₄, (k₃, (k₄, Hps₂)))).
  apply eq_canon_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
  apply eq_canon_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
  rewrite canonify_ps_add_adjust_l with (n := n₁) (k := k₁).
  rewrite Hps₁; symmetry.
  rewrite canonify_ps_add_adjust_l with (n := n₃) (k := k₃).
  rewrite Hps₂; symmetry.
  rewrite <- canonify_ps_add_adjust_l.
  rewrite <- canonify_ps_add_adjust_l.
  reflexivity.
Qed.

Lemma ps_canon_add_compat_l : ∀ ps₁ ps₂ ps₃,
  canonify_ps ps₁ ≐ canonify_ps ps₂
  → canonify_ps (ps₃ + ps₁)%ps ≐ canonify_ps (ps₃ + ps₂)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
rewrite eq_canon_ps_add_comm; symmetry.
rewrite eq_canon_ps_add_comm; symmetry.
apply ps_canon_add_compat_r; assumption.
Qed.

Lemma null_coeff_range_length_series_0 :
  null_coeff_range_length rng series_0 0 = ∞.
Proof.
apply null_coeff_range_length_iff; simpl.
apply series_nth_series_0.
Qed.

Theorem ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₁ + ps₃ = ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
constructor.
apply ps_canon_add_compat_r.
inversion H₁₂; assumption.
Qed.

Theorem ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₃ + ps₁ = ps₃ + ps₂)%ps.
Proof.
intros ps1 ps₂ ps₃ H₁₂.
rewrite ps_add_comm; symmetry.
rewrite ps_add_comm; symmetry.
apply ps_add_compat_r; assumption.
Qed.

Add Parametric Morphism : ps_add
  with signature eq_canon_ps ==> eq_canon_ps ==> eq_canon_ps
  as ps_canon_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
rewrite eq_canon_ps_add_compat_l; [ idtac | eassumption ].
rewrite eq_canon_ps_add_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Add Parametric Morphism : ps_add₂
  with signature eq_canon_ps ==> eq_canon_ps ==> eq_canon_ps
  as ps_canon_add₂_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
do 2 rewrite <- eq_canon_ps_add_add₂.
rewrite eq_canon_ps_add_compat_l; [ idtac | eassumption ].
rewrite eq_canon_ps_add_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Add Parametric Morphism : ps_add
  with signature eq_ps ==> eq_ps ==> eq_ps
  as ps_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
transitivity (ps_add ps₁ ps₄).
 apply ps_add_compat_l; assumption.

 apply ps_add_compat_r; assumption.
Qed.
