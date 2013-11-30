(* $Id: Ps_add_compat.v,v 2.12 2013-11-30 09:03:38 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Series.
Require Import Puiseux_series.
Require Import Nbar.
Require Import Ps_add.
Require Import Misc.

Delimit Scope ps_scope with ps.
Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ∔ b" := (nz_add a b) (at level 70).

Lemma series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i, series_nth_fld fld i s ≍ Lfield.zero fld)
  → ∀ i, series_nth_fld fld i (series_shift n s) ≍ Lfield.zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite series_shift_0; apply H.

 destruct i.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec 0 (stop s + fin (S n))); reflexivity.

  rewrite <- series_nth_shift_S; apply IHn.
Qed.

Lemma normalise_series_add_shift : ∀ s n m k,
  normalise_series (n + m) k (series_shift m s)
  ≃ normalise_series n k s.
Proof.
intros s n m k.
unfold normalise_series.
unfold series_shrink, series_left_shift.
constructor; intros i.
unfold series_nth_fld.
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

Lemma gcd_nz_add : ∀ nz n,
  gcd_nz (n + Z.to_nat (nz_valnum nz))
    (greatest_series_x_power fld
       (series_shift (Z.to_nat (nz_valnum nz)) (nz_terms nz))
       (n + Z.to_nat (nz_valnum nz))) (nz ∔ nz_zero) =
  gcd_nz n (greatest_series_x_power fld (nz_terms nz) n) nz.
Proof.
intros nz n.
unfold gcd_nz; simpl.
unfold nz_valnum_add.
rewrite Z.mul_1_r.
rewrite Nat2Z.inj_add.
rewrite Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite <- Z.add_assoc.
rewrite Z.add_comm.
unfold cm; simpl.
rewrite Pos.mul_1_r.
remember (nz_valnum nz) as z eqn:Hz .
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

Lemma normalise_nz_add_0_r : ∀ nz,
  normalise_nz (nz ∔ nz_zero) ≐ normalise_nz nz.
Proof.
intros nz.
unfold normalise_nz; simpl.
rewrite nz_add_0_r.
rewrite null_coeff_range_length_shift.
remember (null_coeff_range_length fld (nz_terms nz) 0) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
rewrite Nbar.add_comm.
destruct n₁ as [n₁| ]; [ simpl | reflexivity ].
constructor; constructor; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r.
 rewrite nz_add_0_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.add_assoc, Z.add_shuffle0.
 rewrite Z2Nat_id_max, Z.min_comm.
 f_equal; [ idtac | apply gcd_nz_add ].
 remember (nz_valnum nz) as z eqn:Hz .
 symmetry in Hz.
 destruct z; reflexivity.

 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 do 2 f_equal.
 rewrite nz_add_0_r.
 apply gcd_nz_add.

 rewrite nz_add_0_r.
 rewrite greatest_series_x_power_shift.
 constructor; intros i.
 rewrite normalise_series_add_shift.
 unfold gcd_nz; simpl.
 unfold cm; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r, Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 destruct (nz_valnum nz) as [| p| p]; simpl.
  rewrite Z.add_0_r; reflexivity.

  rewrite positive_nat_Z.
  destruct (Z.of_nat n₁); try reflexivity.
  rewrite Pos.add_comm; reflexivity.

  rewrite Z.add_0_r; reflexivity.
Qed.

Lemma eq_nz_add_compat_r : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz₁ ∔ nz₃) (nz₂ ∔ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 unfold nz_valnum_add.
 unfold cm_factor.
 rewrite H, H0.
 reflexivity.

 unfold cm.
 rewrite H0; reflexivity.

 unfold nz_terms_add.
 unfold cm_factor.
 unfold adjust_series.
 rewrite H, H0, H1.
 reflexivity.
Qed.

Lemma nz_adjust_adjust : ∀ nz n₁ n₂ k₁ k₂,
  eq_nz (adjust_nz n₁ k₁ (adjust_nz n₂ k₂ nz))
    (adjust_nz (n₁ + n₂ * Pos.to_nat k₁) (k₁ * k₂) nz).
Proof.
intros nz n₁ n₂ k₁ k₂.
unfold adjust_nz; simpl.
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

Lemma nz_adjust_adjusted : ∀ nz₁ nz₂ n k,
  eq_nz (adjust_nz n k (adjusted_nz_add nz₁ nz₂))
    (adjusted_nz_add (adjust_nz n k nz₁) (adjust_nz n k nz₂)).
Proof.
intros nz₁ nz₂ n k.
constructor; simpl; try reflexivity.
rewrite series_stretch_add_distr.
rewrite series_shift_add_distr.
reflexivity.
Qed.

Lemma adjust_nz_mul : ∀ nz n k u,
  eq_nz
    (adjust_nz (n * Pos.to_nat u) (k * u) nz)
    (adjust_nz 0 u (adjust_nz n k nz)).
Proof.
intros nz n k u.
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

Lemma eq_norm_ps_add_adjust_0_l : ∀ nz₁ nz₂ k,
  normalise_nz (nz₁ ∔ nz₂) ≐
  normalise_nz (adjust_nz 0 k nz₁ ∔ nz₂).
Proof.
(* à nettoyer (Focus) *)
intros nz₁ nz₂ k.
do 2 rewrite eq_nz_norm_add_add₂.
unfold nz_add₂; simpl.
unfold adjust_nz_from.
unfold cm_factor; simpl.
rewrite Z.sub_0_r.
rewrite nz_adjust_adjust.
rewrite Nat.mul_0_l, Nat.add_0_r.
symmetry.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
remember (nz_valnum nz₁ * Zpos k * Zpos (nz_comden nz₂))%Z as x eqn:Hx .
rewrite Z.mul_shuffle0 in Hx; subst x.
rewrite Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_sub_distr_r.
rewrite <- Z.mul_sub_distr_r.
rewrite Z2Nat.inj_mul.
 rewrite Z2Nat.inj_mul.
  Focus 1.
  simpl.
  do 2 rewrite adjust_nz_mul.
  rewrite <- nz_adjust_adjusted.
  rewrite <- nz_adjust_eq.
  reflexivity.

  rewrite <- Z.sub_max_distr_l, Z.sub_diag.
  apply Z.le_max_r.

  apply Pos2Z.is_nonneg.

 rewrite <- Z.sub_max_distr_l, Z.sub_diag.
 apply Z.le_max_r.

 apply Pos2Z.is_nonneg.
Qed.

Lemma normalise_nz_adjust : ∀ nz₁ nz₂ n,
  normalise_nz
    (adjusted_nz_add (adjust_nz n 1 nz₁) (adjust_nz n 1 nz₂))
  ≐ normalise_nz
      (adjusted_nz_add nz₁ nz₂).
Proof.
(* gros nettoyage à faire : factorisation, focus, etc. *)
intros nz₁ nz₂ n.
rewrite <- nz_adjust_adjusted.
unfold normalise_nz.
simpl.
rewrite null_coeff_range_length_shift.
rewrite series_stretch_1.
remember
 (null_coeff_range_length fld (series_add (nz_terms nz₁) (nz_terms nz₂))
    0)%Nbar as x.
rewrite Nbar.add_comm.
destruct x as [x| ]; [ simpl | reflexivity ].
constructor.
constructor; simpl.
 Focus 1.
 rewrite Z.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 f_equal.
 rewrite series_stretch_1.
 remember (series_add (nz_terms nz₁) (nz_terms nz₂)) as s.
 symmetry in Heqx.
 apply null_coeff_range_length_iff in Heqx.
 simpl in Heqx.
 destruct Heqx as (Hz, Hnz).
 unfold gcd_nz.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite Pos.mul_1_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.

 Focus 1.
 rewrite Pos.mul_1_r.
 f_equal.
 f_equal.
 rewrite series_stretch_1.
 remember (series_add (nz_terms nz₁) (nz_terms nz₂)) as s.
 symmetry in Heqx.
 unfold gcd_nz.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.

 rewrite series_stretch_1.
 rewrite normalise_series_add_shift.
 remember (series_add (nz_terms nz₁) (nz_terms nz₂)) as s.
 unfold gcd_nz.
 simpl.
 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite greatest_series_x_power_shift.
 reflexivity.
Qed.

Lemma normalise_nz_adjust_add : ∀ nz₁ nz₂ n n₁ n₂ k₁ k₂,
  normalise_nz
    (adjusted_nz_add
       (adjust_nz (n + n₁) k₁ nz₁)
       (adjust_nz (n + n₂) k₂ nz₂)) ≐
  normalise_nz
    (adjusted_nz_add
       (adjust_nz n₁ k₁ nz₁)
       (adjust_nz n₂ k₂ nz₂)).
Proof.
intros nz₁ nz₂ n n₁ n₂ k₁ k₂.
replace (n + n₁)%nat with (n + n₁ * Pos.to_nat 1)%nat .
 replace (n + n₂)%nat with (n + n₂ * Pos.to_nat 1)%nat .
  replace k₁ with (1 * k₁)%positive by reflexivity.
  rewrite <- nz_adjust_adjust.
  replace k₂ with (1 * k₂)%positive by reflexivity.
  rewrite <- nz_adjust_adjust.
  do 2 rewrite Pos.mul_1_l.
  rewrite normalise_nz_adjust; reflexivity.

  rewrite Nat.mul_1_r; reflexivity.

 rewrite Nat.mul_1_r; reflexivity.
Qed.

Lemma normalise_nz_adjust_nz_add : ∀ nz₁ nz₂ n k m,
  normalise_nz (adjust_nz m k nz₁ ∔ nz₂) ≐
  normalise_nz (adjust_nz n k nz₁ ∔ nz₂).
Proof.
(* à nettoyer : focus, simplifier peut-être... *)
intros nz₁ nz₂ n k.
intros m.
do 2 rewrite eq_nz_norm_add_add₂.
unfold nz_add₂; simpl.
unfold adjust_nz_from.
unfold cm_factor; simpl.
do 2 rewrite nz_adjust_adjust.
rewrite Pos2Z.inj_mul.
remember (nz_valnum nz₁) as v₁.
remember (nz_comden nz₂) as c₂.
remember (nz_valnum nz₂) as v₂.
remember (nz_comden nz₁) as c₁.
remember (Z.of_nat n) as nn.
remember (Z.of_nat m) as mm.
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_sub_distr_r.
replace n with (Z.to_nat nn) by (rewrite Heqnn, Nat2Z.id; reflexivity).
replace m with (Z.to_nat mm) by (rewrite Heqmm, Nat2Z.id; reflexivity).
simpl.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
rewrite <- Z2Nat.inj_add.
 rewrite <- Z2Nat.inj_add.
  do 2 rewrite <- Z.sub_add_distr.
  do 2 rewrite <- Z.add_sub_swap.
  do 2 rewrite Z.sub_add_distr.
  do 2 rewrite Z.add_simpl_r.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
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
    Focus 1.
    destruct (Z_le_dec vc₁ vc₂) as [H₁| H₁].
     Focus 1.
     rewrite Z2Nat.inj_add.
      3: omega.

      rewrite Z.add_comm.
      rewrite Z2Nat.inj_add.
       3: omega.

       rewrite Z.min_l; auto.
       rewrite Z.sub_diag.
       do 2 rewrite Nat.sub_0_r.
       rewrite <- Z2Nat_sub_min.
       rewrite Z.min_l; auto.
       rewrite Z.sub_diag, Nat.add_0_r.
       rewrite Nat.add_0_r.
       replace (Z.to_nat (nn * Zpos c₂)) with (Z.to_nat (nn * Zpos c₂) + 0)%nat
        by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite normalise_nz_adjust_add.
       replace (Z.to_nat (mm * Zpos c₂)) with (Z.to_nat (mm * Zpos c₂) + 0)%nat
        by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite normalise_nz_adjust_add.
       reflexivity.

       subst mm; simpl.
       destruct m; [ reflexivity | idtac ].
       simpl.
       apply Pos2Z.is_nonneg.

      subst nn; simpl.
      destruct n; [ reflexivity | simpl ].
      apply Pos2Z.is_nonneg.

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
      2: omega.

      rewrite <- Z2Nat.inj_sub.
       2: omega.

       remember (Z.to_nat (nn * Zpos c₂ - x)) as y.
       replace y with (y + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite normalise_nz_adjust_add.
       clear y Heqy.
       remember (Z.to_nat (mm * Zpos c₂ - x)) as y.
       replace y with (y + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite normalise_nz_adjust_add.
       reflexivity.

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

Lemma normalise_nz_adjust_nz_add_r : ∀ nz₁ nz₂ n k,
  normalise_nz (nz₁ ∔ nz₂) ≐
  normalise_nz (adjust_nz n k nz₁ ∔ nz₂).
Proof.
intros nz₁ nz₂ n k.
rewrite eq_norm_ps_add_adjust_0_l with (k := k).
apply normalise_nz_adjust_nz_add.
Qed.

Lemma null_coeff_range_length_succ2 : ∀ s m,
  null_coeff_range_length fld s (S m) =
  null_coeff_range_length fld (series_left_shift m s) 1.
Proof.
intros s m.
remember (null_coeff_range_length fld s (S m)) as n eqn:Hn .
symmetry in Hn |- *.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop in Hn |- *.
destruct n as [n| ].
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin.
  unfold series_nth_fld; simpl.
  rewrite Nbar.fold_sub.
  destruct (Nbar.lt_dec (fin (S i)) (stop s - fin m)) as [H₁| H₁].
   rewrite Nat.add_succ_r, <- Nat.add_succ_l.
   apply Hz in Hin.
   unfold series_nth_fld in Hin.
   destruct (Nbar.lt_dec (fin (S m + i)) (stop s)) as [H₂| H₂].
    assumption.

    exfalso; apply H₂.
    apply Nbar.lt_add_lt_sub_r in H₁.
    simpl in H₁.
    rewrite Nat.add_comm, <- Nat.add_succ_l in H₁.
    assumption.

   reflexivity.

  unfold series_nth_fld; simpl.
  rewrite Nbar.fold_sub.
  unfold series_nth_fld in Hnz; simpl in Hnz.
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
 unfold series_nth_fld; simpl.
 rewrite Nbar.fold_sub.
 unfold series_nth_fld in Hi; simpl in Hi.
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
  series_left_shift m (series_left_shift n s) ≃ series_left_shift (m + n) s.
Proof.
intros s m n.
constructor; intros i.
unfold series_nth_fld; simpl.
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
 remember (null_coeff_range_length fld (series_left_shift (m + p) s) 1) as q.
 symmetry in Heqq.
 destruct q as [q| ].
  symmetry.
  rewrite <- Nat.add_assoc, <- Nat.add_succ_r.
  symmetry.
  apply IHn.

  reflexivity.
Qed.

Lemma greatest_series_x_power_left_shift : ∀ s n p,
  greatest_series_x_power fld (series_left_shift n s) p =
  greatest_series_x_power fld s (n + p).
Proof.
intros s n p.
remember (greatest_series_x_power fld s (n + p)) as k eqn:Hk .
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

Lemma normalised_exists_adjust : ∀ nz nz₁,
  normalise_nz nz = NonZero nz₁
  → ∃ n k, eq_nz nz (adjust_nz n k nz₁).
Proof.
intros nz nz₁ Heq.
unfold normalise_nz in Heq.
remember (null_coeff_range_length fld (nz_terms nz) 0) as len₁.
symmetry in Heqlen₁.
destruct len₁ as [len₁| ]; [ idtac | discriminate Heq ].
injection Heq; clear Heq; intros Heq; symmetry in Heq.
subst nz₁.
unfold adjust_nz; simpl.
remember (greatest_series_x_power fld (nz_terms nz) len₁) as k₁.
remember (gcd_nz len₁ k₁ nz) as g.
symmetry in Heqg.
destruct g as [| g| g]; simpl.
 Focus 1.
 unfold gcd_nz in Heqg.
 apply Z.gcd_eq_0_r in Heqg.
 exfalso; revert Heqg; apply Pos2Z_ne_0.

 exists len₁, g.
 constructor; simpl.
  unfold gcd_nz in Heqg.
  remember (nz_valnum nz + Z.of_nat len₁)%Z as v.
  remember (Zpos (nz_comden nz))%Z as c.
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

  unfold gcd_nz in Heqg.
  remember (nz_valnum nz + Z.of_nat len₁)%Z as v.
  remember (Zpos (nz_comden nz)) as c.
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

  unfold normalise_series.
  rewrite series_stretch_shrink.
   rewrite series_shift_left_shift; [ reflexivity | assumption ].

   rewrite greatest_series_x_power_left_shift.
   rewrite Nat.add_0_r.
   rewrite <- Heqk₁.
   unfold gcd_nz in Heqg.
   apply Pos2Z.inj_divide.
   rewrite <- Heqg.
   apply Z.gcd_divide_r.

 exfalso.
 pose proof (Zlt_neg_0 g) as H.
 rewrite <- Heqg in H.
 unfold gcd_nz in H.
 apply Z.nle_gt in H.
 apply H, Z.gcd_nonneg.
Qed.

Definition nz_neg_zero :=
  {| nz_terms := series_0;
     nz_valnum := -1;
     nz_comden := 1 |}.

Lemma eq_nz_adjust_zero_neg_zero : ∀ nz,
  normalise_nz nz = Zero α
  → ∃ n₁ n₂ k₁ k₂,
    eq_nz (adjust_nz n₁ k₁ nz) (adjust_nz n₂ k₂ nz_neg_zero).
Proof.
intros nz Hz.
unfold normalise_nz in Hz.
remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
symmetry in Hn.
destruct n; [ discriminate Hz | clear Hz ].
apply null_coeff_range_length_iff in Hn.
simpl in Hn.
destruct (Z_le_dec 0 (nz_valnum nz)) as [H₁| H₁].
 exists (Z.to_nat (nz_valnum nz + Zpos (nz_comden nz))), O, xH, (nz_comden nz).
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

 exists (Pos.to_nat (nz_comden nz)), (Z.to_nat (- nz_valnum nz)), 
  xH, (nz_comden nz).
 constructor; simpl.
  rewrite Z.mul_1_r.
  rewrite Z2Nat.id; [ idtac | omega ].
  rewrite Z.opp_involutive.
  remember (nz_valnum nz) as v.
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

Lemma nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz nz₁ ≐ normalise_nz nz₂
  → normalise_nz (nz₁ ∔ nz₃) ≐ normalise_nz (nz₂ ∔ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
remember (normalise_nz nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz nz₂) as ps₂ eqn:Hps₂ .
symmetry in Hps₁, Hps₂.
destruct ps₁ as [nz'₁| ].
 destruct ps₂ as [nz'₂| ]; [ idtac | inversion Heq ].
 apply normalised_exists_adjust in Hps₁.
 apply normalised_exists_adjust in Hps₂.
 destruct Hps₁ as (n₁, (k₁, Hps₁)).
 destruct Hps₂ as (n₂, (k₂, Hps₂)).
 inversion Heq; subst.
 apply eq_nz_add_compat_r with (nz₃ := nz₃) in Hps₁.
 apply eq_nz_add_compat_r with (nz₃ := nz₃) in Hps₂.
 rewrite Hps₁, Hps₂.
 rewrite <- normalise_nz_adjust_nz_add_r.
 rewrite <- normalise_nz_adjust_nz_add_r.
 apply eq_nz_add_compat_r with (nz₃ := nz₃) in H1.
 rewrite H1; reflexivity.

 destruct ps₂ as [nz'₂| ]; [ inversion Heq | idtac ].
 apply eq_nz_adjust_zero_neg_zero in Hps₁.
 apply eq_nz_adjust_zero_neg_zero in Hps₂.
 destruct Hps₁ as (n₁, (n₂, (k₁, (k₂, Hps₁)))).
 destruct Hps₂ as (n₃, (n₄, (k₃, (k₄, Hps₂)))).
 apply eq_nz_add_compat_r with (nz₃ := nz₃) in Hps₁.
 apply eq_nz_add_compat_r with (nz₃ := nz₃) in Hps₂.
 rewrite normalise_nz_adjust_nz_add_r with (n := n₁) (k := k₁).
 rewrite Hps₁; symmetry.
 rewrite normalise_nz_adjust_nz_add_r with (n := n₃) (k := k₃).
 rewrite Hps₂; symmetry.
 rewrite <- normalise_nz_adjust_nz_add_r.
 rewrite <- normalise_nz_adjust_nz_add_r.
 reflexivity.
Qed.

Lemma null_coeff_range_length_series_0 :
  null_coeff_range_length fld series_0 0 = ∞.
Proof.
apply null_coeff_range_length_iff; simpl.
apply series_nth_series_0.
Qed.

Lemma ps_add_0_l_compat_r : ∀ nz₁ nz₂,
  NonZero nz₁ ≈ Zero α
  → NonZero (nz₁ ∔ nz₂) ≈ NonZero nz₂.
Proof.
intros nz₁ nz₂.
constructor.
rewrite nz_norm_add_compat_r with (nz₂ := nz_zero).
 rewrite nz_norm_add_comm.
 rewrite normalise_nz_add_0_r.
 reflexivity.

 inversion H; subst.
 inversion H1; subst.
 unfold normalise_nz; simpl.
 rewrite null_coeff_range_length_series_0.
 remember (null_coeff_range_length fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
 symmetry in Hn₁.
 destruct n₁ as [n₁| ]; [ exfalso | reflexivity ].
 apply null_coeff_range_length_iff in Hn₁.
 simpl in Hn₁.
 destruct Hn₁ as (Hz, Hnz).
 rewrite H0 in Hnz.
 apply Hnz.
 apply series_nth_series_0.
Qed.

Theorem ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₁ + ps₃)%ps ≈ (ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
destruct ps₃ as [nz₃| ]; [ idtac | do 2 rewrite ps_add_0_r; assumption ].
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | simpl ].
  constructor.
  apply nz_norm_add_compat_r.
  inversion H₁₂; assumption.

  apply ps_add_0_l_compat_r; assumption.

 destruct ps₂ as [nz₂| ]; [ simpl | reflexivity ].
 symmetry.
 apply ps_add_0_l_compat_r.
 symmetry.
 assumption.
Qed.

Theorem ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₃ + ps₁)%ps ≈ (ps₃ + ps₂)%ps.
Proof.
intros ps1 ps₂ ps₃ H₁₂.
rewrite ps_add_comm; symmetry.
rewrite ps_add_comm; symmetry.
apply ps_add_compat_r; assumption.
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
