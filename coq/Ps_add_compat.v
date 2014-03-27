(* Ps_add_compat.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Misc.
Require Import Field.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.

Section theorem_add_compat.

Variable α : Type.
Variable r : ring α.

Lemma series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i, (s .[i] = 0)%K)
  → ∀ i, ((series_shift r n s) .[i] = 0)%K.
Proof.
intros s n H i; simpl.
destruct (lt_dec i n) as [| H₁]; [ reflexivity | idtac ].
apply H.
Qed.

Lemma canonify_series_add_shift : ∀ s n m k,
  (canonify_series (n + m) k (series_shift r m s) =
   canonify_series n k s)%ser.
Proof.
intros s n m k.
unfold canonify_series.
constructor; intros i; simpl.
destruct (lt_dec (n + m + i * Pos.to_nat k) m) as [H₂| H₂].
 rewrite Nat.add_shuffle0, Nat.add_comm in H₂.
 apply Nat.nle_gt in H₂.
 exfalso; apply H₂.
 apply Nat.le_add_r.

 rewrite Nat.add_comm, Nat.add_assoc, Nat.add_sub.
 rewrite Nat.add_comm; reflexivity.
Qed.

Lemma eq_strong_ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  eq_ps_strong r ps₁ ps₂
  → eq_ps_strong r (ps₁ .+ r ps₃)%ps (ps₂ .+ r ps₃)%ps.
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

Lemma eq_strong_ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ ≐ r ps₂)%ps
  → (ps₃ .+ r ps₁ ≐ r ps₃ .+ r ps₂)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
rewrite eq_strong_ps_add_comm; symmetry.
rewrite eq_strong_ps_add_comm; symmetry.
apply eq_strong_ps_add_compat_r; assumption.
Qed.

Lemma ps_adjust_adjust : ∀ ps n₁ n₂ k₁ k₂,
  eq_ps_strong r (adjust_ps r n₁ k₁ (adjust_ps r n₂ k₂ ps))
    (adjust_ps r (n₁ + n₂ * Pos.to_nat k₁) (k₁ * k₂) ps).
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
  eq_ps_strong r (adjust_ps r n k (adjusted_ps_add r ps₁ ps₂))
    (adjusted_ps_add r (adjust_ps r n k ps₁) (adjust_ps r n k ps₂)).
Proof.
intros ps₁ ps₂ n k.
constructor; simpl; try reflexivity.
rewrite series_stretch_add_distr.
rewrite series_shift_add_distr.
reflexivity.
Qed.

Lemma eq_strong_ps_add_adjust_0_l : ∀ ps₁ ps₂ k,
  canonic_ps r (ps₁ .+ r ps₂)%ps ≐ r
  canonic_ps r (adjust_ps r 0 k ps₁ .+ r ps₂)%ps.
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
remember (ps_valnum ps₁ * ' ps_polord ps₂ * ' k)%Z as x eqn:Hx .
rewrite Z.mul_shuffle0 in Hx; rewrite <- Hx.
rewrite Pos.mul_comm.
remember (k * ps_polord ps₁)%positive as y eqn:Hy .
rewrite Pos.mul_comm in Hy; rewrite <- Hy.
rewrite Pos_mul_shuffle0, <- Hy.
reflexivity.
Qed.

Lemma canonic_ps_adjust : ∀ ps₁ ps₂ n,
  canonic_ps r (adjusted_ps_add r (adjust_ps r n 1 ps₁) (adjust_ps r n 1 ps₂))
  ≐ r canonic_ps r (adjusted_ps_add r ps₁ ps₂).
Proof.
(* gros nettoyage à faire : factorisation, focus, etc. *)
intros ps₁ ps₂ n.
rewrite <- ps_adjust_adjusted.
unfold canonic_ps.
simpl.
rewrite null_coeff_range_length_shift.
rewrite series_stretch_1.
remember
 (null_coeff_range_length r (series_add (ps_terms ps₁) (ps_terms ps₂))
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

Lemma canonic_ps_adjust_add : ∀ ps₁ ps₂ n n₁ n₂ k₁ k₂,
  canonic_ps r
    (adjusted_ps_add r
       (adjust_ps r (n + n₁) k₁ ps₁)
       (adjust_ps r (n + n₂) k₂ ps₂)) ≐ r
  canonic_ps r
    (adjusted_ps_add r
       (adjust_ps r n₁ k₁ ps₁)
       (adjust_ps r n₂ k₂ ps₂)).
Proof.
intros ps₁ ps₂ n n₁ n₂ k₁ k₂.
replace (n + n₁)%nat with (n + n₁ * Pos.to_nat 1)%nat .
 replace (n + n₂)%nat with (n + n₂ * Pos.to_nat 1)%nat .
  replace k₁ with (1 * k₁)%positive by reflexivity.
  rewrite <- ps_adjust_adjust.
  replace k₂ with (1 * k₂)%positive by reflexivity.
  rewrite <- ps_adjust_adjust.
  do 2 rewrite Pos.mul_1_l.
  rewrite canonic_ps_adjust; reflexivity.

  rewrite Nat.mul_1_r; reflexivity.

 rewrite Nat.mul_1_r; reflexivity.
Qed.

Lemma canonic_ps_add_adjust : ∀ ps₁ ps₂ n k m,
  canonic_ps r (adjust_ps r m k ps₁ .+ r ps₂)%ps ≐ r
  canonic_ps r (adjust_ps r n k ps₁ .+ r ps₂)%ps.
Proof.
intros ps₁ ps₂ n k m.
do 2 rewrite eq_strong_ps_canon_add_add₂.
unfold ps_add₂; simpl.
unfold adjust_ps_from.
unfold cm_factor; simpl.
do 2 rewrite ps_adjust_adjust.
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
remember (ps_valnum ps₁) as v₁.
remember (ps_polord ps₂) as c₂.
remember (ps_valnum ps₂) as v₂.
remember (ps_polord ps₁) as c₁.
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
       rewrite canonic_ps_adjust_add.
       replace (Z.to_nat (mm * Zpos c₂)) with
        (Z.to_nat (mm * Zpos c₂) + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonic_ps_adjust_add.
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
       rewrite canonic_ps_adjust_add.
       clear y Heqy.
       remember (Z.to_nat (mm * Zpos c₂ - x)) as y.
       replace y with (y + 0)%nat by omega.
       rewrite <- Nat.add_assoc; simpl.
       rewrite canonic_ps_adjust_add.
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

Lemma canonic_ps_add_adjust_l : ∀ ps₁ ps₂ n k,
  canonic_ps r (ps₁ .+ r ps₂)%ps ≐ r
  canonic_ps r (adjust_ps r n k ps₁ .+ r ps₂)%ps.
Proof.
intros ps₁ ps₂ n k.
rewrite eq_strong_ps_add_adjust_0_l with (k := k).
apply canonic_ps_add_adjust.
Qed.

Lemma canonified_exists_adjust : ∀ ps ps₁,
  null_coeff_range_length r (ps_terms ps) 0 ≠ ∞
  → canonic_ps r ps = ps₁
    → ∃ n k, eq_ps_strong r ps (adjust_ps r n k ps₁).
Proof.
intros ps ps₁ Hnz Heq.
unfold canonic_ps in Heq.
remember (null_coeff_range_length r (ps_terms ps) 0) as len₁.
symmetry in Heqlen₁.
destruct len₁ as [len₁| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
subst ps₁.
unfold adjust_ps; simpl.
remember (greatest_series_x_power r (ps_terms ps) len₁) as k₁.
remember (gcd_ps len₁ k₁ ps) as g.
symmetry in Heqg.
destruct g as [| g| g]; simpl.
 unfold gcd_ps in Heqg.
 rewrite Z.gcd_comm, Z.gcd_assoc in Heqg.
 apply Z.gcd_eq_0_r in Heqg.
 exfalso; revert Heqg; apply Pos2Z_ne_0.

 exists len₁, g.
 constructor; simpl.
  unfold gcd_ps in Heqg.
  remember (ps_valnum ps + Z.of_nat len₁)%Z as v.
  remember (Zpos (ps_polord ps))%Z as c.
  pose proof (Z.gcd_divide_l (Z.gcd v c) (Z.of_nat k₁)) as H₁.
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
  remember (Zpos (ps_polord ps)) as c.
  pose proof (Z.gcd_divide_l (Z.gcd v c) (Z.of_nat k₁)) as H₁.
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
   remember (ps_valnum ps + Z.of_nat len₁)%Z as x.
   remember (' ps_polord ps)%Z as y.
   pose proof (Z.gcd_divide_r (Z.gcd x y) (Z.of_nat k₁)) as H.
   rewrite Heqg in H.
   destruct H as (c, Hc).
   exists (Z.to_nat c).
   rewrite <- Z2Nat_inj_mul_pos_r.
   rewrite <- Hc.
   rewrite Nat2Z.id; reflexivity.

 exfalso.
 pose proof (Zlt_neg_0 g) as H.
 rewrite <- Heqg in H.
 unfold gcd_ps in H.
 apply Z.nle_gt in H.
 apply H, Z.gcd_nonneg.
Qed.

Definition ps_neg_zero :=
  {| ps_terms := 0%ser; ps_valnum := -1; ps_polord := 1 |}.

Lemma eq_strong_ps_adjust_zero_neg_zero : ∀ ps,
  null_coeff_range_length r (ps_terms ps) 0 = ∞
  → ∃ n₁ n₂ k₁ k₂,
    eq_ps_strong r (adjust_ps r n₁ k₁ ps) (adjust_ps r n₂ k₂ ps_neg_zero).
Proof.
intros ps Hz.
unfold canonic_ps in Hz.
remember (null_coeff_range_length r (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n; [ discriminate Hz | clear Hz ].
apply null_coeff_range_length_iff in Hn.
simpl in Hn.
destruct (Z_le_dec 0 (ps_valnum ps)) as [H₁| H₁].
 exists (Z.to_nat (ps_valnum ps + Zpos (ps_polord ps))), O, xH, (ps_polord ps).
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

 exists (Pos.to_nat (ps_polord ps)).
 exists (Z.to_nat (- ps_valnum ps)).
 exists xH, (ps_polord ps).
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

Lemma null_coeff_range_length_inf_compat : ∀ ps₁ ps₂,
  canonic_ps r ps₁ ≐ r canonic_ps r ps₂
  → null_coeff_range_length r (ps_terms ps₁) 0 = ∞
    → null_coeff_range_length r (ps_terms ps₂) 0 = ∞.
Proof.
intros ps₁ ps₂ Heq Hinf.
apply null_coeff_range_length_inf_iff in Hinf.
apply null_coeff_range_length_inf_iff.
inversion Hinf; constructor.
rewrite <- Heq, H; reflexivity.
Qed.

Lemma ps_canon_add_compat_r : ∀ ps₁ ps₂ ps₃,
  canonic_ps r ps₁ ≐ r canonic_ps r ps₂
  → canonic_ps r (ps₁ .+ r ps₃)%ps ≐ r canonic_ps r (ps₂ .+ r ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
remember (null_coeff_range_length r (ps_terms ps₁) 0) as m₁ eqn:Hm₁ .
remember (null_coeff_range_length r (ps_terms ps₂) 0) as m₂ eqn:Hm₂ .
symmetry in Hm₁, Hm₂.
destruct m₁ as [m₁| ].
 destruct m₂ as [m₂| ].
  remember (canonic_ps r ps₁) as nps₁ eqn:Hps₁ .
  remember (canonic_ps r ps₂) as nps₂ eqn:Hps₂ .
  symmetry in Hps₁, Hps₂.
  apply canonified_exists_adjust in Hps₁.
   apply canonified_exists_adjust in Hps₂.
    destruct Hps₁ as (n₁, (k₁, Hps₁)).
    destruct Hps₂ as (n₂, (k₂, Hps₂)).
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
    rewrite Hps₁, Hps₂.
    rewrite <- canonic_ps_add_adjust_l.
    rewrite <- canonic_ps_add_adjust_l.
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Heq.
    rewrite Heq; reflexivity.

    rewrite Hm₂; intros H; discriminate H.

   rewrite Hm₁; intros H; discriminate H.

  symmetry in Heq.
  eapply null_coeff_range_length_inf_compat in Hm₂; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

 destruct m₂ as [m₂| ].
  eapply null_coeff_range_length_inf_compat in Hm₁; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

  apply eq_strong_ps_adjust_zero_neg_zero in Hm₁.
  apply eq_strong_ps_adjust_zero_neg_zero in Hm₂.
  destruct Hm₁ as (n₁, (n₂, (k₁, (k₂, Hps₁)))).
  destruct Hm₂ as (n₃, (n₄, (k₃, (k₄, Hps₂)))).
  apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
  apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
  rewrite canonic_ps_add_adjust_l with (n := n₁) (k := k₁).
  rewrite Hps₁; symmetry.
  rewrite canonic_ps_add_adjust_l with (n := n₃) (k := k₃).
  rewrite Hps₂; symmetry.
  rewrite <- canonic_ps_add_adjust_l.
  rewrite <- canonic_ps_add_adjust_l.
  reflexivity.
Qed.

Theorem ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  (ps₁ .= r ps₂)%ps
  → (ps₁ .+ r ps₃ .= r ps₂ .+ r ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
constructor.
apply ps_canon_add_compat_r.
inversion H₁₂; assumption.
Qed.

Theorem ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ .= r ps₂)%ps
  → (ps₃ .+ r ps₁ .= r ps₃ .+ r ps₂)%ps.
Proof.
intros ps1 ps₂ ps₃ H₁₂.
rewrite ps_add_comm; symmetry.
rewrite ps_add_comm; symmetry.
apply ps_add_compat_r; assumption.
Qed.

End theorem_add_compat.

Add Parametric Morphism α (r : ring α) : (ps_add r)
  with signature eq_ps_strong r ==> eq_ps_strong r ==> eq_ps_strong r
  as ps_canon_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
rewrite eq_strong_ps_add_compat_l; [ idtac | eassumption ].
rewrite eq_strong_ps_add_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Add Parametric Morphism α (r : ring α) : (ps_add r)
  with signature eq_ps r ==> eq_ps r ==> eq_ps r
  as ps_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
transitivity (ps_add r ps₁ ps₄).
 apply ps_add_compat_l; assumption.

 apply ps_add_compat_r; assumption.
Qed.
