(* Ps_add_compat.v *)

From Stdlib Require Import Utf8 Arith.

Require Import A_PosArith A_ZArith.
Require Import NbarM.
Require Import Misc.
Require Import Field2.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.

Section theorem_add_compat.

Variable α : Type.
Variable r : ring α.
Variable K : field r.

Theorem series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i, (s .[i] = 0)%K)
  → ∀ i, ((series_shift n s) .[i] = 0)%K.
Proof.
intros s n H i; simpl.
destruct (lt_dec i n) as [| H₁]; [ reflexivity | idtac ].
apply H.
Qed.

Theorem normalise_series_add_shift : ∀ s n m k,
  (normalise_series (n + m) k (series_shift m s) =
   normalise_series n k s)%ser.
Proof.
intros s n m k.
unfold normalise_series.
constructor; intros i; simpl.
destruct (lt_dec (n + m + i * Pos.to_nat k) m) as [H₂| H₂].
 rewrite Nat.add_shuffle0, Nat.add_comm in H₂.
 apply Nat.nle_gt in H₂.
 exfalso; apply H₂.
 apply Nat.le_add_r.

 rewrite Nat.add_comm, Nat.add_assoc, Nat.add_sub.
 rewrite Nat.add_comm; reflexivity.
Qed.

Theorem eq_strong_ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  eq_ps_strong ps₁ ps₂
  → eq_ps_strong (ps₁ + ps₃)%ps (ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
induction Heq.
unfold ps_add.
constructor; simpl.
 unfold ps_ordnum_add.
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

Theorem ps_adjust_adjust : ∀ ps n₁ n₂ k₁ k₂,
  eq_ps_strong (adjust_ps n₁ k₁ (adjust_ps n₂ k₂ ps))
    (adjust_ps (n₁ + n₂ * Pos.to_nat k₁) (k₁ * k₂) ps).
Proof.
intros ps n₁ n₂ k₁ k₂.
unfold adjust_ps; simpl.
constructor; simpl. {
  rewrite Z.mul_sub_distr_r.
  rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_mul_swap.
  rewrite <- Z.sub_add_distr; f_equal.
  rewrite Nat2Z.inj_add, Z.add_comm; f_equal.
  rewrite Nat2Z.inj_mul, Z.pos_nat.
  reflexivity.
} {
  rewrite Pos.mul_assoc, Pos.mul_mul_swap.
  reflexivity.
} {
  rewrite stretch_shift_series_distr.
  rewrite series_shift_shift.
  rewrite series_stretch_stretch.
  reflexivity.
}
Qed.

Theorem ps_adjust_adjusted : ∀ ps₁ ps₂ n k,
  eq_ps_strong (adjust_ps n k (adjusted_ps_add ps₁ ps₂))
    (adjusted_ps_add (adjust_ps n k ps₁) (adjust_ps n k ps₂)).
Proof.
intros ps₁ ps₂ n k.
constructor; simpl; try reflexivity.
rewrite series_stretch_add_distr.
rewrite series_shift_add_distr.
reflexivity.
Qed.

Theorem eq_strong_ps_add_adjust_0_l : ∀ ps₁ ps₂ k,
  normalise_ps (ps₁ + ps₂)%ps ≐
  normalise_ps (adjust_ps 0 k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ k.
rewrite ps_normal_adjust_eq with (n := O) (k := k).
unfold ps_add; simpl.
unfold adjust_ps; simpl.
unfold ps_terms_add, ps_ordnum_add, adjust_series, cm, cm_factor; simpl.
do 2 rewrite series_shift_0.
do 2 rewrite Z.sub_0_r.
rewrite series_stretch_add_distr.
do 2 rewrite stretch_shift_series_distr.
do 3 rewrite <- series_stretch_stretch.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
do 2 rewrite Z.mul_sub_distr_r.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
remember (ps_ordnum ps₁ * z_pos (ps_polydo ps₂) * z_pos k)%Z as x eqn:Hx .
rewrite Z.mul_mul_swap in Hx; rewrite <- Hx.
rewrite Pos.mul_comm.
remember (k * ps_polydo ps₁)%pos as y eqn:Hy .
rewrite Pos.mul_comm in Hy; rewrite <- Hy.
rewrite Pos.mul_mul_swap, <- Hy.
reflexivity.
Qed.

Theorem normalise_ps_adjust : ∀ ps₁ ps₂ n,
  normalise_ps (adjusted_ps_add (adjust_ps n 1 ps₁) (adjust_ps n 1 ps₂))
  ≐ normalise_ps (adjusted_ps_add ps₁ ps₂).
Proof.
intros ps₁ ps₂ n.
rewrite <- ps_adjust_adjusted.
unfold normalise_ps.
simpl.
rewrite series_order_shift.
rewrite series_stretch_1.
remember
 (series_order (series_add (ps_terms ps₁) (ps_terms ps₂))
    0)%Nbar as x.
rewrite Nbar.add_comm.
destruct x as [x| ]; [ simpl | reflexivity ].
constructor; simpl. {
  rewrite Z.mul_1_r.
  rewrite Nat2Z.inj_add.
  rewrite (Z.add_comm (Z.of_nat x)), Z.add_assoc, Z.sub_add.
  rewrite series_stretch_1.
  remember (series_add (ps_terms ps₁) (ps_terms ps₂)) as s.
  symmetry in Heqx.
  apply series_order_iff in Heqx.
  simpl in Heqx.
  destruct Heqx as (Hz, Hnz).
  progress unfold gcd_ps.
  simpl.
  rewrite Z.mul_1_r.
  rewrite Nat2Z.inj_add.
  rewrite (Z.add_comm (Z.of_nat x)), Z.add_assoc, Z.sub_add.
  rewrite Pos.mul_1_r.
  rewrite greatest_series_x_power_shift.
  reflexivity.
} {
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
  rewrite (Z.add_comm (Z.of_nat x)), Z.add_assoc, Z.sub_add.
  rewrite greatest_series_x_power_shift.
  reflexivity.
} {
  rewrite series_stretch_1.
  rewrite normalise_series_add_shift.
  remember (series_add (ps_terms ps₁) (ps_terms ps₂)) as s.
  unfold gcd_ps.
  simpl.
  rewrite Z.mul_1_r.
  rewrite Pos.mul_1_r.
  rewrite Nat2Z.inj_add.
  rewrite (Z.add_comm (Z.of_nat x)), Z.add_assoc, Z.sub_add.
  rewrite greatest_series_x_power_shift.
  reflexivity.
}
Qed.

Theorem normalise_ps_adjust_add : ∀ ps₁ ps₂ n n₁ n₂ k₁ k₂,
  normalise_ps
    (adjusted_ps_add
       (adjust_ps (n + n₁) k₁ ps₁)
       (adjust_ps (n + n₂) k₂ ps₂)) ≐
  normalise_ps
    (adjusted_ps_add
       (adjust_ps n₁ k₁ ps₁)
       (adjust_ps n₂ k₂ ps₂)).
Proof.
intros ps₁ ps₂ n n₁ n₂ k₁ k₂.
replace (n + n₁)%nat with (n + n₁ * Pos.to_nat 1)%nat .
 replace (n + n₂)%nat with (n + n₂ * Pos.to_nat 1)%nat .
  replace k₁ with (1 * k₁)%pos by now rewrite Pos.mul_1_l.
  rewrite <- ps_adjust_adjust.
  replace k₂ with (1 * k₂)%pos by now rewrite Pos.mul_1_l.
  rewrite <- ps_adjust_adjust.
  do 2 rewrite Pos.mul_1_l.
  rewrite normalise_ps_adjust; reflexivity.

  rewrite Nat.mul_1_r; reflexivity.

 rewrite Nat.mul_1_r; reflexivity.
Qed.

Theorem normalise_ps_add_adjust : ∀ ps₁ ps₂ n k m,
  normalise_ps (adjust_ps m k ps₁ + ps₂)%ps ≐
  normalise_ps (adjust_ps n k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ n k m.
do 2 rewrite eq_strong_ps_normal_add_add₂.
unfold ps_add₂; simpl.
unfold adjust_ps_from.
unfold cm_factor; simpl.
do 2 rewrite ps_adjust_adjust.
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
remember (ps_ordnum ps₁) as v₁.
remember (ps_polydo ps₂) as c₂.
remember (ps_ordnum ps₂) as v₂.
remember (ps_polydo ps₁) as c₁.
remember (Z.of_nat n) as nn.
remember (Z.of_nat m) as mm.
do 2 rewrite Z.mul_sub_distr_r.
replace n with (Z.to_nat nn) by (rewrite Heqnn, Nat2Z.id; reflexivity).
replace m with (Z.to_nat mm) by (rewrite Heqmm, Nat2Z.id; reflexivity).
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
rewrite <- Z2Nat.inj_add. {
  rewrite <- Z2Nat.inj_add. {
    do 2 rewrite <- Z.sub_add_distr.
    do 2 rewrite <- Z.add_sub_swap.
    do 2 rewrite Z.sub_add_distr.
    do 2 rewrite Z.add_sub.
    rewrite Z.mul_mul_swap.
    progress unfold Z.of_pos.
    remember (v₁ * z_pos c₂ * z_pos k)%Z as vc₁.
    remember (v₂ * z_pos c₁ * z_pos k)%Z as vc₂.
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
    rewrite Z2Nat.inj_sub. {
      symmetry.
      rewrite Z2Nat.inj_sub. {
        rewrite Z.add_comm.
        destruct (Z.le_dec vc₁ vc₂) as [H₁| H₁]. {
          rewrite Z2Nat.inj_add. {
            rewrite Z.add_comm.
            rewrite Z2Nat.inj_add. {
              rewrite Z.min_l; [ | easy ].
              rewrite Z.sub_diag.
              do 2 rewrite Nat.sub_0_r.
              rewrite <- Z2Nat_sub_min.
              rewrite Z.min_l; [ | easy ].
              rewrite Z.sub_diag, Nat.add_0_r.
              rewrite Nat.add_0_r.
              rewrite <- (Nat.add_0_r (Z.to_nat (nn * z_pos c₂))).
              rewrite <- Nat.add_assoc; simpl.
              rewrite normalise_ps_adjust_add.
              rewrite <- (Nat.add_0_r (Z.to_nat (mm * z_pos c₂))).
              rewrite <- Nat.add_assoc; simpl.
              rewrite normalise_ps_adjust_add.
              reflexivity.
            } {
              subst mm; simpl.
              destruct m; [ reflexivity | easy ].
            }
            now apply Z.le_0_sub.
          } {
            subst nn; simpl.
            destruct n; [ reflexivity | easy ].
          }
          now apply Z.le_0_sub.
        }
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
        rewrite <- Z2Nat.inj_sub. {
          rewrite <- Z2Nat.inj_sub. {
            remember (Z.to_nat (nn * z_pos c₂ - x)) as y.
            replace y with (y + 0)%nat by fast_omega.
            rewrite <- Nat.add_assoc; simpl.
            rewrite normalise_ps_adjust_add.
            clear y Heqy.
            remember (Z.to_nat (mm * z_pos c₂ - x)) as y.
            replace y with (y + 0)%nat by fast_omega.
            rewrite <- Nat.add_assoc; simpl.
            rewrite normalise_ps_adjust_add.
            reflexivity.
          }
          subst x.
          now apply Z.le_0_sub, Z.lt_le_incl.
        }
        subst x.
        now apply Z.le_0_sub, Z.lt_le_incl.
      }
      rewrite <- Z.sub_max_distr_l, Z.sub_diag.
      apply Z.le_max_l.
    }
    rewrite <- Z.sub_max_distr_l, Z.sub_diag.
    apply Z.le_max_l.
  } {
    rewrite <- Z.sub_max_distr_l, Z.sub_diag.
    apply Z.le_max_r.
  }
  subst nn.
  destruct n; [ reflexivity | easy ].
} {
  rewrite <- Z.sub_max_distr_l, Z.sub_diag.
  apply Z.le_max_r.
}
subst mm.
destruct m; [ reflexivity | easy ].
Qed.

Theorem normalise_ps_add_adjust_l : ∀ ps₁ ps₂ n k,
  normalise_ps (ps₁ + ps₂)%ps ≐
  normalise_ps (adjust_ps n k ps₁ + ps₂)%ps.
Proof.
intros ps₁ ps₂ n k.
rewrite eq_strong_ps_add_adjust_0_l with (k := k).
apply normalise_ps_add_adjust.
Qed.

Theorem normalised_exists_adjust : ∀ ps ps₁,
  series_order (ps_terms ps) 0 ≠ ∞
  → normalise_ps ps = ps₁
    → ∃ n k, eq_ps_strong ps (adjust_ps n k ps₁).
Proof.
intros ps ps₁ Hnz Heq.
unfold normalise_ps in Heq.
remember (series_order (ps_terms ps) 0) as len₁.
symmetry in Heqlen₁.
destruct len₁ as [len₁| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
subst ps₁.
unfold adjust_ps; simpl.
remember (greatest_series_x_power K (ps_terms ps) len₁) as k₁.
remember (gcd_ps len₁ k₁ ps) as g.
symmetry in Heqg.
destruct g as [| sg vg]; simpl. {
  unfold gcd_ps in Heqg.
  rewrite Z.gcd_comm, Z.gcd_assoc in Heqg.
  apply Z.gcd_eq_0_r in Heqg.
  exfalso; revert Heqg; apply Pos2Z_ne_0.
}
destruct sg. {
  exists len₁, vg.
  constructor; simpl. {
    unfold gcd_ps in Heqg.
    remember (ps_ordnum ps + Z.of_nat len₁)%Z as v.
    remember (z_pos (ps_polydo ps))%Z as c.
    pose proof (Z.gcd_divide_l (Z.gcd v c) (Z.of_nat k₁)) as H₁.
    destruct H₁ as (a, Ha).
    rewrite Heqg in Ha.
    pose proof (Z.gcd_divide_l v c) as H₁.
    destruct H₁ as (b, Hb).
    rewrite Ha in Hb.
    rewrite Z.mul_assoc in Hb.
    rewrite Hb.
    rewrite Z.mul_div; [ idtac | apply Pos2Z_ne_0 ].
    progress unfold z_pos.
    rewrite <- Hb.
    rewrite Heqv.
    rewrite Z.add_sub.
    reflexivity.
  } {
    unfold gcd_ps in Heqg.
    remember (ps_ordnum ps + Z.of_nat len₁)%Z as v.
    remember (z_pos (ps_polydo ps)) as c.
    pose proof (Z.gcd_divide_l (Z.gcd v c) (Z.of_nat k₁)) as H₁.
    destruct H₁ as (a, Ha).
    rewrite Heqg in Ha.
    pose proof (Z.gcd_divide_r v c) as H₁.
    destruct H₁ as (b, Hb).
    rewrite Ha in Hb.
    rewrite Z.mul_assoc in Hb.
    rewrite Hb.
    rewrite Z.mul_div; [ idtac | apply Pos2Z_ne_0 ].
    replace vg with (Z.to_pos (z_pos vg)) by easy.
    rewrite <- Z2Pos.inj_mul; [ | | easy ]. {
      progress unfold z_pos.
      rewrite <- Hb.
      rewrite Heqc; simpl.
      reflexivity.
    } {
      apply (Z.mul_lt_mono_pos_r (z_pos vg)); [ easy | ].
      progress unfold z_pos.
      rewrite <- Hb; simpl.
      now rewrite Heqc.
    }
  }
  unfold normalise_series.
  rewrite series_stretch_shrink.
  rewrite series_shift_left_shift; [ reflexivity | apply Heqlen₁ ].
  rewrite greatest_series_x_power_left_shift.
  rewrite Nat.add_0_r.
  rewrite <- Heqk₁.
  unfold gcd_ps in Heqg.
  remember (ps_ordnum ps + Z.of_nat len₁)%Z as x.
  remember (z_pos (ps_polydo ps))%Z as y.
  pose proof (Z.gcd_divide_r (Z.gcd x y) (Z.of_nat k₁)) as H.
  rewrite Heqg in H.
  destruct H as (c, Hc).
  exists (Z.to_nat c).
  rewrite <- Z2Nat_inj_mul_pos_r.
  progress unfold z_pos.
  rewrite <- Hc.
  rewrite Nat2Z.id; reflexivity.
}
exfalso.
assert (H : (z_val false vg < 0)%Z) by easy.
rewrite <- Heqg in H.
unfold gcd_ps in H.
apply Z.nle_gt in H.
apply H, Z.gcd_nonneg.
Qed.

Definition ps_neg_zero :=
  {| ps_terms := 0%ser; ps_ordnum := -1; ps_polydo := 1 |}.

Theorem eq_strong_ps_adjust_zero_neg_zero : ∀ ps,
  series_order (ps_terms ps) 0 = ∞
  → ∃ n₁ n₂ k₁ k₂,
    eq_ps_strong (adjust_ps n₁ k₁ ps) (adjust_ps n₂ k₂ ps_neg_zero).
Proof.
intros ps Hz.
unfold normalise_ps in Hz.
remember (series_order (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n; [ discriminate Hz | clear Hz ].
apply series_order_iff in Hn.
simpl in Hn.
destruct (Z.le_dec 0 (ps_ordnum ps)) as [H₁| H₁]. {
  exists (Z.to_nat (ps_ordnum ps + z_pos (ps_polydo ps))).
  exists O, 1%pos, (ps_polydo ps).
  constructor; simpl. {
    rewrite Z2Nat.id. {
      rewrite Z.mul_1_r, Pos.mul_1_l.
      rewrite Z.sub_add_distr, Z.sub_diag; reflexivity.
    }
    apply Z.add_nonneg_nonneg; [ assumption | easy ].
  } {
    rewrite Pos.mul_1_r, Pos.mul_1_l; reflexivity.
  }
  rewrite series_stretch_series_0.
  rewrite series_shift_series_0.
  rewrite series_stretch_1.
  constructor; intros i.
  rewrite series_nth_0_series_nth_shift_0; [ | easy ].
  rewrite series_nth_series_0; reflexivity.
}
exists (Pos.to_nat (ps_polydo ps)).
exists (Z.to_nat (- ps_ordnum ps)).
exists 1%pos, (ps_polydo ps).
constructor; simpl. {
  rewrite Z.mul_1_r.
  apply Z.nle_gt in H₁.
  rewrite Z2Nat.id. 2: {
    apply Z.opp_le_compat.
    rewrite Z.opp_involutive.
    now apply Z.lt_le_incl.
  }
  rewrite Z.opp_involutive.
  remember (ps_ordnum ps) as v.
  rewrite Z.pos_nat.
...
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

Theorem series_order_inf_compat : ∀ ps₁ ps₂,
  normalise_ps ps₁ ≐ normalise_ps ps₂
  → series_order (ps_terms ps₁) 0 = ∞
    → series_order (ps_terms ps₂) 0 = ∞.
Proof.
intros ps₁ ps₂ Heq Hinf.
apply ps_series_order_inf_iff in Hinf.
apply ps_series_order_inf_iff.
inversion Hinf; constructor.
rewrite <- Heq, H; reflexivity.
Qed.

Theorem ps_normal_add_compat_r : ∀ ps₁ ps₂ ps₃,
  normalise_ps ps₁ ≐ normalise_ps ps₂
  → normalise_ps (ps₁ + ps₃)%ps ≐ normalise_ps (ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
remember (series_order (ps_terms ps₁) 0) as m₁ eqn:Hm₁ .
remember (series_order (ps_terms ps₂) 0) as m₂ eqn:Hm₂ .
symmetry in Hm₁, Hm₂.
destruct m₁ as [m₁| ].
 destruct m₂ as [m₂| ].
  remember (normalise_ps ps₁) as nps₁ eqn:Hps₁ .
  remember (normalise_ps ps₂) as nps₂ eqn:Hps₂ .
  symmetry in Hps₁, Hps₂.
  apply normalised_exists_adjust in Hps₁.
   apply normalised_exists_adjust in Hps₂.
    destruct Hps₁ as (n₁, (k₁, Hps₁)).
    destruct Hps₂ as (n₂, (k₂, Hps₂)).
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
    rewrite Hps₁, Hps₂.
    rewrite <- normalise_ps_add_adjust_l.
    rewrite <- normalise_ps_add_adjust_l.
    apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Heq.
    rewrite Heq; reflexivity.

    rewrite Hm₂; intros H; discriminate H.

   rewrite Hm₁; intros H; discriminate H.

  symmetry in Heq.
  eapply series_order_inf_compat in Hm₂; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

 destruct m₂ as [m₂| ].
  eapply series_order_inf_compat in Hm₁; [ idtac | eassumption ].
  rewrite Hm₁ in Hm₂; discriminate Hm₂.

  apply eq_strong_ps_adjust_zero_neg_zero in Hm₁.
  apply eq_strong_ps_adjust_zero_neg_zero in Hm₂.
  destruct Hm₁ as (n₁, (n₂, (k₁, (k₂, Hps₁)))).
  destruct Hm₂ as (n₃, (n₄, (k₃, (k₄, Hps₂)))).
  apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₁.
  apply eq_strong_ps_add_compat_r with (ps₃ := ps₃) in Hps₂.
  rewrite normalise_ps_add_adjust_l with (n := n₁) (k := k₁).
  rewrite Hps₁; symmetry.
  rewrite normalise_ps_add_adjust_l with (n := n₃) (k := k₃).
  rewrite Hps₂; symmetry.
  rewrite <- normalise_ps_add_adjust_l.
  rewrite <- normalise_ps_add_adjust_l.
  reflexivity.
Qed.

Theorem ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₁ + ps₃ = ps₂ + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
constructor.
apply ps_normal_add_compat_r.
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

End theorem_add_compat.

Global Instance ps_add_morph α (r : ring α) (K : field r) :
  Proper (eq_ps ==> eq_ps ==> eq_ps) ps_add.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
transitivity (ps_add ps₁ ps₄).
 apply ps_add_compat_l; assumption.

 apply ps_add_compat_r; assumption.
Qed.
