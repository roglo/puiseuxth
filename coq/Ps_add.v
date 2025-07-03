(* Ps_add.v *)

From Stdlib Require Import Utf8 Arith.

Require Import A_PosArith A_ZArith.
Require Import NbarM.
Require Import Misc.
Require Import Field2.
Require Import Power_series.
Require Import Puiseux_series.

Set Implicit Arguments.

Definition adjust_ps α {R : ring α} n k ps :=
  {| ps_terms := series_shift n (series_stretch k (ps_terms ps));
     ps_ordnum := ps_ordnum ps * z_pos k - Z.of_nat n;
     ps_polydo := ps_polydo ps * k |}.

Section first_theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem ncrl_inf_gsxp : ∀ s n,
  series_order s (S n) = ∞
  → greatest_series_x_power K s n = O.
Proof.
intros s n Hn.
apply greatest_series_x_power_iff.
rewrite Hn; reflexivity.
Qed.

Theorem greatest_series_x_power_stretch_inf : ∀ s b k,
  series_order s (S b) = ∞
  → greatest_series_x_power K (series_stretch k s) (b * Pos.to_nat k) = O.
Proof.
intros s b k Hs.
remember (greatest_series_x_power K s b) as n eqn:Hn .
symmetry in Hn.
apply greatest_series_x_power_iff in Hn.
apply greatest_series_x_power_iff.
rewrite Hs in Hn.
rewrite series_order_stretch_succ_inf; auto.
Qed.

Theorem gcd_ps_0_m : ∀ n (ps : puiseux_series α),
  gcd_ps n O ps =
    Z.abs (Z.gcd (ps_ordnum ps + Z.of_nat n) (z_pos (ps_polydo ps))).
Proof.
intros n ps.
unfold gcd_ps.
apply Z.gcd_0_r.
Qed.

Theorem ps_normal_adjust_eq : ∀ ps n k,
  normalise_ps ps ≐ normalise_ps (adjust_ps n k ps).
Proof.
intros ps n k.
unfold normalise_ps; simpl.
rewrite series_order_shift.
rewrite series_order_stretch_0.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (series_order (ps_terms ps) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
rewrite greatest_series_x_power_shift.
rewrite Nat2Z.inj_add, Z.add_assoc.
rewrite Z.add_add_swap.
rewrite Z.sub_add.
rewrite Nat2Z.inj_mul, Z.pos_nat.
rewrite <- Z.mul_add_distr_r.
rewrite Z.mul_comm.
remember (series_order (ps_terms ps) (S m)) as p eqn:Hp .
symmetry in Hp.
remember (greatest_series_x_power K (ps_terms ps) m) as x.
pose proof (gcd_ps_is_pos m x ps) as Hgp; subst x.
destruct p as [p| ]. {
  erewrite greatest_series_x_power_stretch. {
    unfold gcd_ps.
    remember (z_val true k)%Z as kp; simpl.
    rewrite Nat2Z.inj_add.
    rewrite (Z.add_comm _ (Z.of_nat n)), Z.add_assoc, Z.sub_add.
    rewrite Nat2Z.inj_mul.
    rewrite Nat2Z.inj_mul.
    rewrite Z.pos_nat.
    rewrite <- Z.mul_add_distr_r.
    rewrite Pos2Z.inj_mul.
    rewrite Z.gcd_mul_mono_r_nonneg; [ | easy ].
    subst kp.
    rewrite Z.mul_comm.
    rewrite Z.gcd_mul_mono_l_nonneg; [ idtac | easy ].
    rewrite Z.div_mul_cancel_l; [ | easy | ]. {
      rewrite <- Pos2Z.inj_mul, Pos.mul_comm, Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_l; [ | easy | ]. {
        unfold normalise_series.
        rewrite Z2Pos.inj_mul; [ | easy | easy ].
        rewrite Pos.mul_comm.
        rewrite series_shrink_shrink.
        rewrite series_left_shift_shift. {
          rewrite Nat.add_sub.
          rewrite series_left_shift_stretch.
          rewrite series_shrink_stretch.
          reflexivity.
        }
        rewrite Nat.add_comm; apply Nat.le_add_r.
      }
      intros H.
      apply Z.gcd_eq_0_l in H.
      apply Z.gcd_eq_0_r in H.
      easy.
    }
    intros H.
    apply Z.gcd_eq_0_l in H.
    apply Z.gcd_eq_0_r in H.
    easy.
  }
  intros H; rewrite H in Hp; discriminate Hp.
}
rewrite ncrl_inf_gsxp; [ idtac | assumption ].
rewrite greatest_series_x_power_stretch_inf; auto.
rewrite gcd_ps_0_m.
rewrite gcd_ps_0_m.
remember Z.mul as g; simpl; subst g.
rewrite Nat2Z.inj_add.
rewrite Nat2Z.inj_mul.
rewrite Z.pos_nat.
rewrite (Z.add_comm _ (Z.of_nat n)), Z.add_assoc, Z.sub_add.
rewrite <- Z.mul_add_distr_r.
rewrite Pos2Z.inj_mul.
rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | easy ].
rewrite Z.mul_comm.
rewrite Z.abs_mul.
remember Z.mul as g; simpl; subst g.
rewrite Z.pos_nat.
rewrite Z.div_mul_cancel_l; [ | easy | ]. {
  rewrite <- Pos2Z.inj_mul, Pos.mul_comm, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_l; [ | easy | ]. {
    unfold normalise_series.
    rewrite Z2Pos.inj_mul; [ idtac | easy | idtac ]. {
      rewrite Pos.mul_comm.
      rewrite series_shrink_shrink.
      rewrite series_left_shift_shift. {
        rewrite Nat.add_sub.
        rewrite series_left_shift_stretch.
        rewrite series_shrink_stretch.
        reflexivity.
      }
      rewrite Nat.add_comm; apply Nat.le_add_r.
    }
    apply Z.abs_pos.
    intros H.
    apply Z.gcd_eq_0_r in H.
    revert H; apply Pos2Z_ne_0.
  }
  intros H.
  apply -> Z.abs_0_iff in H.
  apply Z.gcd_eq_0_r in H.
  easy.
}
intros H.
apply -> Z.abs_0_iff in H.
apply Z.gcd_eq_0_r in H.
easy.
Qed.

Theorem ps_adjust_eq : ∀ ps n k, (ps = adjust_ps n k ps)%ps.
Proof.
intros ps n k.
constructor.
apply ps_normal_adjust_eq.
Qed.

End first_theorems.

Definition adjust_series α {R : ring α} n k s :=
  series_shift n (series_stretch k s).

Definition ps_terms_add α {R : ring α} (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_ordnum ps₁ * z_pos k₁)%Z in
  let v₂ := (ps_ordnum ps₂ * z_pos k₂)%Z in
  let n₁ := Z.to_nat (v₁ - Z.min v₁ v₂) in
  let n₂ := Z.to_nat (v₂ - Z.min v₂ v₁) in
  let s₁ := adjust_series n₁ k₁ (ps_terms ps₁) in
  let s₂ := adjust_series n₂ k₂ (ps_terms ps₂) in
  series_add s₁ s₂.

Definition ps_ordnum_add α (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_ordnum ps₁ * z_pos k₁)%Z in
  let v₂ := (ps_ordnum ps₂ * z_pos k₂)%Z in
  Z.min v₁ v₂.

Definition ps_add {α} {r : ring α} (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms := ps_terms_add ps₁ ps₂;
     ps_ordnum := ps_ordnum_add ps₁ ps₂;
     ps_polydo := cm ps₁ ps₂ |}.

(* I prefer this other version for addition; proved strongly equal to
   ps_add below; could be the main and only one, perhaps ? *)

Definition adjusted_ps_add α {R : ring α} ps₁ ps₂ :=
  {| ps_terms := series_add (ps_terms ps₁) (ps_terms ps₂);
     ps_ordnum := ps_ordnum ps₁;
     ps_polydo := ps_polydo ps₁ |}.

Definition adjust_ps_from α {R : ring α} (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := ps_polydo ps₂ in
  let k₂ := ps_polydo ps₁ in
  let v₁ := (ps_ordnum ps₁ * z_pos k₁)%Z in
  let v₂ := (ps_ordnum ps₂ * z_pos k₂)%Z in
  adjust_ps (Z.to_nat (v₂ - Z.min v₁ v₂)) k₂ ps₂.

Definition ps_add₂ {α} {r : ring α} (ps₁ ps₂ : puiseux_series α) :=
  adjusted_ps_add (adjust_ps_from ps₂ ps₁) (adjust_ps_from ps₁ ps₂).

Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ++ b" := (ps_add₂ a b) : ps_scope.

Definition ps_opp {α} {r : ring α} ps :=
  {| ps_terms := (- ps_terms ps)%ser;
     ps_ordnum := ps_ordnum ps;
     ps_polydo := ps_polydo ps |}.

Notation "- a" := (ps_opp a) : ps_scope.
Notation "a - b" := (ps_add a (ps_opp b)) : ps_scope.

Section theorems_add.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem series_stretch_add_distr : ∀ k s₁ s₂,
  (series_stretch k (s₁ + s₂) =
   series_stretch k s₁ + series_stretch k s₂)%ser.
Proof.
intros kp s₁ s₂.
constructor; intros i; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by now subst k.
destruct (zerop (i mod k)); [ reflexivity | idtac ].
rewrite rng_add_0_l; reflexivity.
Qed.

Theorem ps_terms_add_comm : ∀ ps₁ ps₂,
  (ps_terms_add ps₁ ps₂ = ps_terms_add ps₂ ps₁)%ser.
Proof.
intros ps₁ ps₂.
unfold ps_terms_add.
rewrite series_add_comm; reflexivity.
Qed.

Theorem eq_strong_ps_add_comm : ∀ ps₁ ps₂,
  (ps₁ + ps₂)%ps ≐ (ps₂ + ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor; simpl. {
  apply Z.min_comm.
} {
  apply Pos.mul_comm.
} {
  apply ps_terms_add_comm.
}
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, (ps₁ + ps₂ = ps₂ + ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor.
rewrite eq_strong_ps_add_comm; reflexivity.
Qed.

Theorem series_shift_add_distr : ∀ s₁ s₂ n,
  (series_shift n (s₁ + s₂) =
   series_shift n s₁ + series_shift n s₂)%ser.
Proof.
intros s₁ s₂ n.
constructor; intros i; simpl.
destruct (lt_dec i n) as [H₁| H₁]; [ idtac | reflexivity ].
rewrite rng_add_0_l; reflexivity.
Qed.

Theorem ps_terms_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps_terms_add (ps₁ + ps₂)%ps ps₃ =
   ps_terms_add ps₁ (ps₂ + ps₃)%ps)%ser.
Proof.
intros ps₁ ps₂ ps₃.
constructor; intros i.
unfold ps_terms_add.
remember adjust_series as g; simpl.
unfold cm_factor, cm.
unfold ps_terms_add; simpl.
unfold ps_ordnum_add; simpl.
unfold cm_factor, cm.
remember (ps_ordnum ps₁) as v₁ eqn:Hv₁ .
remember (ps_ordnum ps₂) as v₂ eqn:Hv₂ .
remember (ps_ordnum ps₃) as v₃ eqn:Hv₃ .
remember (ps_polydo ps₁) as c₁.
remember (ps_polydo ps₂) as c₂.
remember (ps_polydo ps₃) as c₃.
subst g; unfold adjust_series.
do 2 rewrite series_stretch_add_distr.
do 2 rewrite series_shift_add_distr.
do 4 rewrite stretch_shift_series_distr.
do 4 rewrite <- series_stretch_stretch; try apply Pos2Nat_ne_0.
do 4 rewrite series_shift_shift.
do 4 rewrite <- Z2Nat_inj_mul_pos_r.
do 4 rewrite Z.mul_sub_distr_r.
do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
progress unfold Z.of_pos.
remember (v₁ * z_pos c₂ * z_pos c₃)%Z as vcc eqn:Hvcc .
remember (v₂ * z_pos c₁ * z_pos c₃)%Z as cvc eqn:Hcvc .
remember (v₃ * z_pos c₂ * z_pos c₁)%Z as ccv eqn:Hccv .
do 2 rewrite Z.min_assoc.
rewrite Z.mul_mul_swap, <- Hccv.
rewrite (Z.mul_mul_swap v₂), <- Hcvc.
rewrite Pos.mul_comm.
rewrite (Pos.mul_comm c₃ c₁).
do 6 rewrite Z2Nat_sub_min.
do 2 rewrite Z2Nat_sub_min1.
do 2 rewrite Z2Nat_sub_min2.
do 2 rewrite <- Z.min_assoc.
do 2 rewrite Z2Nat_sub_min.
simpl; rewrite rng_add_assoc; reflexivity.
Qed.

Theorem gcd_ps_add_assoc : ∀ ps₁ ps₂ ps₃ n k,
  gcd_ps n k ((ps₁ + ps₂) + ps₃)%ps =
  gcd_ps n k (ps₁ + (ps₂ + ps₃))%ps.
Proof.
intros ps₁ ps₂ ps₃ n k.
unfold gcd_ps; simpl.
unfold ps_ordnum_add; simpl.
unfold ps_ordnum_add; simpl.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
rewrite Z.min_assoc.
unfold cm_factor, cm; simpl; unfold cm; simpl.
do 6 rewrite Pos2Z.inj_mul.
do 3 rewrite Z.mul_assoc.
do 3 f_equal.
f_equal; [ idtac | rewrite Z.mul_mul_swap; reflexivity ].
f_equal; rewrite Z.mul_mul_swap; reflexivity.
Qed.

Theorem ps_normal_add_assoc : ∀ ps₁ ps₂ ps₃,
  normalise_ps ((ps₁ + ps₂) + ps₃)%ps ≐
  normalise_ps (ps₁ + (ps₂ + ps₃))%ps.
Proof.
intros ps₁ ps₂ ps₃.
unfold normalise_ps; simpl.
rewrite ps_terms_add_assoc.
remember (ps₂ + ps₃)%ps as x.
remember (series_order (ps_terms_add ps₁ x) 0) as n.
subst x.
rename Heqn into Hn.
symmetry in Hn.
destruct n as [n| ]; [ constructor; simpl | reflexivity ]. {
  rewrite ps_terms_add_assoc.
  rewrite gcd_ps_add_assoc.
  do 2 f_equal.
  unfold ps_ordnum_add; simpl.
  unfold ps_ordnum_add; simpl.
  unfold cm_factor, cm; simpl.
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | easy ].
  rewrite Z.min_assoc.
  do 2 rewrite Pos2Z.inj_mul.
  do 2 rewrite Z.mul_assoc.
  f_equal; [ idtac | rewrite Z.mul_mul_swap; reflexivity ].
  f_equal; rewrite Z.mul_mul_swap; reflexivity.
} {
  rewrite ps_terms_add_assoc.
  rewrite gcd_ps_add_assoc.
  unfold cm_factor, cm; simpl; unfold cm; simpl.
  do 4 rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  reflexivity.
} {
  rewrite ps_terms_add_assoc.
  rewrite gcd_ps_add_assoc.
  reflexivity.
}
Qed.

Theorem ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps₁ + (ps₂ + ps₃) = (ps₁ + ps₂) + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃; symmetry.
constructor.
apply ps_normal_add_assoc.
Qed.

Theorem ps_add_0_l : ∀ ps, (0 + ps = ps)%ps.
Proof.
intros ps.
unfold ps_add; simpl.
constructor.
unfold ps_terms_add; simpl.
rewrite Z.mul_1_r.
unfold cm_factor.
unfold cm; simpl.
unfold ps_ordnum_add; simpl.
rewrite Z.mul_1_r.
unfold adjust_series.
rewrite series_stretch_series_0.
rewrite series_stretch_1.
rewrite series_shift_series_0.
rewrite series_add_0_l.
rewrite <- Z2Nat_sub_min2.
rewrite Z.min_id, Z.sub_0_r.
rewrite Z.sub_diag, Nat.add_0_r.
symmetry.
remember (Z.to_nat (ps_ordnum ps)) as n eqn:Hn .
rewrite ps_normal_adjust_eq with (n := n) (k := 1%pos) in |- * at 1.
subst n.
unfold adjust_ps; simpl.
rewrite Pos.mul_1_r, Z.mul_1_r.
rewrite series_stretch_1.
rewrite Z2Nat_id_max.
rewrite <- Z.sub_min_distr_l.
rewrite Z.sub_0_r, Z.sub_diag, Z.min_comm.
rewrite Pos.mul_1_l.
reflexivity.
Qed.

Theorem ps_add_0_r : ∀ ps, (ps + 0 = ps)%ps.
Proof. intros ps; rewrite ps_add_comm; apply ps_add_0_l. Qed.

Theorem ps_add_opp_r : ∀ ps, (ps - ps = 0)%ps.
Proof.
intros ps.
unfold ps_zero.
unfold ps_add; simpl.
constructor; simpl.
unfold ps_opp; simpl.
unfold ps_terms_add; simpl.
unfold cm_factor; simpl.
rewrite Z.min_id.
rewrite Z.sub_diag; simpl.
unfold adjust_series.
do 2 rewrite series_shift_0.
rewrite <- series_stretch_add_distr.
rewrite series_add_opp_r.
rewrite series_stretch_series_0.
unfold ps_ordnum_add; simpl.
unfold cm_factor, cm; simpl.
rewrite Z.min_id.
symmetry.
remember (ps_polydo ps * ps_polydo ps)%pos as k eqn:Hk .
rewrite ps_normal_adjust_eq with (n := O) (k := k); subst k.
unfold adjust_ps; simpl.
rewrite series_shift_0.
rewrite series_stretch_series_0.
remember (ps_ordnum ps) as v eqn:Hv .
symmetry in Hv.
destruct v as [| sv vv]; [ now cbn; rewrite Pos.mul_1_l | ].
rewrite Pos.mul_1_l.
destruct sv. {
  symmetry.
  remember (Z.to_nat (ps_ordnum ps * z_pos (ps_polydo ps))) as n.
  rewrite ps_normal_adjust_eq with (n := n) (k := 1%pos); subst n.
  unfold adjust_ps.
  remember Z.sub as g; simpl; subst g.
  rewrite series_stretch_series_0.
  rewrite series_shift_series_0.
  do 2 rewrite Pos.mul_1_r.
  rewrite Hv.
  rewrite Z2Nat.id; [ idtac | easy ].
  rewrite Z.sub_diag; reflexivity.
} {
  remember (Z.to_nat (z_pos vv * z_pos (ps_polydo ps))) as n.
  rewrite ps_normal_adjust_eq with (n := n) (k := 1%pos); subst n.
  unfold adjust_ps.
  remember Z.sub as g; simpl; subst g.
  rewrite series_stretch_series_0.
  rewrite series_shift_series_0.
  rewrite Z.pos_nat; simpl.
  rewrite Pos.mul_1_r.
  reflexivity.
}
Qed.

Theorem ps_add_opp_l : ∀ ps, (- ps + ps = 0)%ps.
Proof.
intros ps.
rewrite ps_add_comm.
apply ps_add_opp_r.
Qed.

Theorem eq_strong_ps_add_add₂ : ∀ ps₁ ps₂,
  (ps₁ + ps₂)%ps ≐ ps_add₂ ps₁ ps₂.
Proof.
intros ps₁ ps₂.
constructor; [ simpl | reflexivity | simpl ]. {
  unfold ps_ordnum_add.
  rewrite Z2Nat.id. {
    rewrite Z.sub_sub_distr.
    rewrite Z.sub_diag; simpl.
    apply Z.min_comm.
  }
...
  rewrite <- Z.sub_max_distr_l.
  rewrite Z.sub_diag.
  apply Z.le_max_r.
}
unfold ps_terms_add.
unfold adjust_series.
unfold cm_factor.
remember (ps_ordnum ps₂ * Zpos (ps_polydo ps₁))%Z as vc₂₁.
remember (ps_ordnum ps₁ * Zpos (ps_polydo ps₂))%Z as vc₁₂.
remember (Z.min vc₁₂ vc₂₁) as m eqn:Hm .
rewrite Z.min_comm, <- Hm.
reflexivity.
Qed.

Theorem eq_strong_ps_normal_add_add₂ : ∀ ps₁ ps₂,
  normalise_ps (ps₁ + ps₂)%ps ≐ normalise_ps (ps_add₂ ps₁ ps₂).
Proof.
intros ps₁ ps₂.
rewrite eq_strong_ps_add_add₂; reflexivity.
Qed.

Theorem eq_ps_add_add₂ : ∀ ps₁ ps₂, (ps₁ + ps₂ = ps_add₂ ps₁ ps₂)%ps.
Proof.
intros ps₁ ps₂.
constructor.
apply eq_strong_ps_normal_add_add₂.
Qed.

Theorem ps_monom_add : ∀ a b n,
  (ps_monom a n + ps_monom b n = ps_monom (a + b)%K n)%ps.
Proof.
intros a b n.
symmetry.
unfold ps_add; simpl.
unfold cm; simpl.
unfold ps_ordnum_add; simpl.
unfold ps_terms_add; simpl.
rewrite ps_adjust_eq with (n := O) (k := Qden n).
unfold adjust_ps; simpl.
rewrite Z.sub_0_r.
rewrite Z.min_id.
apply mkps_morphism; try reflexivity.
rewrite series_shift_0.
rewrite Z.sub_diag; simpl.
unfold adjust_series; simpl.
do 2 rewrite series_shift_0.
constructor; intros i; simpl.
destruct (zerop (i mod Pos.to_nat (Qden n))) as [H₁| H₁]. {
  apply Nat.Div0.mod_divides in H₁.
  destruct H₁ as (c, Hc).
  rewrite Nat.mul_comm in Hc; rewrite Hc.
  rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
  destruct c; [ reflexivity | simpl ].
  rewrite rng_add_0_l; reflexivity.
}
rewrite rng_add_0_l; reflexivity.
Qed.

End theorems_add.

Global Instance adjusted_ps_add_morph α (R : ring α) :
  Proper (eq_ps_strong ==> eq_ps_strong ==> eq_ps_strong)
    (@adjusted_ps_add _ R).
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
unfold adjusted_ps_add.
induction Heq₁, Heq₂.
rewrite H, H0.
constructor; simpl; try reflexivity.
rewrite H1, H4; reflexivity.
Qed.

Global Instance adjust_series_morph α (R : ring α) :
  Proper (eq ==> eq ==> eq_series ==> eq_series)
    (@adjust_series _ R).
Proof.
intros n n' Hn k k' Hk s₁ s₂ Heq.
subst n' k'.
constructor; intros; simpl.
induction Heq.
destruct (lt_dec i n) as [H₁| H₁]; [ reflexivity | idtac ].
destruct (zerop ((i - n) mod Pos.to_nat k)); [ apply H | reflexivity ].
Qed.
