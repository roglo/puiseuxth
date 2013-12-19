(* $Id: Ps_add.v,v 2.97 2013-12-19 19:25:10 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Puiseux_series.
Require Import Nbar.
Require Import Misc.
Require Power_series.
Import Power_series.M.

Set Implicit Arguments.

Definition adjust_ps n k ps :=
  {| ps_terms := series_shift n (series_stretch k (ps_terms ps));
     ps_valnum := ps_valnum ps * Zpos k - Z.of_nat n;
     ps_polord := ps_polord ps * k |}.

Lemma ncrl_inf_gsxp : ∀ s n,
  null_coeff_range_length rng s (S n) = ∞
  → greatest_series_x_power rng s n = O.
Proof.
intros s n Hn.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power.
rewrite Hn.
reflexivity.
Qed.

Lemma greatest_series_x_power_stretch_inf : ∀ s b k,
  null_coeff_range_length rng s (S b) = ∞
  → greatest_series_x_power rng (series_stretch k s) (b * Pos.to_nat k) = O.
Proof.
intros s b k Hs.
remember (greatest_series_x_power rng s b) as n eqn:Hn .
symmetry in Hn.
apply greatest_series_x_power_iff in Hn.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hn |- *.
rewrite Hs in Hn.
rewrite null_coeff_range_length_stretch_succ_inf; auto.
Qed.

Lemma gcd_ps_0_m : ∀ n ps,
  gcd_ps n O ps = Z.abs (Z.gcd (ps_valnum ps + Z.of_nat n) (' ps_polord ps)).
Proof.
intros n ps.
unfold gcd_ps.
rewrite Z.gcd_0_r; reflexivity.
Qed.

Lemma ps_canon_adjust_eq : ∀ ps n k,
  canonic_ps ps ≐ canonic_ps (adjust_ps n k ps).
Proof.
intros ps n k.
unfold canonic_ps; simpl.
rewrite null_coeff_range_length_shift.
rewrite null_coeff_range_length_stretch_0.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (null_coeff_range_length rng (ps_terms ps) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
rewrite greatest_series_x_power_shift.
rewrite Nat2Z.inj_add, Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite Z.sub_add.
rewrite Nat2Z.inj_mul, positive_nat_Z.
rewrite <- Z.mul_add_distr_r.
rewrite Z.mul_comm.
remember (null_coeff_range_length rng (ps_terms ps) (S m)) as p eqn:Hp .
symmetry in Hp.
remember (greatest_series_x_power rng (ps_terms ps) m) as x.
pose proof (gcd_ps_is_pos m x ps) as Hgp; subst x.
destruct p as [p| ].
 erewrite greatest_series_x_power_stretch.
  unfold gcd_ps.
  remember (' k)%Z as kp; simpl.
  rewrite Nat2Z.inj_add.
  rewrite Z.sub_add_simpl_r_r.
  rewrite Nat2Z.inj_mul.
  rewrite Nat2Z.inj_mul.
  rewrite positive_nat_Z.
  rewrite <- Z.mul_add_distr_r.
  rewrite Pos2Z.inj_mul.
  rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
  subst kp.
  rewrite Z.mul_comm.
  rewrite Z.gcd_mul_mono_l_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite Z.div_mul_cancel_l.
   rewrite <- Pos2Z.inj_mul, Pos.mul_comm, Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_l.
    unfold canonify_series.
    rewrite Z2Pos.inj_mul; [ idtac | apply Pos2Z.is_pos | idtac ].
     rewrite Pos.mul_comm.
     rewrite series_shrink_shrink.
     rewrite series_left_shift_shift.
      rewrite Nat.add_sub.
      rewrite series_left_shift_stretch.
      rewrite series_shrink_stretch.
      reflexivity.

      rewrite Nat.add_comm; apply Nat.le_add_r.

     assumption.

    unfold gcd_ps in Hgp.
    intros H; rewrite H in Hgp.
    revert Hgp; apply Z.lt_irrefl.

    apply Pos2Z_ne_0.

   unfold gcd_ps in Hgp.
   intros H; rewrite H in Hgp.
   revert Hgp; apply Z.lt_irrefl.

   apply Pos2Z_ne_0.

  intros H; rewrite H in Hp; discriminate Hp.

 rewrite ncrl_inf_gsxp; [ idtac | assumption ].
 rewrite greatest_series_x_power_stretch_inf; auto.
 rewrite gcd_ps_0_m.
 rewrite gcd_ps_0_m.
 remember Z.mul as f; simpl; subst f.
 rewrite Nat2Z.inj_add.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 rewrite Z.sub_add_simpl_r_r.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.mul_comm.
 rewrite Z.abs_mul.
 remember Z.mul as f; simpl; subst f.
 rewrite Z.div_mul_cancel_l.
  rewrite <- Pos2Z.inj_mul, Pos.mul_comm, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_l.
   unfold canonify_series.
   rewrite Z2Pos.inj_mul; [ idtac | apply Pos2Z.is_pos | idtac ].
    rewrite Pos.mul_comm.
    rewrite series_shrink_shrink.
    rewrite series_left_shift_shift.
     rewrite Nat.add_sub.
     rewrite series_left_shift_stretch.
     rewrite series_shrink_stretch.
     reflexivity.

     rewrite Nat.add_comm; apply Nat.le_add_r.

    apply Z.abs_pos.
    intros H.
    apply Z.gcd_eq_0_r in H.
    revert H; apply Pos2Z_ne_0.

   intros H.
   apply -> Z.abs_0_iff in H.
   apply Z.gcd_eq_0_r in H.
   revert H; apply Pos2Z_ne_0.

   apply Pos2Z_ne_0.

  intros H.
  apply -> Z.abs_0_iff in H.
  apply Z.gcd_eq_0_r in H.
  revert H; apply Pos2Z_ne_0.

  apply Pos2Z_ne_0.
Qed.

Theorem ps_adjust_eq : ∀ ps n k, (ps = adjust_ps n k ps)%ps.
Proof.
intros ps n k.
constructor.
apply ps_canon_adjust_eq.
Qed.

Definition adjust_series n k s := series_shift n (series_stretch k s).

Definition ps_terms_add (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  let n₁ := Z.to_nat (v₁ - Z.min v₁ v₂) in
  let n₂ := Z.to_nat (v₂ - Z.min v₂ v₁) in
  let s₁ := adjust_series n₁ k₁ (ps_terms ps₁) in
  let s₂ := adjust_series n₂ k₂ (ps_terms ps₂) in
  series_add s₁ s₂.

Definition ps_valnum_add (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  Z.min v₁ v₂.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms := ps_terms_add ps₁ ps₂;
     ps_valnum := ps_valnum_add ps₁ ps₂;
     ps_polord := cm ps₁ ps₂ |}.

(* I prefer this other version for addition; proved strongly equal to
   ps_add below; could be the main and only one, perhaps ? *)

Definition adjusted_ps_add ps₁ ps₂ :=
  {| ps_terms := series_add (ps_terms ps₁) (ps_terms ps₂);
     ps_valnum := ps_valnum ps₁;
     ps_polord := ps_polord ps₁ |}.

Definition adjust_ps_from ps₁ ps₂ :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  adjust_ps (Z.to_nat (v₂ - Z.min v₁ v₂)) k₂ ps₂.

Definition ps_add₂ (ps₁ ps₂ : puiseux_series α) :=
  adjusted_ps_add (adjust_ps_from ps₂ ps₁) (adjust_ps_from ps₁ ps₂).

Notation "a + b" := (ps_add a b) : ps_scope.
(*
Notation "a ₊ b" := (ps_add₂ a b) (at level 50) : ps_scope.
*)

Lemma series_stretch_add_distr : ∀ k s₁ s₂,
  (series_stretch k (s₁ + s₂) =
   series_stretch k s₁ + series_stretch k s₂)%ser.
Proof.
intros kp s₁ s₂.
unfold series_stretch; simpl.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi).
 subst i.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nbar.mul_max_distr_r.
 remember (Nbar.max (stop s₁) (stop s₂) * fin k)%Nbar as m.
 remember (Nbar.lt_dec (fin (c * k)) m) as n; subst m.
 clear Heqn.
 destruct n as [Hlt| ]; [ idtac | reflexivity ].
 remember (Nbar.max (stop s₁) (stop s₂)) as m.
 remember (Nbar.lt_dec (fin c) m) as lt₁; subst m.
 remember (Nbar.lt_dec (fin c) (stop s₁)) as lt₂.
 remember (Nbar.lt_dec (fin c) (stop s₂)) as lt₃.
 remember (Nbar.lt_dec (fin (c * k)) (stop s₁ * fin k)) as lt₄.
 remember (Nbar.lt_dec (fin (c * k)) (stop s₂ * fin k)) as lt₅.
 clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅.
 destruct lt₁ as [Hlt₁| Hge₁].
  destruct lt₄ as [Hlt₄| Hge₄].
   destruct lt₅ as [Hlt₅| Hge₅]; [ reflexivity | idtac ].
   destruct lt₃ as [Hlt₃| ]; [ idtac | reflexivity ].
   exfalso; apply Hge₅; subst k.
   apply mul_lt_mono_positive_r; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    destruct lt₂ as [Hlt₂| Hge₂]; [ idtac | reflexivity ].
    exfalso; apply Hge₄; subst k.
    apply mul_lt_mono_positive_r; assumption.

    destruct lt₂ as [Hlt₂| Hge₂].
     exfalso; apply Hge₄; subst k.
     apply mul_lt_mono_positive_r; assumption.

     destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
     exfalso; apply Hge₅; subst k.
     apply mul_lt_mono_positive_r; assumption.

  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₁; clear Hge₁.
   apply Nbar.max_lt_iff; left; assumption.

   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₁; clear Hge₁.
    apply Nbar.max_lt_iff; right; assumption.

    destruct lt₄, lt₅; rewrite Lfield.add_0_l; reflexivity.

 remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) * fin k)) as a.
 remember (Nbar.max (stop s₁ * fin k) (stop s₂ * fin k)) as n.
 remember (Nbar.lt_dec (fin i) n) as b.
 remember (Nbar.lt_dec (fin i) (stop s₁ * fin k)) as c.
 remember (Nbar.lt_dec (fin i) (stop s₂ * fin k)) as d.
 destruct a, b, c, d; try rewrite Lfield.add_0_l; reflexivity.
Qed.

Lemma ps_terms_add_comm : ∀ ps₁ ps₂,
  (ps_terms_add ps₁ ps₂ = ps_terms_add ps₂ ps₁)%ser.
Proof.
intros ps₁ ps₂.
unfold ps_terms_add.
rewrite series_add_comm; reflexivity.
Qed.

Lemma cm_comm : ∀ ps₁ ps₂, cm ps₁ ps₂ = cm ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold cm.
apply Pos.mul_comm.
Qed.

Theorem eq_strong_ps_add_comm : ∀ ps₁ ps₂, (ps₁ + ps₂)%ps ≐ (ps₂ + ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor; simpl.
 apply Z.min_comm.

 apply cm_comm.

 apply ps_terms_add_comm.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, (ps₁ + ps₂ = ps₂ + ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor.
rewrite eq_strong_ps_add_comm; reflexivity.
Qed.

(* Experimentation for commutativity of addition for ps_add₂,
   (in order to replace one day ps_add by ps_add₂):
   provable but a bit more complicate than ps_add version;
   supposes to prove ps_valnum_add_comm, ps_polord_add_comm and
   ps_terms_add_comm; this could be a good thing, however, because
   has something pretty
Theorem eq_strong_ps_add₂_comm : ∀ ps₁ ps₂, (ps₁ ₊ ps₂)%ps ≐ (ps₂ ₊ ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor; simpl.
bbb.

Theorem ps_add₂_comm : ∀ ps₁ ps₂, (ps₁ ₊ ps₂ = ps₂ ₊ ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor.
rewrite eq_strong_ps_add₂_comm; reflexivity.
Qed.
*)

Lemma series_shift_add_distr : ∀ s₁ s₂ n,
  (series_shift n (s₁ + s₂) = series_shift n s₁ + series_shift n s₂)%ser.
Proof.
intros s₁ s₂ n.
constructor.
intros i.
unfold series_add, series_nth; simpl.
rewrite Nbar.add_max_distr_r.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) + fin n)) as c₁.
remember (Nbar.lt_dec (fin i) (stop s₁ + fin n)) as c₂.
remember (Nbar.lt_dec (fin i) (stop s₂ + fin n)) as c₃.
remember (Nbar.lt_dec (fin (i - n)) (stop s₁)) as c₄.
remember (Nbar.lt_dec (fin (i - n)) (stop s₂)) as c₅.
clear Heqc₁ Heqc₂ Heqc₃ Heqc₄ Heqc₅.
destruct (lt_dec i n) as [Hlt| Hge].
 destruct c₁, c₂, c₃; try rewrite Lfield.add_0_l; reflexivity.

 apply not_gt in Hge.
 remember (i - n)%nat as m.
 assert (m + n = i)%nat by (subst m; apply Nat.sub_add; assumption).
 subst i; clear Heqm Hge.
 destruct c₁ as [H₁| ]; [ idtac | reflexivity ].
 destruct c₂ as [H₂| H₂].
  destruct c₄ as [H₄| H₄].
   destruct c₃ as [H₃| H₃].
    destruct c₅ as [H₅| H₅]; [ reflexivity | idtac ].
    rewrite Nbar.fin_inj_add in H₃.
    apply Nbar.add_lt_mono_r in H₃; [ idtac | intros H; discriminate H ].
    contradiction.

    destruct c₅ as [c₅| c₅]; [ idtac | reflexivity ].
    rewrite Nbar.fin_inj_add in H₃.
    exfalso; apply H₃.
    apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
    assumption.

   rewrite Nbar.fin_inj_add in H₂.
   apply Nbar.add_lt_mono_r in H₂; [ idtac | intros H; discriminate H ].
   contradiction.

  destruct c₄ as [H₄| H₄].
   exfalso; apply H₂.
   rewrite Nbar.fin_inj_add.
   apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
   assumption.

   destruct c₃ as [H₃| H₃].
    destruct c₅ as [H₅| H₅]; [ reflexivity | idtac ].
    rewrite Nbar.fin_inj_add in H₃.
    apply Nbar.add_lt_mono_r in H₃; [ idtac | intros H; discriminate H ].
    contradiction.

    destruct c₅ as [c₅| c₅]; [ idtac | reflexivity ].
    exfalso; apply H₃.
    rewrite Nbar.fin_inj_add.
    apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
    assumption.
Qed.

Lemma ps_terms_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps_terms_add (ps₁ + ps₂)%ps ps₃ = ps_terms_add ps₁ (ps₂ + ps₃)%ps)%ser.
Proof.
intros ps₁ ps₂ ps₃.
constructor; intros i.
unfold ps_add; simpl.
unfold cm_factor, cm.
unfold ps_terms_add; simpl.
unfold ps_valnum_add; simpl.
unfold cm_factor, cm.
remember (ps_valnum ps₁) as v₁ eqn:Hv₁ .
remember (ps_valnum ps₂) as v₂ eqn:Hv₂ .
remember (ps_valnum ps₃) as v₃ eqn:Hv₃ .
remember (ps_polord ps₁) as c₁.
remember (ps_polord ps₂) as c₂.
remember (ps_polord ps₃) as c₃.
unfold adjust_series.
do 2 rewrite series_stretch_add_distr.
do 2 rewrite series_shift_add_distr.
rewrite series_add_assoc.
do 4 rewrite stretch_shift_series_distr.
do 4 rewrite <- series_stretch_stretch; try apply Pos2Nat_ne_0.
do 4 rewrite series_shift_shift.
do 4 rewrite <- Z2Nat_inj_mul_pos_r.
do 4 rewrite Z.mul_sub_distr_r.
do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
remember (v₁ * Zpos c₂ * Zpos c₃)%Z as vcc eqn:Hvcc .
remember (v₂ * Zpos c₁ * Zpos c₃)%Z as cvc eqn:Hcvc .
remember (v₃ * Zpos c₂ * Zpos c₁)%Z as ccv eqn:Hccv .
do 2 rewrite Z.min_assoc.
rewrite Z.mul_shuffle0, <- Hccv.
rewrite Z.mul_shuffle0, <- Hcvc.
rewrite Pos.mul_comm.
replace (c₃ * c₁)%positive with (c₁ * c₃)%positive by apply Pos.mul_comm.
do 6 rewrite Z2Nat_sub_min.
do 2 rewrite Z2Nat_sub_min1.
do 2 rewrite Z2Nat_sub_min2.
do 2 rewrite <- Z.min_assoc.
do 2 rewrite Z2Nat_sub_min.
reflexivity.
Qed.

Lemma gcd_ps_add_assoc : ∀ ps₁ ps₂ ps₃ n k,
  gcd_ps n k (ps₁ + ps₂ + ps₃)%ps = gcd_ps n k (ps₁ + (ps₂ + ps₃))%ps.
Proof.
intros ps₁ ps₂ ps₃ n k.
unfold gcd_ps; simpl.
unfold ps_valnum_add; simpl.
unfold ps_valnum_add; simpl.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite Z.min_assoc.
unfold cm_factor, cm; simpl; unfold cm; simpl.
do 6 rewrite Pos2Z.inj_mul.
do 3 rewrite Z.mul_assoc.
do 3 f_equal.
f_equal; [ idtac | rewrite Z.mul_shuffle0; reflexivity ].
f_equal; rewrite Z.mul_shuffle0; reflexivity.
Qed.

Lemma ps_canon_add_assoc : ∀ ps₁ ps₂ ps₃,
  canonic_ps (ps₁ + ps₂ + ps₃)%ps ≐ canonic_ps (ps₁ + (ps₂ + ps₃))%ps.
Proof.
intros ps₁ ps₂ ps₃.
unfold canonic_ps; simpl.
rewrite ps_terms_add_assoc.
remember
  (null_coeff_range_length rng (ps_terms_add ps₁ (ps₂ + ps₃)%ps) 0) as n.
rename Heqn into Hn.
symmetry in Hn.
destruct n as [n| ]; [ constructor; simpl | reflexivity ].
 rewrite ps_terms_add_assoc.
 rewrite gcd_ps_add_assoc.
 do 2 f_equal.
 unfold ps_valnum_add; simpl.
 unfold ps_valnum_add; simpl.
 unfold cm_factor, cm; simpl.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 f_equal; [ idtac | rewrite Z.mul_shuffle0; reflexivity ].
 f_equal; rewrite Z.mul_shuffle0; reflexivity.

 rewrite ps_terms_add_assoc.
 rewrite gcd_ps_add_assoc.
 unfold cm_factor, cm; simpl; unfold cm; simpl.
 do 4 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 reflexivity.

 rewrite ps_terms_add_assoc.
 rewrite gcd_ps_add_assoc.
 reflexivity.
Qed.

Theorem ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps₁ + (ps₂ + ps₃) = (ps₁ + ps₂) + ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃; symmetry.
constructor.
apply ps_canon_add_assoc.
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
unfold ps_valnum_add; simpl.
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
remember (Z.to_nat (ps_valnum ps)) as n eqn:Hn .
rewrite ps_canon_adjust_eq with (n := n) (k := xH) in |- * at 1.
subst n.
unfold adjust_ps; simpl.
rewrite Pos.mul_1_r, Z.mul_1_r.
rewrite series_stretch_1.
rewrite Z2Nat_id_max.
rewrite <- Z.sub_min_distr_l.
rewrite Z.sub_0_r, Z.sub_diag, Z.min_comm.
reflexivity.
Qed.

Theorem ps_add_0_r : ∀ ps, (ps + 0 = ps)%ps.
Proof. intros ps; rewrite ps_add_comm; apply ps_add_0_l. Qed.

Definition ps_opp ps :=
  {| ps_terms := series_opp (ps_terms ps);
     ps_valnum := ps_valnum ps;
     ps_polord := ps_polord ps |}.

Notation "- a" := (ps_opp a) : ps_scope.
Notation "a - b" := (ps_add a (ps_opp b)) : ps_scope.

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
unfold ps_valnum_add; simpl.
unfold cm_factor, cm; simpl.
rewrite Z.min_id.
symmetry.
remember (ps_polord ps * ps_polord ps)%positive as k eqn:Hk .
rewrite ps_canon_adjust_eq with (n := O) (k := k); subst k.
unfold adjust_ps; simpl.
rewrite series_shift_0.
rewrite series_stretch_series_0.
remember (ps_valnum ps) as v eqn:Hv .
symmetry in Hv.
destruct v as [| v| v].
 reflexivity.

 symmetry.
 remember (Z.to_nat (ps_valnum ps * Zpos (ps_polord ps))) as n.
 rewrite ps_canon_adjust_eq with (n := n) (k := xH); subst n.
 unfold adjust_ps.
 remember Z.sub as f; simpl; subst f.
 rewrite series_stretch_series_0.
 rewrite series_shift_series_0.
 do 2 rewrite Pos.mul_1_r.
 rewrite Hv.
 rewrite Z2Nat.id; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.sub_diag; reflexivity.

 remember (Z.to_nat (Zpos v * Zpos (ps_polord ps))) as n.
 rewrite ps_canon_adjust_eq with (n := n) (k := xH); subst n.
 unfold adjust_ps.
 remember Z.sub as f; simpl; subst f.
 rewrite series_stretch_series_0.
 rewrite series_shift_series_0.
 rewrite positive_nat_Z; simpl.
 rewrite Pos.mul_1_r.
 reflexivity.
Qed.

Theorem ps_add_opp_l : ∀ ps, (- ps + ps = 0)%ps.
Proof.
intros ps.
rewrite ps_add_comm.
apply ps_add_opp_r.
Qed.

Lemma eq_strong_ps_add_add₂ : ∀ ps₁ ps₂,
  eq_ps_strong (ps_add ps₁ ps₂) (ps_add₂ ps₁ ps₂).
Proof.
intros ps₁ ps₂.
constructor; [ simpl | reflexivity | simpl ].
 unfold ps_valnum_add.
 rewrite Z2Nat.id.
  rewrite Z.sub_sub_distr.
  rewrite Z.sub_diag; simpl.
  apply Z.min_comm.

  rewrite <- Z.sub_max_distr_l.
  rewrite Z.sub_diag.
  apply Z.le_max_r.

 unfold ps_terms_add.
 unfold adjust_series.
 remember (ps_valnum ps₂ * Zpos (cm_factor ps₂ ps₁))%Z as vc₂₁.
 remember (ps_valnum ps₁ * Zpos (cm_factor ps₁ ps₂))%Z as vc₁₂.
 remember (Z.min vc₁₂ vc₂₁) as m eqn:Hm .
 rewrite Z.min_comm, <- Hm.
 reflexivity.
Qed.

Lemma eq_strong_ps_canon_add_add₂ : ∀ ps₁ ps₂,
  canonic_ps (ps₁ + ps₂)%ps ≐ canonic_ps (ps_add₂ ps₁ ps₂).
Proof.
intros ps₁ ps₂.
rewrite eq_strong_ps_add_add₂; reflexivity.
Qed.

Lemma eq_ps_add_add₂ : ∀ ps₁ ps₂, (ps₁ + ps₂ = ps_add₂ ps₁ ps₂)%ps.
Proof.
intros ps₁ ps₂.
constructor.
apply eq_strong_ps_canon_add_add₂.
Qed.

Add Parametric Morphism : adjusted_ps_add
  with signature eq_ps_strong ==> eq_ps_strong ==> eq_ps_strong
  as adjusted_ps_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
unfold adjusted_ps_add.
induction Heq₁, Heq₂.
rewrite H, H0.
constructor; simpl; try reflexivity.
rewrite H1, H4; reflexivity.
Qed.

(* pas utilisés, mais bon, je les garde, on sait jamais *)

Add Parametric Morphism : adjust_series
with signature eq ==> eq ==> eq_series ==> eq_series
as adjust_series_morph.
Proof.
(* à nettoyer *)
intros n k s₁ s₂ Heq.
constructor; intros.
induction Heq.
unfold series_nth.
simpl.
destruct (Nbar.lt_dec (fin i) (stop s₁ * fin (Pos.to_nat k) + fin n))
 as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop s₂ * fin (Pos.to_nat k) + fin n))
  as [H₂| H₂].
  destruct (lt_dec i n) as [H₃| H₃]; [ reflexivity | idtac ].
  destruct (zerop ((i - n) mod Pos.to_nat k)) as [H₄| H₄];
   [ idtac | reflexivity ].
  apply H.

  destruct (lt_dec i n) as [H₃| H₃].
   reflexivity.

   destruct (zerop ((i - n) mod Pos.to_nat k)) as [H₄| H₄];
    [ idtac | reflexivity ].
   rewrite H.
   unfold series_nth.
   destruct (Nbar.lt_dec (fin ((i - n) / Pos.to_nat k)) (stop s₂))
    as [H₅| H₅]; [ idtac | reflexivity ].
   exfalso; apply H₂.
   apply Nbar.lt_sub_lt_add_r; [ intros I; discriminate I | simpl ].
   apply Nat.mod_divides in H₄; auto.
   destruct H₄ as (c, H₄).
   rewrite Nat.mul_comm in H₄.
   rewrite H₄ in H₅ |- *.
   rewrite Nat.div_mul in H₅; auto.
   rewrite Nbar.fin_inj_mul.
   apply Nbar.mul_lt_mono_pos_r.
    apply Nbar.lt_fin, Pos2Nat.is_pos.

    intros I; discriminate I.

    intros I; discriminate I.

    assumption.

 destruct (Nbar.lt_dec (fin i) (stop s₂ * fin (Pos.to_nat k) + fin n))
  as [H₂| H₂].
  destruct (lt_dec i n) as [H₃| H₃]; [ reflexivity | idtac ].
  destruct (zerop ((i - n) mod Pos.to_nat k)) as [H₄| H₄];
   [ idtac | reflexivity ].
  symmetry.
  rewrite <- H.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin ((i - n) / Pos.to_nat k)) (stop s₁)) as [H₅| H₅];
   [ idtac | reflexivity ].
  exfalso; apply H₁.
  apply Nbar.lt_sub_lt_add_r; [ intros I; discriminate I | simpl ].
  apply Nat.mod_divides in H₄; auto.
  destruct H₄ as (c, H₄).
  rewrite Nat.mul_comm in H₄.
  rewrite H₄ in H₅ |- *.
  rewrite Nat.div_mul in H₅; auto.
  rewrite Nbar.fin_inj_mul.
  apply Nbar.mul_lt_mono_pos_r.
   apply Nbar.lt_fin, Pos2Nat.is_pos.

   intros I; discriminate I.

   intros I; discriminate I.

   assumption.

  reflexivity.
Qed.

Add Parametric Morphism : ps_terms_add
  with signature eq_ps_strong ==> eq_ps_strong ==> eq_series
  as ps_terms_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
constructor; intros i.
inversion_clear Heq₁.
inversion_clear Heq₂.
unfold series_nth; simpl.
unfold cm_factor.
rewrite H, H0, H2, H3; simpl.
remember (ps_polord ps₃) as c₃.
remember (ps_polord ps₄) as c₄.
remember (ps_valnum ps₃) as v₃.
remember (ps_valnum ps₄) as v₄.
remember (Z.to_nat (v₃ * ' c₄ - Z.min (v₃ * ' c₄) (v₄ * ' c₃))) as x.
remember (Z.to_nat (v₄ * ' c₃ - Z.min (v₄ * ' c₃) (v₃ * ' c₄))) as y.
remember (stop (ps_terms ps₁) * fin (Pos.to_nat c₄) + fin x)%Nbar as x₁.
remember (stop (ps_terms ps₂) * fin (Pos.to_nat c₃) + fin y)%Nbar as y₁.
remember (stop (ps_terms ps₃) * fin (Pos.to_nat c₄) + fin x)%Nbar as x₂.
remember (stop (ps_terms ps₄) * fin (Pos.to_nat c₃) + fin y)%Nbar as y₂.
destruct (Nbar.lt_dec (fin i) (Nbar.max x₁ y₁)) as [H₁| H₁].
 rewrite H1, H4.
 destruct (Nbar.lt_dec (fin i) (Nbar.max x₂ y₂)) as [H₂| H₂].
  reflexivity.

  unfold adjust_series.
  unfold series_nth; simpl.
  rewrite <- Heqx₂, <- Heqy₂.
  destruct (Nbar.lt_dec (fin i) x₂) as [H₃| H₃].
   exfalso; apply H₂.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite Lfield.add_0_l.
   destruct (Nbar.lt_dec (fin i) y₂) as [H₄| H₄].
    exfalso; apply H₂.
    apply Nbar.max_lt_iff; right; assumption.

    reflexivity.

 destruct (Nbar.lt_dec (fin i) (Nbar.max x₂ y₂)) as [H₂| H₂].
  rewrite <- H1, <- H4.
  unfold adjust_series.
  unfold series_nth; simpl.
  rewrite <- Heqx₁, <- Heqy₁.
  destruct (Nbar.lt_dec (fin i) x₁) as [H₃| H₃].
   exfalso; apply H₁.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite Lfield.add_0_l.
   destruct (Nbar.lt_dec (fin i) y₁) as [H₄| H₄].
    exfalso; apply H₁.
    apply Nbar.max_lt_iff; right; assumption.

    reflexivity.

  reflexivity.
Qed.
