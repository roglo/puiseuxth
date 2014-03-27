(* Ps_add.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Misc.
Require Import Field.
Require Import Power_series.
Require Import Puiseux_series.

Set Implicit Arguments.

Definition adjust_ps α (r : ring α) n k ps :=
  {| ps_terms := series_shift r n (series_stretch r k (ps_terms ps));
     ps_valnum := ps_valnum ps * Zpos k - Z.of_nat n;
     ps_polord := ps_polord ps * k |}.

Section first_lemmas.

Variable α : Type.
Variable r : ring α.

Lemma ncrl_inf_gsxp : ∀ s n,
  null_coeff_range_length r s (S n) = ∞
  → greatest_series_x_power r s n = O.
Proof.
intros s n Hn.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power.
rewrite Hn.
reflexivity.
Qed.

Lemma greatest_series_x_power_stretch_inf : ∀ s b k,
  null_coeff_range_length r s (S b) = ∞
  → greatest_series_x_power r (series_stretch r k s) (b * Pos.to_nat k) = O.
Proof.
intros s b k Hs.
remember (greatest_series_x_power r s b) as n eqn:Hn .
symmetry in Hn.
apply greatest_series_x_power_iff in Hn.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hn |- *.
rewrite Hs in Hn.
rewrite null_coeff_range_length_stretch_succ_inf; auto.
Qed.

Lemma gcd_ps_0_m : ∀ n (ps : puiseux_series α),
  gcd_ps n O ps = Z.abs (Z.gcd (ps_valnum ps + Z.of_nat n) (' ps_polord ps)).
Proof.
intros n ps.
unfold gcd_ps.
rewrite Z.gcd_0_r; reflexivity.
Qed.

Lemma ps_canon_adjust_eq : ∀ ps n k,
  canonic_ps r ps ≐ r canonic_ps r (adjust_ps r n k ps).
Proof.
intros ps n k.
unfold canonic_ps; simpl.
rewrite null_coeff_range_length_shift.
rewrite null_coeff_range_length_stretch_0.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (null_coeff_range_length r (ps_terms ps) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
rewrite greatest_series_x_power_shift.
rewrite Nat2Z.inj_add, Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite Z.sub_add.
rewrite Nat2Z.inj_mul, positive_nat_Z.
rewrite <- Z.mul_add_distr_r.
rewrite Z.mul_comm.
remember (null_coeff_range_length r (ps_terms ps) (S m)) as p eqn:Hp .
symmetry in Hp.
remember (greatest_series_x_power r (ps_terms ps) m) as x.
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
 remember Z.mul as g; simpl; subst g.
 rewrite Nat2Z.inj_add.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 rewrite Z.sub_add_simpl_r_r.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.mul_comm.
 rewrite Z.abs_mul.
 remember Z.mul as g; simpl; subst g.
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

Theorem ps_adjust_eq : ∀ ps n k, (ps .= r adjust_ps r n k ps)%ps.
Proof.
intros ps n k.
constructor.
apply ps_canon_adjust_eq.
Qed.

End first_lemmas.

Definition adjust_series α (r : ring α) n k s :=
  series_shift r n (series_stretch r k s).

Definition ps_terms_add α (r : ring α) (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  let n₁ := Z.to_nat (v₁ - Z.min v₁ v₂) in
  let n₂ := Z.to_nat (v₂ - Z.min v₂ v₁) in
  let s₁ := adjust_series r n₁ k₁ (ps_terms ps₁) in
  let s₂ := adjust_series r n₂ k₂ (ps_terms ps₂) in
  series_add s₁ s₂.

Definition ps_valnum_add α (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  Z.min v₁ v₂.

Definition ps_add α (r : ring α) (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms := ps_terms_add r ps₁ ps₂;
     ps_valnum := ps_valnum_add ps₁ ps₂;
     ps_polord := cm ps₁ ps₂ |}.

(* I prefer this other version for addition; proved strongly equal to
   ps_add below; could be the main and only one, perhaps ? *)

Definition adjusted_ps_add α (r : ring α) ps₁ ps₂ :=
  {| ps_terms := series_add (ps_terms ps₁) (ps_terms ps₂);
     ps_valnum := ps_valnum ps₁;
     ps_polord := ps_polord ps₁ |}.

Definition adjust_ps_from α (r : ring α) ps₁ ps₂ :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_valnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_valnum ps₂ * Zpos k₂)%Z in
  adjust_ps r (Z.to_nat (v₂ - Z.min v₁ v₂)) k₂ ps₂.

Definition ps_add₂ α (r : ring α) (ps₁ ps₂ : puiseux_series α) :=
  adjusted_ps_add r (adjust_ps_from r ps₂ ps₁) (adjust_ps_from r ps₁ ps₂).

Notation "a .+ r b" := (ps_add r a b) : ps_scope.

Definition ps_opp α (r : ring α) ps :=
  {| ps_terms := (- ps_terms ps)%ser;
     ps_valnum := ps_valnum ps;
     ps_polord := ps_polord ps |}.

Notation ".- r a" := (ps_opp r a) : ps_scope.
Notation "a .- r b" := (ps_add r a (ps_opp r b)) : ps_scope.

Section theorems_add.

Variable α : Type.
Variable r : ring α.

Lemma series_stretch_add_distr : ∀ k s₁ s₂,
  (series_stretch r k (s₁ + s₂) .= r
   series_stretch r k s₁ + series_stretch r k s₂)%ser.
Proof.
intros kp s₁ s₂.
constructor; intros i; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)); [ reflexivity | idtac ].
rewrite rng_add_0_l; reflexivity.
Qed.

Lemma ps_terms_add_comm : ∀ ps₁ ps₂,
  (ps_terms_add r ps₁ ps₂ .= r ps_terms_add r ps₂ ps₁)%ser.
Proof.
intros ps₁ ps₂.
unfold ps_terms_add.
rewrite series_add_comm; reflexivity.
Qed.

Lemma cm_comm : ∀ (ps₁ ps₂ : puiseux_series α), cm ps₁ ps₂ = cm ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold cm.
apply Pos.mul_comm.
Qed.

Theorem eq_strong_ps_add_comm : ∀ ps₁ ps₂,
  (ps₁ .+ r ps₂)%ps ≐ r (ps₂ .+ r ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor; simpl.
 apply Z.min_comm.

 apply cm_comm.

 apply ps_terms_add_comm.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, (ps₁ .+ r ps₂ .= r ps₂ .+ r ps₁)%ps.
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
  (series_shift r n (s₁ + s₂) .= r
   series_shift r n s₁ + series_shift r n s₂)%ser.
Proof.
intros s₁ s₂ n.
constructor; intros i; simpl.
destruct (lt_dec i n) as [H₁| H₁]; [ idtac | reflexivity ].
rewrite rng_add_0_l; reflexivity.
Qed.

Lemma ps_terms_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps_terms_add r (ps₁ .+ r ps₂)%ps ps₃ .= r
   ps_terms_add r ps₁ (ps₂ .+ r ps₃)%ps)%ser.
Proof.
intros ps₁ ps₂ ps₃.
constructor; intros i.
unfold ps_terms_add.
remember adjust_series as g; simpl.
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
subst g; unfold adjust_series.
do 2 rewrite series_stretch_add_distr.
do 2 rewrite series_shift_add_distr.
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
simpl; rewrite rng_add_assoc; reflexivity.
Qed.

Lemma gcd_ps_add_assoc : ∀ ps₁ ps₂ ps₃ n k,
  gcd_ps n k ((ps₁ .+ r ps₂) .+ r ps₃)%ps =
  gcd_ps n k (ps₁ .+ r (ps₂ .+ r ps₃))%ps.
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
  canonic_ps r ((ps₁ .+ r ps₂) .+ r ps₃)%ps ≐ r
  canonic_ps r (ps₁ .+ r (ps₂ .+ r ps₃))%ps.
Proof.
intros ps₁ ps₂ ps₃.
unfold canonic_ps; simpl.
rewrite ps_terms_add_assoc.
remember (ps₂ .+ r ps₃)%ps as x.
remember (null_coeff_range_length r (ps_terms_add r ps₁ x) 0) as n.
subst x.
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
  (ps₁ .+ r (ps₂ .+ r ps₃) .= r (ps₁ .+ r ps₂) .+ r ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃; symmetry.
constructor.
apply ps_canon_add_assoc.
Qed.

Theorem ps_add_0_l : ∀ ps, (.0 r .+ r ps .= r ps)%ps.
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

Theorem ps_add_0_r : ∀ ps, (ps .+ r .0 r .= r ps)%ps.
Proof. intros ps; rewrite ps_add_comm; apply ps_add_0_l. Qed.

Theorem ps_add_opp_r : ∀ ps, (ps .- r ps .= r .0 r)%ps.
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
 remember Z.sub as g; simpl; subst g.
 rewrite series_stretch_series_0.
 rewrite series_shift_series_0.
 do 2 rewrite Pos.mul_1_r.
 rewrite Hv.
 rewrite Z2Nat.id; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.sub_diag; reflexivity.

 remember (Z.to_nat (Zpos v * Zpos (ps_polord ps))) as n.
 rewrite ps_canon_adjust_eq with (n := n) (k := xH); subst n.
 unfold adjust_ps.
 remember Z.sub as g; simpl; subst g.
 rewrite series_stretch_series_0.
 rewrite series_shift_series_0.
 rewrite positive_nat_Z; simpl.
 rewrite Pos.mul_1_r.
 reflexivity.
Qed.

Theorem ps_add_opp_l : ∀ ps, (.- r ps .+ r ps .= r .0 r)%ps.
Proof.
intros ps.
rewrite ps_add_comm.
apply ps_add_opp_r.
Qed.

Lemma eq_strong_ps_add_add₂ : ∀ ps₁ ps₂,
  (ps₁ .+ r ps₂)%ps ≐ r ps_add₂ r ps₁ ps₂.
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
  canonic_ps r (ps₁ .+ r ps₂)%ps ≐ r canonic_ps r (ps_add₂ r ps₁ ps₂).
Proof.
intros ps₁ ps₂.
rewrite eq_strong_ps_add_add₂; reflexivity.
Qed.

Lemma eq_ps_add_add₂ : ∀ ps₁ ps₂, (ps₁ .+ r ps₂ .= r ps_add₂ r ps₁ ps₂)%ps.
Proof.
intros ps₁ ps₂.
constructor.
apply eq_strong_ps_canon_add_add₂.
Qed.

End theorems_add.

Add Parametric Morphism α (r : ring α) : (adjusted_ps_add r)
  with signature eq_ps_strong r ==> eq_ps_strong r ==> eq_ps_strong r
  as adjusted_ps_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
unfold adjusted_ps_add.
induction Heq₁, Heq₂.
rewrite H, H0.
constructor; simpl; try reflexivity.
rewrite H1, H4; reflexivity.
Qed.

(* not used, mais bon, je les garde, on sait jamais *)

Add Parametric Morphism α (r : ring α) : (adjust_series r)
  with signature eq ==> eq ==> eq_series r ==> eq_series r
  as adjust_series_morph.
Proof.
intros n k s₁ s₂ Heq.
constructor; intros; simpl.
induction Heq.
destruct (lt_dec i n) as [H₁| H₁]; [ reflexivity | idtac ].
destruct (zerop ((i - n) mod Pos.to_nat k)); [ apply H | reflexivity ].
Qed.

Add Parametric Morphism α (r : ring α) : (ps_terms_add r)
  with signature eq_ps_strong r ==> eq_ps_strong r ==> eq_series r
  as ps_terms_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
constructor; intros i.
inversion Heq₁; subst.
inversion Heq₂; subst.
unfold ps_terms_add.
remember adjust_series as g; simpl.
unfold cm_factor.
rewrite H, H0, H2, H3; simpl.
subst g.
unfold adjust_series.
rewrite H1, H4.
reflexivity.
Qed.
