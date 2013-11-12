(* $Id: Ps_add.v,v 2.27 2013-11-12 11:00:27 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Series.
Require Import Puiseux_series.
Require Import Nbar.
Require Import Misc.

Set Implicit Arguments.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

(*
Definition cm ps₁ ps₂ := Plcm (nz_comden ps₁) (nz_comden ps₂).
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (nz_comden ps₁) (nz_comden ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (nz_comden ps₁))%nat.
*)
Definition cm (nz₁ nz₂ : nz_ps α) :=
  (nz_comden nz₁ * nz_comden nz₂)%positive.
Definition cm_factor α (nz₁ nz₂ : nz_ps α) :=
  nz_comden nz₂.
(**)

(* for a possible redefinition of ps_add, or perhaps to change a
   representation for another to manage to make proofs... *)
Definition adjust_nz n k nz :=
  {| nz_terms := series_shift fld n (series_stretch fld k (nz_terms nz));
     nz_valnum := nz_valnum nz * Zpos k - Z.of_nat n;
     nz_comden := nz_comden nz * k |}.

Lemma nz_adjust_eq : ∀ nz n k,
  normalise_nz fld nz ≐ normalise_nz fld (adjust_nz n k nz).
Proof.
intros nz n k.
unfold normalise_nz; simpl.
rewrite null_coeff_range_length_shift.
rewrite null_coeff_range_length_stretch_0.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (null_coeff_range_length fld (nz_terms nz) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite greatest_series_x_power_shift.
 rewrite Nat2Z.inj_add, Z.add_assoc.
 rewrite Z.add_shuffle0.
 rewrite Z.sub_add.
 rewrite Nat2Z.inj_mul, positive_nat_Z.
 rewrite <- Z.mul_add_distr_r.
 rewrite Z.mul_comm.
 erewrite greatest_series_x_power_stretch.
 unfold gcd_nz.
 remember (' k)%Z as kp.
 simpl.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Pos.mul_comm.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r_nonneg; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.mul_comm.
 subst kp.
 rewrite Z.div_mul_cancel_r; [ reflexivity | idtac | apply Pos2Z_ne_0 ].
 intros H₁.
 apply Z.gcd_eq_0_r in H₁.
 revert H₁; apply Pos2Z_ne_0.

 rewrite greatest_series_x_power_shift.
 rewrite greatest_series_x_power_stretch.
 unfold gcd_nz; simpl.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Pos.mul_comm.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Z.div_mul_cancel_r; auto; [ idtac | apply Pos2Z_ne_0 ].
 intros H₁.
 apply Z.gcd_eq_0_r in H₁.
 revert H₁; apply Pos2Z_ne_0.

 rewrite greatest_series_x_power_shift.
 rewrite greatest_series_x_power_stretch.
 constructor; intros i.
 unfold normalise_series.
 unfold gcd_nz; simpl.
 rewrite Nat2Z.inj_add.
 rewrite Z.sub_add_simpl_r_r.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.gcd_mul_mono_r; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_comm.
 rewrite Z.gcd_mul_mono_l.
 rewrite Z.mul_comm; simpl.
 rewrite Z2Pos.inj_mul; simpl.
  rewrite series_shrink_shrink.
  rewrite series_left_shift_shift.
   rewrite Nat.add_sub.
   rewrite series_left_shift_stretch.
   rewrite series_shrink_stretch.
   reflexivity.

   apply le_plus_r.

  apply Z.nle_gt.
  pose proof
   (Z.gcd_nonneg (Z.gcd (nz_valnum nz + Z.of_nat m) (' nz_comden nz))
      (' greatest_series_x_power fld (nz_terms nz) m)) 
   as H₁.
  intros H₂.
  apply Z.le_antisymm in H₁; [ idtac | assumption ].
  apply Z.gcd_eq_0_r in H₁.
  revert H₁; apply Pos2Z_ne_0.

  apply Pos2Z.is_pos.
Qed.

Theorem ps_adjust_eq : ∀ nz n k, NonZero nz ≈ NonZero (adjust_nz n k nz).
Proof.
intros nz n k.
constructor.
apply nz_adjust_eq.
Qed.

Definition adjust_series n k s :=
  series_shift fld n (series_stretch fld k s).

Definition nz_terms_add (nz₁ nz₂ : nz_ps α) :=
  let k₁ := cm_factor nz₁ nz₂ in
  let k₂ := cm_factor nz₂ nz₁ in
  let v₁ := (nz_valnum nz₁ * ' k₁)%Z in
  let v₂ := (nz_valnum nz₂ * ' k₂)%Z in
  let n₁ := Z.to_nat (v₁ - Z.min v₁ v₂) in
  let n₂ := Z.to_nat (v₂ - Z.min v₂ v₁) in
  let s₁ := adjust_series n₁ k₁ (nz_terms nz₁) in
  let s₂ := adjust_series n₂ k₂ (nz_terms nz₂) in
  series_add fld s₁ s₂.

Definition nz_valnum_add (nz₁ nz₂ : nz_ps α) :=
  let k₁ := cm_factor nz₁ nz₂ in
  let k₂ := cm_factor nz₂ nz₁ in
  let v₁ := (nz_valnum nz₁ * ' k₁)%Z in
  let v₂ := (nz_valnum nz₂ * ' k₂)%Z in
  Z.min v₁ v₂.

Definition nz_add (nz₁ nz₂ : nz_ps α) :=
  {| nz_terms := nz_terms_add nz₁ nz₂;
     nz_valnum := nz_valnum_add nz₁ nz₂;
     nz_comden := cm nz₁ nz₂ |}.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_add nz₁ nz₂)
      | Zero => ps₁
      end
  | Zero => ps₂
  end.

(* version with adjust_nz, just to see... *)
Definition adjusted_nz_add nz'₁ nz'₂ :=
  {| nz_terms := series_add fld (nz_terms nz'₁) (nz_terms nz'₂);
     nz_valnum := nz_valnum nz'₁;
     nz_comden := nz_comden nz'₁ |}.

Definition nz_add₂ (nz₁ nz₂ : nz_ps α) :=
  let k₁ := cm_factor nz₁ nz₂ in
  let k₂ := cm_factor nz₂ nz₁ in
  let v₁ := (nz_valnum nz₁ * ' k₁)%Z in
  let v₂ := (nz_valnum nz₂ * ' k₂)%Z in
  let nz'₁ := adjust_nz (Z.to_nat (v₁ - Z.min v₁ v₂)) k₁ nz₁ in
  let nz'₂ := adjust_nz (Z.to_nat (v₂ - Z.min v₁ v₂)) k₂ nz₂ in
  adjusted_nz_add nz'₁ nz'₂.

Definition ps_add₂ (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_add₂ nz₁ nz₂)
      | Zero => ps₁
      end
  | Zero => ps₂
  end.

(* ps_mul *)

Fixpoint sum_mul_coeff i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add fld (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition series_mul_term (s₁ s₂ : series α) :=
  {| terms i :=
       match sum_mul_coeff 0 (S i) s₁ s₂ with
       | Some c => c
       | None => zero fld
       end;
     stop := Nbar.max (stop s₁) (stop s₂) |}.

(*
Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match nz_valnum ps₁ with
  | zfin _ =>
      match nz_valnum ps₂ with
      | zfin _ =>
          let aps₁ := adjust (cm_factor ps₁ ps₂) ps₁ in
          let aps₂ := adjust (cm_factor ps₂ ps₁) ps₂ in
          {| nz_terms := series_mul_term (nz_terms aps₁) (nz_terms aps₂);
             nz_valnum := nz_valnum aps₁ + nz_valnum aps₂;
             nz_comden := nz_comden aps₁ |}
      | ∞ => ps_zero fld
      end
  | ∞ => ps_zero fld
  end.
*)

Lemma series_stretch_add_distr : ∀ k s₁ s₂,
  series_stretch fld k (series_add fld s₁ s₂) ≃
  series_add fld (series_stretch fld k s₁) (series_stretch fld k s₂).
Proof.
intros kp s₁ s₂.
unfold series_stretch; simpl.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
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

    destruct lt₄, lt₅; rewrite fld_add_0_l; reflexivity.

 remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) * fin k)) as a.
 remember (Nbar.max (stop s₁ * fin k) (stop s₂ * fin k)) as n.
 remember (Nbar.lt_dec (fin i) n) as b.
 remember (Nbar.lt_dec (fin i) (stop s₁ * fin k)) as c.
 remember (Nbar.lt_dec (fin i) (stop s₂ * fin k)) as d.
 destruct a, b, c, d; try rewrite fld_add_0_l; reflexivity.
Qed.

Lemma stretch_shift_1_series_distr : ∀ kp s,
  series_stretch fld kp (series_shift fld 1 s) ≃
  series_shift fld (Pos.to_nat kp) (series_stretch fld kp s).
Proof.
intros kp s.
remember (Pos.to_nat kp) as x.
rewrite <- Nat.mul_1_l in Heqx; subst x.
apply stretch_shift_series_distr.
Qed.

(* *)

Lemma Pcm_factor_mul : ∀ x y,
  (x * Pos.of_nat (Pos.to_nat (Plcm x y) / Pos.to_nat x))%positive = Plcm x y.
Proof.
intros x y.
pose proof (Pos_divides_lcm_l x y) as H.
destruct H as (k, H).
rewrite H.
rewrite Pos2Nat.inj_mul.
rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Pos2Nat.id.
apply Pos.mul_comm.
Qed.

Lemma nz_terms_add_comm : ∀ ps₁ ps₂,
  nz_terms_add ps₁ ps₂ ≃ nz_terms_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold nz_terms_add.
rewrite series_add_comm; reflexivity.
Qed.

Lemma cm_comm : ∀ nz₁ nz₂, cm nz₁ nz₂ = cm nz₂ nz₁.
Proof.
intros nz₁ nz₂.
unfold cm.
apply Pos.mul_comm.
Qed.

Lemma gcd_nz_add_comm : ∀ nz₁ nz₂ n k,
  gcd_nz n k (nz_add nz₁ nz₂)%Z = gcd_nz n k (nz_add nz₂ nz₁)%Z.
Proof.
intros nz₁ nz₂ n k.
unfold gcd_nz; simpl.
unfold nz_valnum_add; simpl.
rewrite cm_comm, Z.min_comm.
reflexivity.
Qed.

Lemma nz_norm_add_comm : ∀ nz₁ nz₂,
  normalise_nz fld (nz_add nz₁ nz₂) ≐ normalise_nz fld (nz_add nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
rewrite nz_terms_add_comm.
remember (null_coeff_range_length fld (nz_terms_add nz₂ nz₁) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 unfold nz_valnum_add.
 rewrite nz_terms_add_comm, gcd_nz_add_comm, Z.min_comm; reflexivity.

 rewrite nz_terms_add_comm, gcd_nz_add_comm, cm_comm; reflexivity.

 rewrite nz_terms_add_comm, gcd_nz_add_comm; reflexivity.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add ps₁ ps₂ ≈ ps_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
constructor; apply nz_norm_add_comm.
Qed.

Lemma series_shift_add_distr : ∀ s₁ s₂ n,
  series_shift fld n (series_add fld s₁ s₂)
  ≃ series_add fld (series_shift fld n s₁) (series_shift fld n s₂).
Proof.
intros s₁ s₂ n.
constructor.
intros i.
unfold series_add, series_nth_fld; simpl.
rewrite Nbar.add_max_distr_r.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) + fin n)) as c₁.
remember (Nbar.lt_dec (fin i) (stop s₁ + fin n)) as c₂.
remember (Nbar.lt_dec (fin i) (stop s₂ + fin n)) as c₃.
remember (Nbar.lt_dec (fin (i - n)) (stop s₁)) as c₄.
remember (Nbar.lt_dec (fin (i - n)) (stop s₂)) as c₅.
clear Heqc₁ Heqc₂ Heqc₃ Heqc₄ Heqc₅.
destruct (lt_dec i n) as [Hlt| Hge].
 destruct c₁, c₂, c₃; try rewrite fld_add_0_l; reflexivity.

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

Lemma null_coeff_range_length_nonzero_fin : ∀ s n,
  null_coeff_range_length fld s 0 = fin (S n)
  → series_nth_fld fld 0 s ≍ zero fld.
Proof.
intros s n Hn.
replace 0%nat with (0 + 0)%nat by reflexivity.
apply lt_null_coeff_range_length.
rewrite Hn.
constructor; apply lt_0_Sn.
Qed.

Definition Qmin x y :=
  match x ?= y with
  | Eq => x
  | Lt => x
  | Gt => y
  end.

Definition Qmin₃ x y z := Qmin (Qmin x y) z.

Lemma Z2Nat_sub_min :  ∀ x y, Z.to_nat (x - Z.min x y) = Z.to_nat (x - y).
Proof.
intros x y.
destruct (Z.min_dec x y) as [H₁| H₁].
 rewrite H₁.
 rewrite Z.sub_diag.
 apply Z.min_l_iff in H₁.
 apply Z.le_sub_0 in H₁.
 destruct (x - y)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
 apply Z.nlt_ge in H₁.
 exfalso; apply H₁, Pos2Z.is_pos.

 rewrite H₁; reflexivity.
Qed.

Lemma nz_terms_add_assoc : ∀ nz₁ nz₂ nz₃,
  nz_terms_add (nz_add nz₁ nz₂) nz₃ ≃
  nz_terms_add nz₁ (nz_add nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
constructor; intros i.
unfold nz_add; simpl.
unfold cm_factor, cm.
unfold nz_terms_add; simpl.
unfold nz_valnum_add; simpl.
unfold cm_factor, cm.
remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
remember (nz_comden nz₁) as c₁.
remember (nz_comden nz₂) as c₂.
remember (nz_comden nz₃) as c₃.
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
remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc .
remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc .
remember (v₃ * ' c₂ * ' c₁)%Z as ccv eqn:Hccv .
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

Definition terms_add ps₁ ps₂ :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => nz_terms_add nz₁ nz₂
      | Zero => nz_terms nz₁
      end
  | Zero =>
      match ps₂ with
      | NonZero nz₂ => nz_terms nz₂
      | Zero => series_0 fld
      end
  end.

Lemma gcd_nz_add_assoc : ∀ nz₁ nz₂ nz₃ n k,
  gcd_nz n k (nz_add (nz_add nz₁ nz₂) nz₃)%Z =
  gcd_nz n k (nz_add nz₁ (nz_add nz₂ nz₃))%Z.
Proof.
intros nz₁ nz₂ nz₃ n k.
unfold gcd_nz; simpl.
unfold nz_valnum_add; simpl.
unfold nz_valnum_add; simpl.
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

Lemma nz_norm_add_assoc : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld (nz_add (nz_add nz₁ nz₂) nz₃)
  ≐ normalise_nz fld (nz_add nz₁ (nz_add nz₂ nz₃)).
Proof.
intros nz₁ nz₂ nz₃.
unfold normalise_nz; simpl.
rewrite nz_terms_add_assoc.
remember
  (null_coeff_range_length fld (nz_terms_add nz₁ (nz_add nz₂ nz₃)) 0) as n.
rename Heqn into Hn.
symmetry in Hn.
destruct n as [n| ]; constructor; constructor; simpl.
 rewrite nz_terms_add_assoc.
 rewrite gcd_nz_add_assoc.
 do 2 f_equal.
 unfold nz_valnum_add; simpl.
 unfold nz_valnum_add; simpl.
 unfold cm_factor, cm; simpl.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 f_equal; [ idtac | rewrite Z.mul_shuffle0; reflexivity ].
 f_equal; rewrite Z.mul_shuffle0; reflexivity.

 rewrite nz_terms_add_assoc.
 rewrite gcd_nz_add_assoc.
 unfold cm_factor, cm; simpl; unfold cm; simpl.
 do 4 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 reflexivity.

 rewrite nz_terms_add_assoc.
 rewrite gcd_nz_add_assoc.
 reflexivity.
Qed.

Delimit Scope ps_scope with ps.
Bind Scope ps_scope with puiseux_series.
Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ∔ b" := (nz_add a b) (at level 70).

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add (ps_add ps₁ ps₂) ps₃ ≈ ps_add ps₁ (ps_add ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | rewrite ps_add_comm; reflexivity ].
remember (ps_add (NonZero nz₁) (NonZero nz₂)) as x.
remember (ps_add (NonZero nz₂) (NonZero nz₃)) as y.
simpl in Heqx, Heqy; subst x y.
simpl; constructor.
apply nz_norm_add_assoc.
Qed.

Lemma Z2Nat_sub_mul_succ_l : ∀ a b,
  (Z.to_nat (a * ' b) - Z.to_nat ((a + 1) * ' b))%nat = O.
Proof.
intros a b.
destruct a as [| a| a]; [ reflexivity | simpl | reflexivity ].
do 2 rewrite Pos2Nat.inj_mul.
rewrite <- Nat.mul_sub_distr_r.
rewrite Pos2Nat.inj_add.
rewrite Nat.sub_add_distr, Nat.sub_diag; reflexivity.
Qed.

(* à revoir, si nécessaire...
Lemma stop_head_tail : ∀ nz,
  stop (nz_terms nz) ≠ fin 0
  → stop (nz_terms_add (nz_head nz) (nz_tail nz)) =
    stop (series_stretch fld (nz_comden nz) (nz_terms nz)).
Proof.
intros nz Hst.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail.
remember (stop (nz_terms nz)) as st.
destruct st as [st| ]; [ simpl | simpl; rewrite <- Heqst; reflexivity ].
destruct st as [| st]; [ negation Hst | simpl ].
rewrite Nat.add_0_r.
rewrite <- Heqst; simpl.
rewrite Nat.sub_0_r.
rewrite Z.mul_add_distr_r, Z.mul_1_l.
rewrite Z.sub_add_distr, Z.sub_diag; simpl.
rewrite Nat.add_0_r.
rewrite Z.add_simpl_l.
rewrite Nat.max_r; [ rewrite Nat.add_comm; reflexivity | idtac ].
apply Nat.le_sub_le_add_r; rewrite Nat.sub_diag; apply Nat.le_0_l.
Qed.
*)

Lemma stop_0_series_nth_0 : ∀ s i,
  stop s = 0%Nbar
  → series_nth_fld fld i s = zero fld.
Proof.
intros s i Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt₁| Hge₁]; [ idtac | reflexivity ].
apply Nbar.nlt_ge in Hlt₁.
 exfalso; apply Hlt₁; constructor; apply lt_0_Sn.

 constructor; apply Nat.le_0_l.
Qed.

Lemma stop_0_series_nth_stretch_0 : ∀ s n i,
  stop s = 0%Nbar
  → series_nth_fld fld i (series_stretch fld n s) = zero fld.
Proof.
intros s n i Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt₁| Hge₁]; [ idtac | reflexivity ].
apply Nbar.nlt_ge in Hlt₁.
 exfalso; apply Hlt₁; constructor; apply lt_0_Sn.

 constructor; apply Nat.le_0_l.
Qed.

Lemma stop_0_series_nth_shift_stretch_0 : ∀ s i n k,
  stop s = 0%Nbar
  → series_nth_fld fld i (series_shift fld n (series_stretch fld k s))
    = zero fld.
Proof.
intros s i n k Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) (fin n)) as [H₁| H₁]; [ idtac | reflexivity ].
destruct (lt_dec i n) as [H₂| H₂]; [ reflexivity | idtac ].
exfalso; apply H₂.
apply Nbar.fin_lt_mono; assumption.
Qed.

(* à revoir, si nécessaire...
Lemma stop_head_tail₂ : ∀ nz,
  stop (nz_terms nz) ≠ 0%Nbar
  → stop (nz_terms_add (nz_head nz) (nz_tail nz))
    = (fin (Pos.to_nat (nz_comden nz)) * stop (nz_terms nz))%Nbar.
Proof.
intros nz Hst.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail.
remember (stop (nz_terms nz)) as st.
destruct st as [st| ]; [ simpl | simpl; rewrite <- Heqst; reflexivity ].
destruct st as [| st]; [ negation Hst | simpl ].
rewrite <- Heqst; simpl.
rewrite Nat.add_0_r.
rewrite Nat.sub_0_r.
rewrite Z.mul_add_distr_r, Z.mul_1_l.
rewrite Z.sub_add_distr, Z.sub_diag; simpl.
rewrite Z.add_simpl_l; simpl.
rewrite Nat.add_0_r.
rewrite max_r.
 rewrite <- Nat.mul_succ_l, Nat.mul_comm; reflexivity.

 rewrite Nat.add_comm.
 apply Nat.le_add_r.
Qed.
*)

(* à revoir, si nécessaire...
Lemma stop_nz_add_pos_pos : ∀ nz,
  (0 < stop (nz_terms_add (nz_head nz) (nz_tail nz)))%Nbar
  → (0 < stop (nz_terms nz))%Nbar.
Proof.
intros nz H.
unfold nz_terms_add in H; simpl in H.
unfold nz_head, nz_tail in H; simpl in H.
remember (stop (nz_terms nz)) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; [ idtac | constructor ].
destruct st as [| st]; [ idtac | constructor; apply Nat.lt_0_succ ].
rewrite Hst in H; simpl in H.
rewrite Z.sub_diag in H; assumption.
Qed.
*)

(* à revoir, si nécessaire...
Lemma stop_nz_pos_add_pos : ∀ nz,
  (0 < stop (nz_terms nz))%Nbar
  → (0 < stop (nz_terms_add (nz_head nz) (nz_tail nz)))%Nbar.
Proof.
intros nz H.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail; simpl.
remember (stop (nz_terms nz)) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; [ simpl | simpl; rewrite Hst; constructor ].
destruct st as [| st]; simpl.
 exfalso; revert H; apply Nbar.lt_irrefl.

 rewrite Hst; simpl.
 rewrite Nat.add_0_r, Nat.sub_0_r.
 rewrite Z.mul_add_distr_r, Z.mul_1_l.
 rewrite Z.sub_add_distr, Z.sub_diag.
 rewrite Z.add_simpl_l; simpl.
 rewrite Nat.add_0_r.
 rewrite Nat.max_r.
  rewrite <- Nat.mul_succ_l.
  rewrite Nbar.fin_inj_mul.
  constructor.
  apply Nat.mul_pos_pos; [ apply Nat.lt_0_succ | apply Pos2Nat.is_pos ].

  rewrite Nat.add_comm; apply Nat.le_add_r.
Qed.
*)

(* à revoir, si nécessaire...
Lemma series_nth_add_head_tail : ∀ nz,
  series_nth_fld fld 0 (nz_terms nz)
  ≍ series_nth_fld fld 0 (nz_terms_add (nz_head nz) (nz_tail nz)).
Proof.
intros nz.
unfold series_nth_fld.
remember (nz_terms_add (nz_head nz) (nz_tail nz)) as s eqn:Hs .
destruct (Nbar.lt_dec 0 (stop (nz_terms nz))) as [H₁| H₁].
 destruct (Nbar.lt_dec 0 (stop s)) as [H₂| H₂].
  subst s; simpl.
  unfold nz_head, nz_tail; simpl.
  remember (stop (nz_terms nz)) as st.
  symmetry in Heqst.
  destruct st as [st| ]; simpl.
   destruct st as [st| ]; simpl.
    exfalso; revert H₁; apply Nbar.lt_irrefl.

    rewrite Z.mul_add_distr_r, Z.mul_1_l.
    rewrite Z.sub_add_distr, Z.sub_diag; simpl.
    rewrite Z.add_simpl_l; simpl.
    rewrite series_shift_0.
    unfold series_head, series_tail; simpl.
    rewrite Heqst; simpl.
    rewrite Nat.sub_0_r.
    unfold series_nth_fld; simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
    rewrite Nat.div_0_l; [ simpl | apply Pos2Nat_ne_0 ].
    remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
    destruct (Nbar.lt_dec 0 (fin c)) as [H₃| H₃].
     unfold series_nth_fld; simpl.
     destruct (Nbar.lt_dec 0 1) as [H₄| H₄].
      destruct (Nbar.lt_dec 0 (fin (st * c + c))) as [H₅| H₅].
       destruct (lt_dec 0 c) as [H₆| H₆].
        rewrite fld_add_comm, fld_add_0_l; reflexivity.

        exfalso; apply H₆; subst c; apply Pos2Nat.is_pos.

       rewrite fld_add_comm, fld_add_0_l; reflexivity.

      exfalso; apply H₄; apply Nbar.lt_0_1.

     exfalso; apply H₃; constructor; subst c; apply Pos2Nat.is_pos.

   rewrite Z.mul_add_distr_r, Z.mul_1_l.
   rewrite Z.sub_add_distr, Z.sub_diag; simpl.
   rewrite Z.add_simpl_l; simpl.
   rewrite series_shift_0.
   unfold series_head, series_tail; simpl.
   rewrite Heqst; simpl.
   unfold series_nth_fld; simpl.
   rewrite Nat.add_0_r.
   rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
   rewrite Nat.div_0_l; [ simpl | apply Pos2Nat_ne_0 ].
   unfold series_nth_fld; simpl.
   remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
   destruct (Nbar.lt_dec 0 (fin c)) as [H₃| H₃].
    destruct (Nbar.lt_dec 0 1) as [H₄| H₄].
     destruct (Nbar.lt_dec 0 inf) as [H₅| H₅].
      destruct (lt_dec 0 c) as [H₆| H₆].
       rewrite fld_add_comm, fld_add_0_l; reflexivity.

       exfalso; apply H₆; subst c; apply Pos2Nat.is_pos.

      exfalso; apply H₅; constructor.

     exfalso; apply H₄, Nbar.lt_0_1.

    exfalso; apply H₃; subst c; constructor; apply Pos2Nat.is_pos.

  exfalso; apply H₂; subst s.
  apply stop_nz_pos_add_pos; assumption.

 destruct (Nbar.lt_dec 0 (stop s)) as [H₂| H₂]; [ idtac | reflexivity ].
 exfalso; apply H₁; subst s.
 apply stop_nz_add_pos_pos; assumption.
Qed.
*)

(* à voir...
Lemma stop_tail : ∀ s, (0 < stop s)%Nbar → stop s = NS (stop (series_tail s)).
Proof.
intros s Hs.
unfold series_tail; simpl.
destruct (stop s) as [| st]; [ simpl | reflexivity ].
rewrite <- Nat.sub_succ_l.
 simpl; rewrite Nat.sub_0_r; reflexivity.

 destruct x.
  exfalso; revert Hs; apply Nbar.lt_irrefl.

  apply -> Nat.succ_le_mono; apply Nat.le_0_l.
Qed.

Lemma stop_tail_0 : ∀ s, stop s = fin 0 → stop (series_tail s) = fin 0.
Proof.
intros s H; simpl.
rewrite H; reflexivity.
Qed.

Lemma terms_S_tail : ∀ s n, terms s (S n) = terms (series_tail s) n.
Proof.
intros s n.
unfold series_tail; reflexivity.
Qed.

Lemma null_coeff_range_length_S_tail : ∀ s n,
  null_coeff_range_length fld s = fin (S n)
  → null_coeff_range_length fld (series_tail s) = fin n.
Proof.
intros s n Hn₃.
apply null_coeff_range_length_iff in Hn₃.
apply null_coeff_range_length_iff.
destruct Hn₃ as (Hisn, Hsn).
split; [ intros i Hin | idtac ].
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ].
  destruct st as [| st].
   destruct (Nbar.lt_dec (fin i) 0) as [H₁| ].
    apply Nbar.nle_gt in H₁.
    exfalso; apply H₁; constructor; apply Nat.le_0_l.

    assert (i < S n)%nat as H by omega.
    apply Hisn in H.
    unfold series_nth_fld in H.
    remember Hst as Hst₂; clear HeqHst₂.
    apply stop_0_series_nth_stretch_0 with (i := S i) (n := xH) in Hst.
    rewrite <- Hst.
    rewrite series_stretch_1.
    unfold series_nth_fld.
    rewrite <- terms_S_tail.
    rewrite Hst₂.
    rewrite stop_tail_0; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
     contradiction.

     destruct (Nbar.lt_dec (fin (S i)) 0) as [H₂| H₂].
      apply Nbar.nle_gt in H₂.
      exfalso; apply H₂; constructor; apply Nat.le_0_l.

      reflexivity.

   apply Nat.succ_lt_mono in Hin.
   apply Hisn in Hin.
   unfold series_nth_fld.
   rename Hin into H.
   unfold series_nth_fld in H.
   remember Hst as Hst₂; clear HeqHst₂.
   rewrite stop_tail in H.
    remember (series_tail s) as s₁.
    destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
     destruct (Nbar.lt_dec (fin (S i)) (NS (stop s₁))) as [H₂| H₂].
      rewrite Heqs₁.
      rewrite <- terms_S_tail.
      assumption.

      exfalso; apply H₂.
      destruct (stop s₁) as [st₁| ].
       destruct st₁ as [| st₁].
        apply Nbar.nle_gt in H₁.
        exfalso; apply H₁, Nbar.le_0_l.

        simpl.
        constructor.
        apply Nbar.fin_lt_mono in H₁.
        apply Nat.succ_lt_mono in H₁; assumption.

       constructor.

     reflexivity.

    rewrite Hst.
    constructor; apply Nat.lt_0_succ.

  apply Nat.succ_lt_mono in Hin.
  apply Hisn in Hin.
  unfold series_nth_fld.
  rename Hin into H.
  unfold series_nth_fld in H.
  remember Hst as Hst₂; clear HeqHst₂.
  rewrite stop_tail in H.
   remember (series_tail s) as s₁.
   destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin (S i)) (NS (stop s₁))) as [H₂| H₂].
     rewrite Heqs₁.
     rewrite <- terms_S_tail.
     assumption.

     exfalso; apply H₂.
     destruct (stop s₁) as [st₁| ].
      destruct st₁ as [| st₁].
       apply Nbar.nle_gt in H₁.
       exfalso; apply H₁, Nbar.le_0_l.

       simpl.
       constructor.
       apply Nbar.fin_lt_mono in H₁.
       apply Nat.succ_lt_mono in H₁; assumption.

      constructor.

    reflexivity.

   rewrite Hst; constructor.

 unfold series_nth_fld.
 unfold series_nth_fld in Hsn.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ].
  destruct st as [| st].
   destruct (Nbar.lt_dec (fin (S n)) 0) as [H₁| ]; [ idtac | negation Hsn ].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁; constructor; apply Nat.le_0_l.

   rewrite <- Hst in Hsn.
   rewrite stop_tail in Hsn.
    remember (stop (series_tail s)) as st₁.
    destruct (Nbar.lt_dec (fin n) st₁) as [H₁| H₁].
     destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
      rewrite <- terms_S_tail; assumption.

      negation Hsn.

     destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
      exfalso; apply H₁.
      destruct st₁ as [st₁| ]; [ idtac | constructor ].
      constructor.
      apply Nat.succ_lt_mono.
      inversion H₂; assumption.

      negation Hsn.

    rewrite Hst.
    constructor.
    apply Nat.lt_0_succ.

  rewrite <- Hst in Hsn.
  rewrite stop_tail in Hsn.
   remember (stop (series_tail s)) as st₁.
   destruct (Nbar.lt_dec (fin n) st₁) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
     rewrite <- terms_S_tail; assumption.

     negation Hsn.

    destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
     exfalso; apply H₁.
     destruct st₁ as [st₁| ]; [ idtac | constructor ].
     constructor.
     apply Nat.succ_lt_mono.
     inversion H₂; assumption.

     negation Hsn.

   rewrite Hst; constructor.
Qed.
*)

Definition series_tail_n n (s : series α) :=
  {| terms i := terms s (i + n); stop := stop s - fin n |}.

Definition series_stretch_nat n s :=
  {| terms i :=
       if zerop (i mod n) then
         series_nth_fld fld (i / n) s
       else zero fld;
     stop :=
       stop s * fin n |}.

Lemma series_stretch_to_nat : ∀ k s,
  series_stretch fld k s = series_stretch_nat (Pos.to_nat k) s.
Proof. reflexivity. Qed.

Lemma series_tail_n_tail_comm : ∀ n s,
  series_tail (series_tail_n n s) = series_tail_n n (series_tail s).
Proof.
intros n s.
unfold series_tail_n, series_tail.
simpl; f_equal.
destruct (stop s) as [st| ]; [ idtac | reflexivity ].
rewrite <- Nat.sub_add_distr, Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Lemma series_nth_tail : ∀ i s,
  series_nth_fld fld i (series_tail s) = series_nth_fld fld (S i) s.
Proof.
intros i s.
unfold series_nth_fld, series_tail; simpl.
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 destruct (Nbar.lt_dec (fin i) (fin (st - 1))) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin (S i)) (fin st)) as [H₂| H₂].
   reflexivity.

   destruct st as [| st].
    apply Nbar.nle_gt in H₁.
    exfalso; apply H₁, Nbar.le_0_l.

    simpl in H₁; rewrite Nat.sub_0_r in H₁.
    apply Nbar.succ_lt_mono in H₁.
    exfalso; apply H₂; assumption.

  destruct (Nbar.lt_dec (fin (S i)) (fin st)) as [H₂| H₂].
   destruct st as [| st].
    apply Nbar.nle_gt in H₂.
    exfalso; apply H₂, Nbar.le_0_l.

    simpl in H₁; rewrite Nat.sub_0_r in H₁.
    exfalso; apply H₁, Nbar.succ_lt_mono.
    assumption.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin (S i)) ∞) as [H₂| H₂]; [ reflexivity | idtac ].
  exfalso; apply H₂; constructor.

  exfalso; apply H₁; constructor.
Qed.

Lemma series_stretch_tail : ∀ k s,
  series_stretch fld k (series_tail s)
  ≃ series_tail_n (Pos.to_nat k) (series_stretch fld k s).
Proof.
intros k s.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nat.add_mod; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Nat.mod_same; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Nat.add_0_r.
rewrite Nat.mod_mod; [ idtac | apply Pos2Nat_ne_0 ].
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; simpl.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite series_nth_tail.
 remember (Pos.to_nat k) as x.
 replace (i + x)%nat with (i + 1 * x)%nat .
  rewrite Nat.div_add; [ idtac | subst x; apply Pos2Nat_ne_0 ].
  rewrite Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_l; reflexivity.

 rewrite series_nth_tail.
 remember (Pos.to_nat k) as x.
 replace (i + x)%nat with (i + 1 * x)%nat .
  rewrite Nat.div_add; [ idtac | subst x; apply Pos2Nat_ne_0 ].
  rewrite Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_l; reflexivity.
Qed.

(*
Definition norm_nz nz₁ nz₂ :=
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  let s₁ := series_stretch fld (cm_factor nz₁ nz₂) (nz_terms nz₁) in
  {| nz_terms := series_shift fld (Z.to_nat (v₁ - v₂)) s₁;
     nz_valnum := Z.min v₁ v₂;
     nz_comden := cm nz₁ nz₂ |}.

Lemma nz_add_norm : ∀ nz₁ nz₂ v,
  NonZero (nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (nz_add fld (v * Pos.to_nat (nz_comden nz₁ * nz_comden nz₂))%nat
         (norm_nz nz₁ nz₂) (norm_nz nz₂ nz₁)).
Proof.
intros nz₁ nz₂ v.
remember (nz_comden nz₁ * nz_comden nz₂)%positive as c.
constructor 1 with (k₁ := c) (k₂ := xH); subst c; simpl.
 constructor; intros i.
 unfold series_nth_fld; simpl.
 unfold cm_factor, cm; simpl.
 remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
 remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
 remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
 remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
 symmetry in Hv₁, Hv₂, Hc₁, Hc₂.
 rewrite divmod_div.
 rewrite Nat.div_1_r.
 rewrite Z.min_comm.
 replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
 rewrite Z.sub_diag; simpl.
 do 2 rewrite Nbar.add_0_r.
 remember (Z.to_nat (v₁ * ' c₂ - v₂ * ' c₁))%Z as vc₁ eqn:Hvc₁ .
 remember (Z.to_nat (v₂ * ' c₁ - v₁ * ' c₂))%Z as vc₂ eqn:Hvc₂ .
 symmetry in Hvc₁, Hvc₂.
 rewrite Nbar.mul_1_r.
 rewrite Nbar.mul_max_distr_r.
 remember
  (Nbar.max (stop (nz_terms nz₁) * fin (Pos.to_nat c₂) + fin vc₁)
     (stop (nz_terms nz₂) * fin (Pos.to_nat c₁) + fin vc₂) *
   fin (Pos.to_nat (c₁ * c₂)))%Nbar as x.
 destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
 destruct (zerop (i mod Pos.to_nat (c₁ * c₂))) as [H₂| H₂].
  apply Nat.mod_divides in H₂; [ idtac | apply Pos2Nat_ne_0 ].
  destruct H₂ as (k, Hi).
  rewrite Hi.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
  unfold nz_terms_add; simpl.
  unfold cm_factor, cm; simpl.
  rewrite Hv₁, Hv₂, Hc₁, Hc₂.
  rewrite Hvc₁, Hvc₂.
  rewrite Z.min_comm.
  replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
  rewrite Z.sub_diag; simpl.
  do 2 rewrite series_shift_0.
  rewrite <- series_stretch_add_distr.
  rewrite Nat.mul_comm.
  rewrite series_nth_fld_mul_stretch.
  reflexivity.

  remember (norm_nz nz₁ nz₂) as nz'₁.
  remember (norm_nz nz₂ nz₁) as nz'₂.
  unfold nz_terms_add.
  subst nz'₁ nz'₂; simpl.
  unfold cm_factor, cm; simpl.
  rewrite Hv₁, Hv₂, Hc₁, Hc₂.
  rewrite Hvc₁, Hvc₂.
  rewrite Z.min_comm.
  replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
  rewrite Z.sub_diag; simpl.
  do 2 rewrite series_shift_0.
  rewrite <- series_stretch_add_distr.
  symmetry.
  rewrite shifted_in_stretched; [ reflexivity | assumption ].

 unfold cm_factor, cm; simpl.
 rewrite Z.mul_1_r.
 symmetry.
 rewrite Z.min_l.
  rewrite Nat2Z.inj_mul.
  rewrite positive_nat_Z.
  rewrite Z.mul_add_distr_r.
  rewrite Pos.mul_comm.
  reflexivity.

  rewrite Z.min_comm, Pos.mul_comm; reflexivity.

 rewrite Pos.mul_1_r.
 unfold cm; simpl.
 unfold cm; simpl.
 f_equal.
 apply Pos.mul_comm.
Qed.

Definition norm₂_nz (nz₁ nz₂ nz₃ : nz_ps α) :=
  let c₁ := nz_comden nz₁ in
  let c₂ := nz_comden nz₂ in
  let c₃ := nz_comden nz₃ in
  let v₁ := (nz_valnum nz₁ * 'c₂ * 'c₃)%Z in
  let v₂ := (nz_valnum nz₂ * 'c₃ * 'c₁)%Z in
  let v₃ := (nz_valnum nz₃ * 'c₁ * 'c₂)%Z in
  let vm := Z.min v₁ (Z.min v₂ v₃) in
  let s₁ := series_stretch fld (c₂ * c₃) (nz_terms nz₁) in
  {| nz_terms := series_shift fld (Z.to_nat (v₁ - vm)) s₁;
     nz_valnum := vm;
     nz_comden := c₁ * c₂ * c₃ |}.

Lemma nz_add_norm₂ : ∀ nz₁ nz₂ nz₃ v,
  NonZero (nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (nz_add fld
         (v *
          Pos.to_nat
            (nz_comden nz₁ * nz_comden nz₂ * nz_comden nz₃ * nz_comden nz₃))
         (norm₂_nz nz₁ nz₂ nz₃) (norm₂_nz nz₂ nz₁ nz₃)).
Proof.
intros nz₁ nz₂ nz₃ v.
remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
remember (nz_comden nz₃) as c₃ eqn:Hc₃ .
symmetry in Hc₁, Hc₂, Hc₃.
remember (c₁ * c₂ * c₃ * c₃)%positive as c.
constructor 1 with (k₁ := c) (k₂ := xH); subst c; simpl.
 3: unfold cm; simpl.
 3: rewrite Hc₁, Hc₂, Hc₃.
 Focus 2.
 unfold cm_factor.
 rewrite Hc₁, Hc₂, Hc₃.
 remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
 remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
 remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
 rewrite Z.mul_add_distr_r.
 rewrite Z.mul_1_r.
 f_equal.
  symmetry.
  rewrite Z.min_l.
   rewrite Z.min_assoc.
aaa.
mmm.... pas sûr que ce soit bon.
*)

(*
Lemma zzz : ∀ nz₁ nz₂ nz₃ n,
  NonZero nz₂ ≈ NonZero nz₃
  → NonZero (nz_add fld 0 nz₁ nz₂)
    ≈ NonZero (nz_add fld n nz₁ nz₃).
Proof.
intros nz₁ nz₂ nz₃ n H₂₃.
rewrite nz_add_norm₂ with (nz₃ := nz₃); symmetry.
rewrite nz_add_norm₂ with (nz₃ := nz₂); symmetry; simpl.
aaa.
intros nz₁ nz₂ nz₃ n H₂₃.
rewrite nz_add_norm; symmetry.
rewrite nz_add_norm; symmetry.
rewrite Nat.mul_0_l.
revert nz₁ nz₂ nz₃ H₂₃.
induction n; intros.
 inversion H₂₃; subst; simpl.
 constructor 1 with (k₁ := k₁) (k₂ := k₂); simpl.
  inversion H1; subst.
  constructor; intros i.
  remember norm_nz as f.
  unfold nz_terms_add.
  unfold cm_factor, cm; simpl.
  do 2 rewrite series_stretch_add_distr.
  do 4 rewrite stretch_shift_series_distr.
  do 4 rewrite <- series_stretch_stretch.
  do 4 rewrite Pos.mul_comm, series_stretch_stretch.
  subst f; simpl.
  unfold cm_factor, cm; simpl.
  remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
  remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
  remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
  remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
  remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
  remember (nz_comden nz₃) as c₃ eqn:Hc₃ .
  rewrite Z.min_comm, Pos.mul_comm, Z.sub_diag; symmetry.
  rewrite Z.min_comm, Pos.mul_comm, Z.sub_diag; symmetry.
  simpl.
  do 4 rewrite series_shift_0.
  do 8 rewrite stretch_shift_series_distr.
  do 8 rewrite <- series_stretch_stretch.
  move H1 at bottom.
  move H2 at bottom.
  move H3 at bottom.
  remember (Z.to_nat (v₁ * ' c₃ - v₃ * ' c₁) * Pos.to_nat k₂)%nat as x.
  assert (Z.to_nat (v₁ * ' c₂ - v₂ * ' c₁) * Pos.to_nat k₁ = x)%nat as H₁.
   subst x.
   do 2 rewrite <- Z2Nat_inj_mul_pos_r.
   do 2 rewrite Z.mul_sub_distr_r.
   assert (v₂ * ' c₁ * ' k₁ = v₃ * ' c₁ * ' k₂)%Z as H₁.
    rewrite Z.mul_shuffle0, H2, Z.mul_shuffle0; reflexivity.

    rewrite H₁; clear H₁; rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
    rewrite H3, Pos2Z.inj_mul, Z.mul_assoc; reflexivity.

   rewrite H₁; clear H₁.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite Pos.mul_comm.
   rewrite series_stretch_stretch.
   rewrite <- stretch_shift_series_distr.
   rewrite <- Pos.mul_assoc, H3, Pos.mul_assoc.
   symmetry.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite Pos.mul_comm.
   rewrite series_stretch_stretch.
   rewrite <- stretch_shift_series_distr.
   symmetry.
   rewrite series_add_comm.
   remember (Z.to_nat (v₃ * ' c₁ - v₁ * ' c₃) * Pos.to_nat k₂)%nat as y.
   assert (Z.to_nat (v₂ * ' c₁ - v₁ * ' c₂) * Pos.to_nat k₁ = y)%nat as H₁.
    subst y.
    do 2 rewrite <- Z2Nat_inj_mul_pos_r.
    do 2 rewrite Z.mul_sub_distr_r.
    assert (v₁ * ' c₂ * ' k₁ = v₁ * ' c₃ * ' k₂)%Z as H₁.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     rewrite H3.
     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     reflexivity.

     rewrite H₁; clear H₁.
     rewrite Z.mul_shuffle0, H2, Z.mul_shuffle0.
     reflexivity.

    rewrite H₁; clear H₁.
    assert
     (series_stretch fld (c₁ * c₃ * k₂ * c₁) (nz_terms nz₂)
      ≃ series_stretch fld (c₁ * c₂ * k₂ * c₁) (nz_terms nz₃)) 
     as H₁.
     assert (c₁ * c₃ * k₂ * c₁ = c₁ * c₂ * k₁ * c₁)%positive as H₁.
      f_equal.
      rewrite <- Pos.mul_assoc, <- H3, Pos.mul_assoc.
      reflexivity.

      rewrite H₁; clear H₁.
      rewrite Pos_mul_shuffle0.
      rewrite series_stretch_stretch, H1, <- series_stretch_stretch.
      rewrite Pos_mul_shuffle0; reflexivity.

     rewrite H₁; clear H₁.
     rewrite Nat.mul_assoc.
     assert (c₁ * c₂ * k₂ * c₁ = c₂ * (c₁ * k₂ * c₁))%positive as H₁.
      rewrite Pos.mul_assoc; f_equal.
      rewrite Pos.mul_assoc; f_equal.
      apply Pos.mul_comm.

      rewrite H₁; clear H₁.
      rewrite series_stretch_stretch.
      rewrite <- stretch_shift_series_distr.
      rewrite <- series_stretch_add_distr.
      rewrite series_add_comm.
      symmetry.
      rewrite series_add_comm.
      rewrite Nat.mul_assoc.
      assert (c₁ * c₃ * k₂ * c₁ = c₃ * (c₁ * k₂ * c₁))%positive as H₁.
       rewrite Pos.mul_assoc; f_equal.
       rewrite Pos.mul_assoc; f_equal.
       apply Pos.mul_comm.

       rewrite H₁; clear H₁.
       rewrite series_stretch_stretch.
       rewrite <- stretch_shift_series_distr.
       rewrite <- series_stretch_add_distr.
       rewrite series_add_comm.
       remember
        (series_add fld
           (series_shift fld (x * Pos.to_nat c₁)
              (series_stretch fld (c₁ * c₃ * k₂) (nz_terms nz₁)))
           (series_shift fld (y * Pos.to_nat c₁)
              (series_stretch fld (c₁ * k₂ * c₁) (nz_terms nz₃)))) as z.
       do 2 rewrite <- Pos.mul_assoc in Heqz.
       subst z.
       rewrite series_stretch_stretch.
       rewrite <- stretch_shift_series_distr.
       rewrite series_add_comm.
       rewrite series_stretch_stretch.
       rewrite <- stretch_shift_series_distr.
       rewrite <- series_stretch_add_distr.
       remember
        (series_stretch fld c₁
           (series_add fld
              (series_shift fld y
                 (series_stretch fld (k₂ * c₁) (nz_terms nz₃)))
              (series_shift fld x
                 (series_stretch fld (c₃ * k₂) (nz_terms nz₁))))) as z.
Focus 1.
aaa.
*)

(*
Theorem ps_add_compat : ∀ ps₁ ps₂ ps₃ ps₄,
  ps₁ ≈ ps₂
  → ps₃ ≈ ps₄
    → ps_add fld ps₁ ps₃ ≈ ps_add fld ps₂ ps₄.
Proof.
intros ps₁ ps₃ ps₂ ps₄ H₁ H₂.
transitivity (ps_add fld ps₁ ps₄).
aaa.
 apply ps_add_cancel_l; assumption.

 rewrite ps_add_comm; symmetry.
 rewrite ps_add_comm; symmetry.
 apply ps_add_cancel_l; assumption.
Qed.
*)

(*
Add Parametric Morphism : (ps_add fld) with 
signature (eq_ps fld) ==> (eq_ps fld) ==> (eq_ps fld) as ps_add_morph.
Proof.
intros ps₁ ps₃ H₁ ps₂ ps₄ H₂.
aaa.
*)

Theorem ps_add_0_l : ∀ ps, ps_add (ps_zero _) ps ≈ ps.
Proof. reflexivity. Qed.

Definition nz_neg nz :=
  {| nz_terms := series_neg fld (nz_terms nz);
     nz_valnum := nz_valnum nz;
     nz_comden := nz_comden nz |}.

Definition ps_neg ps :=
  match ps with
  | NonZero nz => NonZero (nz_neg nz)
  | Zero => Zero _
  end.

Lemma add_neg_nth : ∀ s i,
  add fld (series_nth_fld fld i s) (series_nth_fld fld i (series_neg fld s)) ≍
  zero fld.
Proof.
intros s i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) (stop s)).
 apply fld_add_neg.

 apply fld_add_0_l.
Qed.

Definition mk_nonzero (s : series α) v c := NonZero (mknz s v c).

Lemma fold_mk_nonzero : ∀ (s : series α) v c,
  NonZero (mknz s v c) = mk_nonzero s v c.
Proof. reflexivity. Qed.

Add Parametric Morphism : mk_nonzero
with signature eq_series fld ==> eq ==> eq ==> eq_ps fld as NonZero_morph.
Proof.
intros s₁ s₂ Heq v c.
constructor.
unfold normalise_nz; simpl.
rewrite <- Heq.
remember (null_coeff_range_length fld s₁ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite Heq in |- * at 1; reflexivity.

 rewrite Heq in |- * at 1; reflexivity.

 rewrite Heq in |- * at 1 3; reflexivity.
Qed.

Theorem ps_add_neg : ∀ ps, ps_add ps (ps_neg ps) ≈ ps_zero _.
Proof.
intros ps.
unfold ps_zero.
unfold ps_add; simpl.
destruct ps as [nz| ]; [ simpl | reflexivity ].
constructor; simpl.
unfold nz_neg; simpl.
unfold nz_terms_add; simpl.
unfold cm_factor; simpl.
rewrite Z.min_id.
rewrite Z.sub_diag; simpl.
unfold adjust_series.
do 2 rewrite series_shift_0.
rewrite <- series_stretch_add_distr.
rewrite series_add_neg.
rewrite series_stretch_series_0.
reflexivity.
Qed.

Definition nz_zero :=
  {| nz_terms := series_0 fld;
     nz_valnum := 0;
     nz_comden := 1 |}.

Lemma series_shift_series_0 : ∀ n,
  series_shift fld n (series_0 fld) ≃ series_0 fld.
Proof.
intros n.
constructor; intros i.
unfold series_nth_fld; simpl.
remember (Nbar.lt_dec (fin i) (fin n)) as d₁.
remember (lt_dec i n) as d₂.
remember (Nbar.lt_dec (fin i) 0) as d₃.
destruct d₁, d₂, d₃; reflexivity.
Qed.

Lemma nz_add_0_r : ∀ nz,
  nz_terms_add nz nz_zero ≃
  series_shift fld (Z.to_nat (nz_valnum nz)) (nz_terms nz).
Proof.
intros nz.
unfold nz_terms_add; simpl.
unfold adjust_series.
rewrite Z2Nat_sub_min.
rewrite Z.mul_1_r, Z.sub_0_r.
rewrite series_stretch_1.
rewrite series_stretch_series_0.
rewrite series_shift_series_0.
rewrite series_add_comm.
rewrite series_add_0_l.
reflexivity.
Qed.

Lemma eq_nz_add_add₂ : ∀ nz₁ nz₂,
  eq_nz fld (nz_add nz₁ nz₂) (nz_add₂ nz₁ nz₂).
Proof.
intros nz₁ nz₂.
constructor; [ simpl | reflexivity | simpl ].
 unfold nz_valnum_add.
 rewrite Z2Nat.id.
  rewrite Z.sub_sub_distr.
  rewrite Z.sub_diag; simpl.
  reflexivity.

  rewrite <- Z.sub_max_distr_l.
  rewrite Z.sub_diag.
  apply Z.le_max_l.

 unfold nz_terms_add.
 unfold adjust_series.
 remember (nz_valnum nz₂ * ' cm_factor nz₂ nz₁)%Z as vc₂₁.
 remember (nz_valnum nz₁ * ' cm_factor nz₁ nz₂)%Z as vc₁₂.
 remember (Z.min vc₁₂ vc₂₁) as m eqn:Hm .
 rewrite Z.min_comm, <- Hm.
 reflexivity.
Qed.

Lemma eq_nz_norm_add_add₂ : ∀ nz₁ nz₂,
  normalise_nz fld (nz_add nz₁ nz₂) ≐ normalise_nz fld (nz_add₂ nz₁ nz₂).
Proof.
intros nz₁ nz₂.
rewrite eq_nz_add_add₂; reflexivity.
Qed.

Lemma eq_ps_add_add₂ : ∀ ps₁ ps₂, (ps₁ + ps₂)%ps ≈ ps_add₂ ps₁ ps₂.
Proof.
intros ps₁ ps₂.
destruct ps₁ as [ps₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [ps₂| ]; [ idtac | reflexivity ].
constructor.
apply eq_nz_norm_add_add₂.
Qed.

End fld.
