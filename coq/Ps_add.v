(* $Id: Ps_add.v,v 1.15 2013-10-13 19:00:48 deraugla Exp $ *)

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
(* mmm... bizarre... nz_valnum n'a pas l'air de coller avec la définition
   dans build_nz_add et adjust_series... à voir
Definition adjust_nz n k nz :=
  {| nz_terms := series_shift fld n (stretch_series fld k (nz_terms nz));
     nz_valnum := nz_valnum nz * Zpos k - Z.of_nat n;
     nz_comden := nz_comden nz * k |}.
*)

(* à voir...
Theorem glop : ∀ nz n k,
  NonZero nz ≈ NonZero (adjust_nz n k nz).
Proof.
intros nz n k.
constructor.
unfold normalise_nz; simpl.
rewrite first_nonzero_shift.
rewrite first_nonzero_stretch_0.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (first_nonzero fld (nz_terms nz) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
constructor; simpl.
 rewrite shrink_factor_shift.
aaa.
 rewrite shrink_factor_stretch; [ idtac | assumption | idtac ].
 rewrite Nat2Z.inj_add, Z.add_assoc.
 rewrite Z.add_shuffle0.
 rewrite Z.sub_add.
 rewrite Nat2Z.inj_mul, positive_nat_Z.
 rewrite <- Z.mul_add_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_comm.
 rewrite Z.div_mul_cancel_l; try apply Zpos_ne_0; reflexivity.
aaa.
*)

Definition adjust_series n k s :=
  series_shift fld n (stretch_series fld k s).

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

Definition build_nz_add (nz₁ nz₂ : nz_ps α) :=
  {| nz_terms := nz_terms_add nz₁ nz₂;
     nz_valnum := nz_valnum_add nz₁ nz₂;
     nz_comden := cm nz₁ nz₂ |}.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (build_nz_add nz₁ nz₂)
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

Lemma stretch_series_add_distr : ∀ k s₁ s₂,
  stretch_series fld k (series_add fld s₁ s₂) ≃
  series_add fld (stretch_series fld k s₁) (stretch_series fld k s₂).
Proof.
intros kp s₁ s₂.
unfold stretch_series; simpl.
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
  stretch_series fld kp (series_shift fld 1 s) ≃
  series_shift fld (Pos.to_nat kp) (stretch_series fld kp s).
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
  gcd_nz n k (build_nz_add nz₁ nz₂)%Z =
  gcd_nz n k (build_nz_add nz₂ nz₁)%Z.
Proof.
intros nz₁ nz₂ n k.
unfold gcd_nz; simpl.
unfold nz_valnum_add; simpl.
rewrite cm_comm, Z.min_comm.
reflexivity.
Qed.

Lemma nz_norm_add_comm : ∀ nz₁ nz₂,
  eq_norm_ps fld
    (normalise_nz fld (build_nz_add nz₁ nz₂))
    (normalise_nz fld (build_nz_add nz₂ nz₁)).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
rewrite nz_terms_add_comm.
remember (first_nonzero fld (nz_terms_add nz₂ nz₁) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl.
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

Lemma first_nonzero_nonzero_fin : ∀ s n,
  first_nonzero fld s 0 = fin (S n)
  → series_nth_fld fld 0 s ≍ zero fld.
Proof.
intros s n Hn.
replace 0%nat with (0 + 0)%nat by reflexivity.
apply lt_first_nonzero.
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
  nz_terms_add (build_nz_add nz₁ nz₂) nz₃ ≃
  nz_terms_add nz₁ (build_nz_add nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
constructor; intros i.
unfold build_nz_add; simpl.
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
do 2 rewrite stretch_series_add_distr.
do 2 rewrite series_shift_add_distr.
rewrite series_add_assoc.
do 4 rewrite stretch_shift_series_distr.
do 4 rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
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
  gcd_nz n k (build_nz_add (build_nz_add nz₁ nz₂) nz₃)%Z =
  gcd_nz n k (build_nz_add nz₁ (build_nz_add nz₂ nz₃))%Z.
Proof.
intros nz₁ nz₂ nz₃ n k.
unfold gcd_nz; simpl.
unfold nz_valnum_add; simpl.
unfold nz_valnum_add; simpl.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite Z.min_assoc.
unfold cm_factor, cm; simpl; unfold cm; simpl.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_assoc.
rewrite Pos.mul_assoc.
do 4 f_equal.
f_equal; [ idtac | rewrite Z.mul_shuffle0; reflexivity ].
f_equal; rewrite Z.mul_shuffle0; reflexivity.
Qed.

Lemma nz_norm_add_assoc : ∀ nz₁ nz₂ nz₃,
  eq_norm_ps fld
    (normalise_nz fld (build_nz_add (build_nz_add nz₁ nz₂) nz₃))
    (normalise_nz fld (build_nz_add nz₁ (build_nz_add nz₂ nz₃))).
Proof.
intros nz₁ nz₂ nz₃.
unfold normalise_nz; simpl.
rewrite nz_terms_add_assoc.
remember (first_nonzero fld (nz_terms_add nz₁ (build_nz_add nz₂ nz₃)) 0) as n.
rename Heqn into Hn.
symmetry in Hn.
destruct n as [n| ]; constructor; simpl.
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

(*
Lemma nz_add_assoc_base : ∀ nz₁ nz₂ nz₃,
  nz_add (build_nz_add nz₁ nz₂) nz₃ ≈
  nz_add nz₁ (build_nz_add nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
unfold nz_add.
rewrite nz_terms_add_assoc.
remember (nz_terms_add nz₁ (build_nz_add nz₂ nz₃)) as nz.
remember (first_nonzero fld nz) as n eqn:Hn ; subst nz.
destruct n as [n| ]; [ constructor | reflexivity ].
apply nz_norm_add_assoc.
Qed.
*)

Delimit Scope ps_scope with ps.
Bind Scope ps_scope with puiseux_series.
Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ∔ b" := (build_nz_add a b) (at level 70).

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
    stop (stretch_series fld (nz_comden nz) (nz_terms nz)).
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
  → series_nth_fld fld i (stretch_series fld n s) = zero fld.
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
  → series_nth_fld fld i (series_shift fld n (stretch_series fld k s))
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

(* à voir...
Lemma ps_cons : ∀ nz,
  series_nth_fld fld 0 (nz_terms_add (nz_head nz) (nz_tail nz)) ≭ zero fld
  → nz_add (nz_head nz) (nz_tail nz) ≈ NonZero nz.
Proof.
intros nz Hzz.
remember (nz_terms_add (nz_head nz) (nz_tail nz)) as s.
remember (first_nonzero fld s) as n eqn:Hn ; subst s.
symmetry in Hn.
destruct n as [[| n]| ].
 destruct (Nbar.eq_dec (stop (nz_terms nz)) (fin 0)) as [Hst| Hst].
  unfold nz_add.
  rewrite Hn.
  constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
   rewrite stretch_series_1.
   constructor; intros i.
   rewrite stop_0_series_nth_stretch_0; [ idtac | assumption ].
   unfold series_nth_fld; simpl.
   unfold nz_head, nz_tail; simpl.
   rewrite Hst; simpl.
   rewrite Hst; simpl.
   rewrite Z.sub_diag; simpl.
   destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁]; [ idtac | reflexivity ].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁, Nbar.le_0_l.

   unfold nz_head, nz_tail; simpl.
   rewrite Hst.
   rewrite Z.mul_1_r.
   rewrite Z.min_id; reflexivity.

   unfold nz_head, nz_tail; simpl.
   rewrite Hst.
   rewrite Pos.mul_1_r; reflexivity.

  unfold nz_add.
  rewrite Hn.
  constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
   rewrite stretch_series_1.
   constructor; intros i.
   remember (nz_terms_add fld (nz_head nz) (nz_tail nz)) as s₁ eqn:Hs₁ .
   remember (stretch_series fld (nz_comden nz) (nz_terms nz)) as s₂ eqn:Hs₂ .
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [H₂| H₂].
     subst s₁ s₂; simpl.
     unfold nz_head, nz_tail; simpl.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ]; simpl in H₁, H₂ |- *.
      destruct st as [| st]; [ negation Hst | simpl in H₁ |- * ].
      rewrite Z.mul_add_distr_r, Z.mul_1_l.
      rewrite Z.sub_add_distr, Z.sub_diag.
      rewrite Z.add_simpl_l; simpl.
      rewrite series_shift_0.
      destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
       apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
       destruct Hz as (k, Hi); subst i.
       rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
       unfold series_head, series_tail; simpl.
       rewrite Heqst; simpl.
       rewrite Nat.sub_0_r.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       unfold series_nth_fld; simpl.
       rewrite Nat.add_0_r.
       rewrite <- Hc.
       rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.mul_comm, <- Nat.mul_pred_r.
       destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [H₃| H₃].
        remember (c * k)%nat as x.
        rewrite Nat.mul_comm, <- Nat.mul_succ_r; subst x.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (c * S st))) as [H₄| H₄].
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          rewrite fld_add_comm, fld_add_0_l.
          destruct (Nbar.lt_dec (fin k) 1) as [H₆| H₆].
           destruct (Nbar.lt_dec (fin k) (fin (S st))) as [| H₇].
            reflexivity.

            exfalso; apply H₇; clear H₇.
            rewrite Heqst, Nbar.fin_inj_mul in H₂.
            apply <- Nbar.mul_lt_mono_pos_r.
             rewrite Nbar.mul_comm; eassumption.

             intros H; discriminate H.

             intros H; discriminate H.

             destruct k; [ rewrite Nat.mul_0_r in H₃; assumption | idtac ].
             apply Nbar.nle_gt in H₆.
             exfalso; apply H₆.
             constructor; apply le_n_S, le_0_n.

           apply Nbar.nlt_ge in H₆.
           destruct k.
            apply Nbar.nlt_ge in H₆.
            exfalso; apply H₆; constructor; apply Nat.lt_0_1.

            apply Nbar.nlt_ge in H₃.
             exfalso; apply H₃.

             constructor.
             rewrite Nat.mul_comm; simpl.
             apply le_plus_l.

          destruct k.
           exfalso; apply H₅; rewrite Nat.mul_0_r; subst c.
           apply Pos2Nat.is_pos.

           unfold series_nth_fld; simpl.
           rewrite Nat.mul_comm.
           rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           destruct (Nbar.lt_dec (fin (S k)) 1) as [H₆| H₆].
            apply Nbar.nlt_ge in H₆.
             exfalso; apply H₆.

             constructor; apply le_n_S, le_0_n.

            rewrite fld_add_0_l.
            rewrite Heqst.
            destruct (Nbar.lt_dec (fin k) (fin st)) as [H₇| H₇].
             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₈| H₈].
              reflexivity.

              exfalso; apply H₈.
              constructor; apply lt_n_S.
              inversion H₇; assumption.

             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₈| H₈].
              exfalso; apply H₇.
              constructor; apply lt_S_n.
              inversion H₈; assumption.

              reflexivity.

         rewrite Heqst in H₂.
         replace (c * S st)%nat with (S st * c)%nat in H₄ .
          contradiction.

          apply Nat.mul_comm.

        rewrite fld_add_0_l.
        rewrite <- Nat.mul_succ_l.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (S st * c))) as [H₄| H₄].
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          exfalso; apply H₃.
          constructor; assumption.

          rewrite Nat.mul_comm.
          rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          destruct k.
           rewrite Nat.mul_0_r in H₅.
           exfalso; apply H₅; subst c; apply Pos2Nat.is_pos.

           simpl.
           destruct (Nbar.lt_dec (fin k) (fin st)) as [H₆| H₆].
            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₇| H₇].
             reflexivity.

             exfalso; apply H₇; constructor; apply lt_n_S.
             inversion H₆; assumption.

            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₇| H₇].
             exfalso; apply H₆; constructor; apply lt_S_n.
             inversion H₇; assumption.

             reflexivity.

         rewrite Heqst in H₂.
         contradiction.

       rewrite <- stretch_shift_1_series_distr.
       rewrite shifted_in_stretched; [ rewrite fld_add_0_l | assumption ].
       rewrite shifted_in_stretched; [ reflexivity | assumption ].

      rewrite Z.mul_add_distr_r, Z.mul_1_l.
      rewrite Z.sub_add_distr, Z.sub_diag.
      rewrite Z.add_simpl_l; simpl.
      rewrite series_shift_0.
      destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
       apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
       destruct Hz as (k, Hi).
       subst i.
       rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
       unfold series_head, series_tail; simpl.
       rewrite Heqst; simpl.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       unfold series_nth_fld; simpl.
       rewrite Nat.add_0_r.
       rewrite <- Hc.
       rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.mul_comm, <- Nat.mul_pred_r.
       destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [H₃| H₃].
        remember (c * k)%nat as x.
        rewrite Heqst.
        destruct (Nbar.lt_dec (fin x) inf) as [H₄| H₄].
         subst x.
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          rewrite fld_add_comm, fld_add_0_l.
          destruct (Nbar.lt_dec (fin k) inf) as [H₆| H₆].
           unfold series_nth_fld; simpl.
           destruct (Nbar.lt_dec (fin k) 1) as [H₇| H₇].
            reflexivity.

            exfalso; apply H₇.
            destruct k; [ apply Nbar.lt_0_1 | idtac ].
            apply Nat.nle_gt in H₅.
            exfalso; apply H₅.
            rewrite Nat.mul_comm; simpl.
            apply Nat.le_add_r.

           exfalso; apply H₆; constructor.

          rewrite Nat.mul_comm.
          rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          destruct (Nbar.lt_dec (fin k) ∞) as [H₆| H₆].
           destruct k.
            exfalso; apply H₅; rewrite Nat.mul_0_r.
            subst c; apply Pos2Nat.is_pos.

            apply Nbar.nle_gt in H₃.
            exfalso; apply H₃.
            constructor.
            rewrite Nat.mul_comm; simpl.
            apply Nat.le_add_r.

           exfalso; apply H₆.
           constructor.

         exfalso; apply H₄; constructor.

        rewrite fld_add_0_l.
        destruct k.
         exfalso; apply H₃; rewrite Nat.mul_0_r.
         constructor.
         subst c; apply Pos2Nat.is_pos.

         destruct (Nbar.lt_dec (fin (c * S k)) ∞) as [H₄| H₄].
          destruct (lt_dec (c * S k) c) as [H₅| H₅].
           apply Nat.nle_gt in H₅.
           exfalso; apply H₅.
           rewrite Nat.mul_comm; simpl.
           apply Nat.le_add_r.

           rewrite Nat.mul_comm.
           rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Heqst.
           destruct (Nbar.lt_dec (fin (S k)) ∞) as [H₆| H₆].
            unfold series_nth_fld; simpl.
            destruct (Nbar.lt_dec (fin k) ∞) as [H₇| H₇].
             reflexivity.

             exfalso; apply H₇; constructor.

            exfalso; apply H₆; constructor.

          exfalso; apply H₄; constructor.

       unfold series_head, series_tail; simpl.
       unfold series_nth_fld; simpl.
       unfold series_nth_fld; simpl.
       rewrite Heqst; simpl.
       rewrite Nat.add_0_r.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       destruct (Nbar.lt_dec (fin i) (fin c)) as [H₃| H₃].
        destruct (zerop (i mod c)) as [Hz| Hnz₂].
         rewrite Hz in Hnz.
         exfalso; revert Hnz; apply Nat.lt_irrefl.

         rewrite fld_add_0_l.
         destruct (Nbar.lt_dec (fin i) ∞) as [H₄| H₄].
          destruct (lt_dec i c) as [H₅| H₅].
           reflexivity.

           apply Nbar.fin_lt_mono in H₃.
           contradiction.

          reflexivity.

        rewrite fld_add_0_l.
        destruct (Nbar.lt_dec (fin i) ∞) as [H₄| H₄].
         destruct (lt_dec i c) as [H₅| H₅].
          reflexivity.

          destruct (zerop ((i - c) mod c)) as [H₆| H₆].
           apply Nat.mod_divides in H₆.
            destruct H₆ as (k, Hic).
            rewrite Hic.
            rewrite Nat.mul_comm.
            rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
            apply Nat.nlt_ge in H₅.
            destruct k.
             rewrite Nat.mul_0_r in Hic.
             apply Nat.sub_0_le in Hic.
             apply Nat.le_antisymm in Hic; [ idtac | assumption ].
             rewrite Hic in Hnz.
             destruct i.
              simpl in Hnz.
              exfalso; revert Hnz; apply Nat.lt_irrefl.

              rewrite Nat.mod_same in Hnz.
               exfalso; revert Hnz; apply Nat.lt_irrefl.

               intros H; discriminate H.

             apply Nat.add_sub_eq_nz in Hic.
              rewrite Nat.add_comm in Hic.
              rewrite <- Nat.mul_succ_r in Hic.
              rewrite <- Hic in Hnz.
              rewrite Nat.mul_comm in Hnz.
              rewrite Nat.mod_mul in Hnz.
               exfalso; revert Hnz; apply Nat.lt_irrefl.

               subst c; apply Pos2Nat_ne_0.

              apply Nat.neq_mul_0.
              split; [ idtac | intros H; discriminate H ].
              subst c; apply Pos2Nat_ne_0.

            subst c; apply Pos2Nat_ne_0.

           reflexivity.

         reflexivity.

     clear Hn.
     rewrite Hs₂ in H₂.
     simpl in H₂.
     apply Nbar.nlt_ge in H₂.
     rewrite Hs₁ in H₁.
     simpl in H₁.
     unfold nz_head, nz_tail in H₁.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ].
      destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
      simpl in H₁.
      rewrite Heqst in H₁.
      simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.sub_0_r in H₁.
      rewrite Z.mul_add_distr_r, Z.mul_1_l in H₁.
      rewrite Z.sub_add_distr, Z.sub_diag in H₁.
      rewrite Z.add_simpl_l in H₁; simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.max_r in H₁.
       rewrite <- Nat.mul_succ_l in H₁.
       rewrite Nbar.fin_inj_mul in H₁.
       apply Nbar.nlt_ge in H₂.
       contradiction.

       rewrite Nat.add_comm; apply Nat.le_add_r.

      apply Nbar.nlt_ge in H₂.
      exfalso; apply H₂; constructor.

    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [H₂| H₂].
     subst s₁ s₂.
     simpl in H₁, H₂.
     unfold nz_head, nz_tail in H₁; simpl in H₁.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ].
      destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
      simpl in H₁.
      rewrite Heqst in H₁; simpl in H₁.
      rewrite Nat.add_0_r, Nat.sub_0_r in H₁.
      rewrite Z.mul_add_distr_r, Z.mul_1_l in H₁.
      rewrite Z.sub_add_distr, Z.sub_diag in H₁.
      rewrite Z.add_simpl_l in H₁; simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.max_r in H₁.
       rewrite <- Nat.mul_succ_l in H₁.
       rewrite Nbar.fin_inj_mul in H₁.
       contradiction.

       rewrite Nat.add_comm; apply Nat.le_add_r.

      simpl in H₁.
      rewrite Heqst in H₁; simpl in H₁.
      exfalso; apply H₁; constructor.

     reflexivity.

   rewrite Z.mul_1_r.
   unfold nz_head, nz_tail; simpl.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ]; simpl.
    destruct st as [| st]; [ exfalso; apply Hst; reflexivity | simpl ].
    rewrite Z.min_l; [ reflexivity | idtac ].
    rewrite Z.add_1_r.
    rewrite Z.mul_succ_l.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Pos2Z.is_nonneg.

    rewrite Z.min_l; [ reflexivity | idtac ].
    rewrite Z.add_1_r.
    rewrite Z.mul_succ_l.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Pos2Z.is_nonneg.

   rewrite Pos.mul_1_r.
   unfold nz_head, nz_tail; simpl.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ].
    destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
    reflexivity.

    reflexivity.

 apply first_nonzero_iff in Hn.
 destruct Hn as (Hn, _).
 rewrite Hn in Hzz; [ idtac | apply Nat.lt_0_succ ].
 negation Hzz.

 apply first_nonzero_iff in Hn.
 rewrite Hn in Hzz.
 negation Hzz.
Qed.
*)

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
Lemma ps_cons2 : ∀ nz,
  series_nth_fld fld 0 (nz_terms nz) ≭ zero fld
  → nz_add (nz_head nz) (nz_tail nz) ≈ NonZero nz.
Proof.
intros nz Hznz.
apply ps_cons.
rewrite <- series_nth_add_head_tail; assumption.
Qed.
*)

(* à voir...
Lemma ps_add_cancel_0_0_l : ∀ nz₁ nz₂ nz₃,
  first_nonzero fld (nz_terms_add nz₁ nz₂) = 0%Nbar
  → first_nonzero fld (nz_terms_add nz₁ nz₃) = 0%Nbar
    → NonZero nz₂ ≈ NonZero nz₃
      → nz_add nz₁ nz₂ ≈ nz_add nz₁ nz₃.
Proof.
intros nz₁ nz₂ nz₃ Hn₂ Hn₃ H₂₃.
unfold nz_add; simpl.
rewrite Hn₂, Hn₃.
inversion H₂₃; subst.
constructor 1 with (k₁ := k₁) (k₂ := k₂); simpl.
 inversion H1; subst.
 constructor; intros i.
 unfold nz_terms_add.
 unfold cm_factor, cm; simpl.
 do 2 rewrite stretch_series_add_distr.
 do 4 rewrite stretch_shift_series_distr.
 do 4 rewrite <- stretch_stretch_series.
 do 4 rewrite Pos.mul_comm, stretch_stretch_series.
 rewrite H1.
 do 3 rewrite <- stretch_stretch_series.
 rewrite H3.
 do 4 rewrite <- Z2Nat_inj_mul_pos_r.
 do 4 rewrite Z.mul_sub_distr_r.
 rewrite <- Z.mul_assoc.
 rewrite <- Pos2Z.inj_mul.
 rewrite H3.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 replace (nz_valnum nz₂ * ' nz_comden nz₁ * ' k₁)%Z with
  (nz_valnum nz₃ * ' nz_comden nz₁ * ' k₂)%Z .
  reflexivity.

  rewrite Z.mul_shuffle0, <- H2.
  rewrite Z.mul_shuffle0; reflexivity.

 unfold cm_factor; simpl.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, H3.
 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 replace (nz_valnum nz₂ * ' nz_comden nz₁ * ' k₁)%Z with
  (nz_valnum nz₃ * ' nz_comden nz₁ * ' k₂)%Z .
  reflexivity.

  rewrite <- Z.mul_assoc, Z.mul_comm.
  rewrite Z.mul_shuffle0.
  rewrite <- Z.mul_assoc, <- H2.
  rewrite <- Z.mul_assoc, Z.mul_comm.
  rewrite <- Z.mul_shuffle0, Z.mul_assoc.
  reflexivity.

 unfold cm.
 rewrite <- Pos.mul_assoc, H3, Pos.mul_assoc.
 reflexivity.
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

Lemma first_nonzero_S_tail : ∀ s n,
  first_nonzero fld s = fin (S n)
  → first_nonzero fld (series_tail s) = fin n.
Proof.
intros s n Hn₃.
apply first_nonzero_iff in Hn₃.
apply first_nonzero_iff.
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
    rewrite stretch_series_1.
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

Definition stretch_series_nat n s :=
  {| terms i :=
       if zerop (i mod n) then
         series_nth_fld fld (i / n) s
       else zero fld;
     stop :=
       stop s * fin n |}.

Lemma stretch_series_to_nat : ∀ k s,
  stretch_series fld k s = stretch_series_nat (Pos.to_nat k) s.
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

Lemma stretch_series_tail : ∀ k s,
  stretch_series fld k (series_tail s)
  ≃ series_tail_n (Pos.to_nat k) (stretch_series fld k s).
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
  let s₁ := stretch_series fld (cm_factor nz₁ nz₂) (nz_terms nz₁) in
  {| nz_terms := series_shift fld (Z.to_nat (v₁ - v₂)) s₁;
     nz_valnum := Z.min v₁ v₂;
     nz_comden := cm nz₁ nz₂ |}.

Lemma nz_add_norm : ∀ nz₁ nz₂ v,
  NonZero (build_nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (build_nz_add fld (v * Pos.to_nat (nz_comden nz₁ * nz_comden nz₂))%nat
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
  rewrite <- stretch_series_add_distr.
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
  rewrite <- stretch_series_add_distr.
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
  let s₁ := stretch_series fld (c₂ * c₃) (nz_terms nz₁) in
  {| nz_terms := series_shift fld (Z.to_nat (v₁ - vm)) s₁;
     nz_valnum := vm;
     nz_comden := c₁ * c₂ * c₃ |}.

Lemma nz_add_norm₂ : ∀ nz₁ nz₂ nz₃ v,
  NonZero (build_nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (build_nz_add fld
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
  → NonZero (build_nz_add fld 0 nz₁ nz₂)
    ≈ NonZero (build_nz_add fld n nz₁ nz₃).
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
  do 2 rewrite stretch_series_add_distr.
  do 4 rewrite stretch_shift_series_distr.
  do 4 rewrite <- stretch_stretch_series.
  do 4 rewrite Pos.mul_comm, stretch_stretch_series.
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
  do 8 rewrite <- stretch_stretch_series.
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
   rewrite stretch_stretch_series.
   rewrite <- stretch_shift_series_distr.
   rewrite <- Pos.mul_assoc, H3, Pos.mul_assoc.
   symmetry.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite Pos.mul_comm.
   rewrite stretch_stretch_series.
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
     (stretch_series fld (c₁ * c₃ * k₂ * c₁) (nz_terms nz₂)
      ≃ stretch_series fld (c₁ * c₂ * k₂ * c₁) (nz_terms nz₃)) 
     as H₁.
     assert (c₁ * c₃ * k₂ * c₁ = c₁ * c₂ * k₁ * c₁)%positive as H₁.
      f_equal.
      rewrite <- Pos.mul_assoc, <- H3, Pos.mul_assoc.
      reflexivity.

      rewrite H₁; clear H₁.
      rewrite Pos_mul_shuffle0.
      rewrite stretch_stretch_series, H1, <- stretch_stretch_series.
      rewrite Pos_mul_shuffle0; reflexivity.

     rewrite H₁; clear H₁.
     rewrite Nat.mul_assoc.
     assert (c₁ * c₂ * k₂ * c₁ = c₂ * (c₁ * k₂ * c₁))%positive as H₁.
      rewrite Pos.mul_assoc; f_equal.
      rewrite Pos.mul_assoc; f_equal.
      apply Pos.mul_comm.

      rewrite H₁; clear H₁.
      rewrite stretch_stretch_series.
      rewrite <- stretch_shift_series_distr.
      rewrite <- stretch_series_add_distr.
      rewrite series_add_comm.
      symmetry.
      rewrite series_add_comm.
      rewrite Nat.mul_assoc.
      assert (c₁ * c₃ * k₂ * c₁ = c₃ * (c₁ * k₂ * c₁))%positive as H₁.
       rewrite Pos.mul_assoc; f_equal.
       rewrite Pos.mul_assoc; f_equal.
       apply Pos.mul_comm.

       rewrite H₁; clear H₁.
       rewrite stretch_stretch_series.
       rewrite <- stretch_shift_series_distr.
       rewrite <- stretch_series_add_distr.
       rewrite series_add_comm.
       remember
        (series_add fld
           (series_shift fld (x * Pos.to_nat c₁)
              (stretch_series fld (c₁ * c₃ * k₂) (nz_terms nz₁)))
           (series_shift fld (y * Pos.to_nat c₁)
              (stretch_series fld (c₁ * k₂ * c₁) (nz_terms nz₃)))) as z.
       do 2 rewrite <- Pos.mul_assoc in Heqz.
       subst z.
       rewrite stretch_stretch_series.
       rewrite <- stretch_shift_series_distr.
       rewrite series_add_comm.
       rewrite stretch_stretch_series.
       rewrite <- stretch_shift_series_distr.
       rewrite <- stretch_series_add_distr.
       remember
        (stretch_series fld c₁
           (series_add fld
              (series_shift fld y
                 (stretch_series fld (k₂ * c₁) (nz_terms nz₃)))
              (series_shift fld x
                 (stretch_series fld (c₃ * k₂) (nz_terms nz₁))))) as z.
Focus 1.
aaa.
*)

(*
Lemma ps_add_cancel_l : ∀ ps₁ ps₂ ps₃,
  ps₂ ≈ ps₃
  → ps_add fld ps₁ ps₂ ≈ ps_add fld ps₁ ps₃.
Proof.
intros ps₁ ps₂ ps₃ H₂₃.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ].
  destruct ps₃ as [nz₃| ]; simpl.
   remember (first_nonzero fld (nz_terms_add fld nz₁ nz₂)) as n₂ eqn:Hn₂ .
   symmetry in Hn₂.
   destruct n₂ as [n₂| ].
    revert nz₁ nz₂ nz₃ H₂₃ Hn₂.
    induction n₂; intros.
     remember (first_nonzero fld (nz_terms_add fld nz₁ nz₃)) as n₃ eqn:Hn₃ .
     symmetry in Hn₃.
     destruct n₃ as [n₃| ].
      unfold nz_add.
      rewrite Hn₂, Hn₃.
aaa.
      revert nz₁ nz₂ nz₃ H₂₃ Hn₂ Hn₃.
      induction n₃; intros.
       apply ps_add_cancel_0_0_l; assumption.
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
  NonZero (build_nz_add fld n nz₁ nz₂)
  = ps_add fld (nz_add fld (nz_head nz₁) (nz_tail nz₁)) (Nonzero nz₂).
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

(*
Definition eq_nz nz₁ nz₂ :=
  nz_valnum nz₁ = nz_valnum nz₂ ∧
  nz_comden nz₁ = nz_comden nz₂ ∧
  nz_terms nz₁ ≃ nz_terms nz₂.

Add Parametric Morphism : (@mknz α)
with signature eq_series fld ==> eq ==> eq ==> eq_nz as mknz_morph.
Proof.
aaa.
*)

(*
Definition eq_nz nz₁ nz₂ :=
  nz_valnum nz₁ = nz_valnum nz₂ ∧
  nz_comden nz₁ = nz_comden nz₂ ∧
  nz_terms nz₁ ≃ nz_terms nz₂.

Axiom eq_nz_refl : reflexive _ eq_nz.
Axiom eq_nz_sym : symmetric _ eq_nz.
Axiom eq_nz_trans : transitive _ eq_nz.

Add Parametric Relation : (nz_ps α) eq_nz
 reflexivity proved by eq_nz_refl
 symmetry proved by eq_nz_sym
 transitivity proved by eq_nz_trans
 as eq_nz_rel.

Add Parametric Morphism : (@NonZero α)
with signature eq_nz ==> eq_ps fld as NonZero_morph.
Proof.
aaa.
*)

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
remember (first_nonzero fld s₁ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl.
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
rewrite <- stretch_series_add_distr.
rewrite series_add_neg.
rewrite stretch_series_series_0.
reflexivity.
Qed.

(* just to test... *)
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
rewrite stretch_series_1.
rewrite stretch_series_series_0.
rewrite series_shift_series_0.
rewrite series_add_comm.
rewrite series_add_0_l.
reflexivity.
Qed.

Lemma series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i : nat, series_nth_fld fld i s ≍ zero fld)
  → ∀ i, series_nth_fld fld i (series_shift fld n s) ≍ zero fld.
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

Lemma series_nth_shift_0_series_nth_0 : ∀ s n,
  (∀ i : nat, series_nth_fld fld i (series_shift fld n s) ≍ zero fld)
  → ∀ i, series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite <- series_shift_0; apply H.

 apply IHn; intros j.
 rewrite series_nth_shift_S; apply H.
Qed.

(*
Lemma series_nth_shift_0_P_series_nth_0 : ∀ s n P,
  (∀ i, P i → series_nth_fld fld i (series_shift fld n s) ≍ zero fld)
  → ∀ i, P i
    → series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n P H i Pi.
revert i Pi.
induction n; intros.
 rewrite <- series_shift_0.
 apply H; assumption.

 apply IHn; [ intros j Pj | assumption ].
 rewrite series_nth_shift_S.
aaa.
*)

Lemma normalise_series_add_shift : ∀ s n m k,
  normalise_series (n + m) k (series_shift fld m s)
  ≃ normalise_series n k s.
Proof.
intros s n m k.
unfold normalise_series.
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

Lemma shrink_factor_le : ∀ s n₁ n₂ k,
  first_nonzero fld s (S n₁) = fin n₂
  → shrink_factor fld s n₁ = k
    → (Pos.to_nat k ≤ S n₂)%nat.
Proof.
intros s n₁ n₂ k Hn₂ Hk.
apply shrink_factor_iff in Hk.
rewrite Hn₂ in Hk.
destruct Hk as (Hz, Hnz).
apply Nat.nlt_ge; intros H₁.
assert (S n₂ mod Pos.to_nat k ≠ 0)%nat as H.
 rewrite Nat.mod_small; [ intros H; discriminate H | assumption ].

 apply Hz in H.
 apply first_nonzero_iff in Hn₂.
 destruct Hn₂ as (_, Hn₂).
 apply Hn₂.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 assumption.
Qed.

(* exercice... *)
(* mmm... à voir... not sure it can be proved cause ¬∀ doesn't imply ∃
Lemma shrink_factor_divides : ∀ s n₁ n₂ k,
  first_nonzero fld s (S n₁) = fin n₂
  → shrink_factor fld s n₁ = k
    → (k | S n₂)%nat.
Proof.
intros s n₁ n₂ k Hn₂ Hk.
aaa.
*)

Lemma normalised_series_first_nonzero : ∀ s n k,
  first_nonzero fld s 0 = fin n
  → first_nonzero fld (normalise_series n k s) 0 = fin 0.
Proof.
intros s n k Hn.
apply first_nonzero_iff in Hn.
apply first_nonzero_iff.
simpl in Hn |- *.
destruct Hn as (Hz, Hnz).
split.
 intros i Hi.
 exfalso; revert Hi; apply Nat.nlt_0_r.

 unfold series_nth_fld in Hnz.
 destruct (Nbar.lt_dec (fin n) (stop s)) as [H₁| H₁].
  unfold series_nth_fld.
  remember (normalise_series n k s) as t eqn:Ht .
  destruct (Nbar.lt_dec 0 (stop t)) as [H₂| H₂].
   rewrite Ht; simpl.
   rewrite Nat.add_0_r; assumption.

   apply Nbar.nlt_ge in H₂.
   apply Nbar.le_0_r in H₂.
   rewrite Ht in H₂.
   unfold normalise_series in H₂.
   simpl in H₂.
   destruct (stop s) as [st| ]; [ idtac | discriminate H₂ ].
   simpl in H₂.
   apply Nbar.fin_inj_wd in H₂.
   apply Nbar.fin_lt_mono in H₁.
   remember (st - n)%nat as stn eqn:Hstn .
   symmetry in Hstn.
   destruct stn as [| stn].
    exfalso; revert Hstn; apply Nat.sub_gt; assumption.

    simpl in H₂.
    rewrite Nat.sub_0_r in H₂.
    remember (Pos.to_nat k) as pk.
    remember (stn + pk)%nat as x.
    replace pk with (1 * pk)%nat in Heqx by apply Nat.mul_1_l.
    subst pk x.
    rewrite Nat.div_add in H₂; [ idtac | apply Pos2Nat_ne_0 ].
    apply Nat.eq_add_0 in H₂.
    destruct H₂ as (_, H); discriminate H.

  exfalso; apply Hnz; reflexivity.
Qed.

Definition series_left_shift n (s : series α) :=
  {| terms i := terms s (i + n);
     stop := stop s - fin n |}.

Lemma normalised_stretched_series : ∀ s n k,
  shrink_factor fld s n = k
  → stretch_series fld k (normalise_series n k s) ≃ series_left_shift n s.
Proof.
intros s n k Hsf.
unfold normalise_series.
apply shrink_factor_iff in Hsf.
remember (first_nonzero fld s (S n)) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
destruct n₁ as [n₁| ].
 destruct Hsf as (Hz, Hnz).
 assert (Pos.to_nat k ≠ 0)%nat as Hknz by apply Pos2Nat_ne_0.
 constructor; intros i.
 remember (Nbar.div_sup (stop s - fin n) (fin (Pos.to_nat k))) as x.
 unfold series_nth_fld; simpl.
 unfold series_nth_fld; simpl.
 rewrite Nbar.fold_sub.
 destruct (Nbar.lt_dec (fin i) (x * fin (Pos.to_nat k))) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; [ idtac | assumption ].
    destruct H₃ as (c, H₃).
    rewrite Nat.mul_comm in H₃.
    subst i.
    rewrite Nat.div_mul; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin c) x) as [H₃| H₃].
     rewrite Nat.add_comm; reflexivity.

     exfalso; apply H₃; clear H₃.
     subst x.
     destruct (stop s) as [st| ]; [ idtac | constructor ].
     rewrite Nbar.fin_inj_mul in H₁.
     apply Nbar.lt_mul_r_lt_div_sup; [ idtac | assumption ].
     apply Nbar.lt_fin, Pos2Nat.is_pos.

    assert (i mod Pos.to_nat k ≠ 0)%nat as Hik.
     intros Hik.
     apply Nat.mod_divides in Hik; [ idtac | assumption ].
     destruct Hik as (c, Hi).
     subst i.
     rewrite Nat.mul_comm in H₃.
     rewrite Nat.mod_mul in H₃; [ idtac | assumption ].
     revert H₃; apply Nat.lt_irrefl.

     apply Hz in Hik.
     unfold series_nth_fld in Hik.
     symmetry; rewrite Nat.add_comm.
     destruct (Nbar.lt_dec (fin (n + i)) (stop s)) as [H₄| H₄].
      assumption.

      exfalso; apply H₄.
      simpl in H₂.
      remember (stop s) as st eqn:Hst .
      destruct st as [st| ].
       apply Nbar.lt_fin.
       apply Nbar.fin_lt_mono in H₂.
       apply Nat.add_le_lt_mono with (n := n) (m := n) in H₂.
        rewrite Nat.add_sub_assoc in H₂.
         replace (n + st)%nat with (st + n)%nat in H₂ by apply Nat.add_comm.
         rewrite Nat.add_sub in H₂; assumption.

         destruct (lt_dec st n) as [H₅| H₅].
          subst x.
          simpl in H₁.
          replace (st - n)%nat with O in H₁ by fast_omega H₅.
          simpl in H₁.
          rewrite Nat.div_small in H₁.
           exfalso; revert H₁; apply Nbar.nlt_0_r.

           remember (Pos.to_nat k) as pk.
           destruct pk as [| pk]; [ assumption | idtac ].
           simpl; rewrite Nat.sub_0_r.
           apply Nat.lt_succ_diag_r.

          apply Nat.nlt_ge in H₅; assumption.

        reflexivity.

       constructor.

   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; [ idtac | assumption ].
    destruct H₃ as (c, Hi).
    subst i.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin c) x) as [H₃| H₃].
     subst x.
     apply Nbar.lt_div_sup_lt_mul_r in H₃.
     exfalso; apply H₂.
     rewrite Nat.mul_comm; assumption.

     reflexivity.

    reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃.
     destruct H₃ as (c, Hi).
     subst i.
     rewrite Nat.mul_comm.
     exfalso; apply H₁.
     subst x.
     rewrite Nat.mul_comm.
     rewrite Nbar.fin_inj_mul.
     apply Nbar.mul_lt_mono_pos_r.
      apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

      intros H; discriminate H.

      intros H; discriminate H.

      apply Nbar.lt_mul_r_lt_div_sup.
       apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

       rewrite Nbar.mul_comm.
       assumption.

     assumption.

    assert (i mod Pos.to_nat k ≠ 0)%nat as Hik.
     intros Hik.
     apply Nat.mod_divides in Hik; [ idtac | assumption ].
     destruct Hik as (c, Hi).
     subst i.
     rewrite Nat.mul_comm in H₃.
     rewrite Nat.mod_mul in H₃; [ idtac | assumption ].
     revert H₃; apply Nat.lt_irrefl.

     apply Hz in Hik.
     unfold series_nth_fld in Hik.
     destruct (Nbar.lt_dec (fin (n + i)) (stop s)) as [H₄| H₄].
      symmetry; rewrite Nat.add_comm.
      assumption.

      exfalso; apply H₄; clear H₄.
      destruct (Nbar.lt_dec (stop s) (fin n)) as [H₄| H₄].
       destruct (stop s) as [st| ]; [ idtac | constructor ].
       apply Nbar.fin_lt_mono in H₂.
       apply Nbar.fin_lt_mono.
       apply Nbar.fin_lt_mono in H₄.
       fast_omega H₂ H₄.

       apply Nbar.nlt_ge in H₄.
       destruct (stop s) as [st| ]; [ idtac | constructor ].
       apply Nbar.fin_lt_mono in H₂.
       apply Nbar.fin_lt_mono.
       apply Nbar.fin_le_mono in H₄.
       fast_omega H₂ H₄.

   reflexivity.

 subst k.
 constructor; intros i.
 rewrite stretch_series_1.
 unfold series_nth_fld; simpl.
 destruct (stop s) as [st| ]; simpl.
  rewrite divmod_div, Nat.div_1_r, Nat.add_sub.
  rewrite Nat.mul_1_r, Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_r, Nat.add_comm; reflexivity.
Qed.

Lemma normalised_series : ∀ s n k,
  first_nonzero fld s 0 = fin n
  → shrink_factor fld s n = k
    → series_shift fld n (stretch_series fld k (normalise_series n k s)) ≃ s.
Proof.
intros s n k Hfn Hsf.
rewrite normalised_stretched_series; [ idtac | assumption ].
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.fold_sub.
apply first_nonzero_iff in Hfn; simpl in Hfn.
destruct Hfn as (Hsz, Hsnz).
unfold series_nth_fld in Hsz.
destruct (lt_dec i n) as [H₃| H₃].
 apply Hsz in H₃; simpl in H₃.
 rewrite H₃.
 destruct (Nbar.lt_dec (fin i) (stop s - fin n + fin n)); reflexivity.

 apply Nat.nlt_ge in H₃.
 rewrite Nat.sub_add; [ idtac | assumption ].
 destruct (Nbar.lt_dec (fin n) (stop s)) as [H₁| H₁].
  rewrite Nbar.sub_add; [ reflexivity | idtac ].
  apply Nbar.lt_le_incl; assumption.

  apply Nbar.nlt_ge in H₁.
  replace (stop s - fin n)%Nbar with 0%Nbar ; simpl.
   destruct (Nbar.lt_dec (fin i) (fin n)) as [H₂| H₂].
    apply Nbar.fin_lt_mono in H₂.
    apply Nat.nle_gt in H₂; contradiction.

    destruct (Nbar.lt_dec (fin i) (stop s)) as [H₄| H₄].
     exfalso; apply H₂.
     eapply Nbar.lt_le_trans; eassumption.

     reflexivity.

   destruct (stop s) as [st| ].
    apply Nbar.fin_le_mono in H₁.
    replace (st - n)%nat with O by fast_omega H₁.
    reflexivity.

    inversion H₁.
Qed.

Lemma normalise_nz_add_0_r : ∀ nz,
  normalise_nz fld (nz ∔ nz_zero) ≐ normalise_nz fld nz.
Proof.
(* à nettoyer *)
intros nz.
unfold normalise_nz; simpl.
rewrite nz_add_0_r.
rewrite first_nonzero_shift.
remember (first_nonzero fld (nz_terms nz) 0) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
rewrite Nbar.add_comm.
destruct n₁ as [n₁| ]; [ simpl | reflexivity ].
constructor; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r.
 rewrite nz_add_0_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.add_assoc, Z.add_shuffle0.
 rewrite Z2Nat_id_max, Z.min_comm.
 do 2 f_equal.
  destruct (Z_le_dec (nz_valnum nz) 0) as [H₁| H₁].
   rewrite Z.min_r; [ idtac | assumption ].
   rewrite Z.max_l; [ idtac | assumption ].
   rewrite Z.add_0_r; reflexivity.

   apply Z.nle_gt, Z.lt_le_incl in H₁.
   rewrite Z.min_l; [ idtac | assumption ].
   rewrite Z.max_r; [ idtac | assumption ].
   reflexivity.

  rewrite shrink_factor_shift.
  unfold gcd_nz; simpl.
  unfold nz_valnum_add.
  rewrite Z.mul_1_r.
  rewrite Nat2Z.inj_add.
  rewrite Z.add_assoc.
  rewrite Z.add_shuffle0.
  rewrite <- Z.add_assoc.
  rewrite Z.add_comm.
  unfold cm.
  simpl.
  rewrite Pos.mul_1_r.
  f_equal.
  f_equal.
  unfold pos_abs.
  destruct (nz_valnum nz) as [| p| p].
   simpl.
   rewrite Z.min_id, Z.add_0_r.
   reflexivity.

   simpl.
   rewrite positive_nat_Z; simpl.
   destruct (Z.of_nat n₁) as [| p₁| p₁].
    reflexivity.

    reflexivity.

    destruct (Z.pos_sub p p₁) as [| p₂| p₂].
     reflexivity.

     reflexivity.

     reflexivity.

   simpl.
   destruct (Z.of_nat n₁) as [| p₁| p₁].
    reflexivity.

    reflexivity.

    apply Pos.add_comm.

 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 f_equal.
 f_equal.
 unfold gcd_nz.
 simpl.
 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r.
 rewrite nz_add_0_r.
 rewrite shrink_factor_shift.
 f_equal.
 f_equal.
 f_equal.
 unfold pos_abs.
 rewrite Nat2Z.inj_add.
 destruct (nz_valnum nz) as [| p| p]; simpl.
  rewrite Z.add_0_r; reflexivity.

  destruct (Z.of_nat n₁) as [| p₁| p₁].
   simpl.
   rewrite positive_nat_Z; reflexivity.

   simpl.
   rewrite positive_nat_Z, Pos.add_comm; reflexivity.

   simpl.
   rewrite positive_nat_Z; reflexivity.

  rewrite Z.add_0_r.
  reflexivity.

 rewrite nz_add_0_r.
 rewrite shrink_factor_shift.
 constructor; intros i.
 rewrite normalise_series_add_shift.
 unfold gcd_nz.
 simpl.
 unfold cm; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r, Pos.mul_1_r.
 unfold pos_abs.
 rewrite Nat2Z.inj_add.
 destruct (nz_valnum nz) as [| p| p]; simpl.
  rewrite Z.add_0_r; reflexivity.

  destruct (Z.of_nat n₁) as [| p₁| p₁].
   simpl.
   rewrite positive_nat_Z; reflexivity.

   simpl.
   rewrite positive_nat_Z, Pos.add_comm; reflexivity.

   simpl.
   rewrite positive_nat_Z; reflexivity.

  rewrite Z.add_0_r.
  reflexivity.
Qed.

(* provable but supposes to use Bézout's identity
   probably complicated
Lemma normalised_series_shrink_factor : ∀ s n k,
  first_nonzero fld s 0 = fin n
  → shrink_factor fld s n = k
    → shrink_factor fld (normalise_series n k s) 0 = 1%positive.
Proof.
intros s n k Hn Hk.
aaa.

Lemma normalised_ps_shrink_factor : ∀ nz nz₁,
  normalise_nz fld nz₁ = NonZero nz
  → shrink_factor fld (nz_terms nz) 0 = 1%positive.
Proof.
intros nz nz₁ Hnorm.
aaa.
*)

(* probablement démontrable aussi avec first_nonzero ... = fin 0 comme but
   à voir, peut-être, si nécessaire *)
Lemma first_nonzero_normalised : ∀ nz nz₁ n,
  normalise_nz fld nz₁ = NonZero nz
  → first_nonzero fld (nz_terms nz) 0 = fin n
    → n = O.
Proof.
intros nz nz₁ n Hnorm Hnz.
destruct n as [| n]; [ reflexivity | exfalso ].
apply first_nonzero_iff in Hnz.
simpl in Hnz.
destruct Hnz as (Hz, Hnz).
pose proof (Hz O (Nat.lt_0_succ n)) as H₀.
unfold normalise_nz in Hnorm.
remember (first_nonzero fld (nz_terms nz₁) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; [ idtac | discriminate Hnorm ].
apply first_nonzero_iff in Hm.
simpl in Hm.
destruct Hm as (Hmz, Hmnz).
unfold series_nth_fld in Hmnz.
destruct (Nbar.lt_dec (fin m) (stop (nz_terms nz₁))) as [H₂| H₂].
 injection Hnorm; clear Hnorm; intros; subst nz.
 simpl in Hz, Hnz, H₀.
 unfold series_nth_fld in H₀.
 simpl in H₀.
 rewrite Nbar.fold_sub in H₀.
 rewrite Nbar.fold_sub in H₀.
 rewrite Nbar.fold_div in H₀.
 remember (shrink_factor fld (nz_terms nz₁) m) as k eqn:Hk .
 symmetry in Hk.
 remember (gcd_nz m k nz₁) as g eqn:Hg .
 remember (stop (nz_terms nz₁) - fin m + fin (Pos.to_nat g) - 1)%Nbar as x.
 symmetry in Heqx.
 rewrite Nat.add_0_r in H₀.
 destruct (Nbar.lt_dec 0 (x / fin (Pos.to_nat g))) as [H₁| H₁].
  rewrite H₀ in Hmnz; apply Hmnz; reflexivity.

  remember (stop (nz_terms nz₁) - fin m)%Nbar as y.
  symmetry in Heqy.
  destruct y as [y| ].
   destruct y as [| y].
    revert Heqy; apply Nbar.sub_gt; assumption.

    simpl in Heqx.
    rewrite Nat.sub_0_r in Heqx.
    apply H₁.
    rewrite <- Heqx; simpl.
    remember (y + Pos.to_nat g)%nat as z.
    replace (Pos.to_nat g) with (1 * Pos.to_nat g)%nat in Heqz .
     subst z.
     rewrite Nat.div_add.
      apply Nbar.lt_fin.
      rewrite Nat.add_comm.
      apply Nat.lt_0_succ.

      apply Pos2Nat_ne_0.

     rewrite Nat.mul_1_l; reflexivity.

   subst x; simpl.
   apply H₁; simpl.
   constructor.

 apply Hmnz; reflexivity.
Qed.

Lemma nz_norm_add_0 : ∀ nz₁ nz₂,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → normalise_nz fld (nz₁ ∔ nz_zero) ≐ normalise_nz fld (nz₂ ∔ nz_zero).
Proof.
intros nz₁ nz₂ Heq.
rewrite normalise_nz_add_0_r.
rewrite normalise_nz_add_0_r.
assumption.
Qed.

(* une idée, comme ça... mais qui marche ! *)
Lemma normalised_nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → (normalise_nz fld nz₁ + normalise_nz fld nz₃ ≈
     normalise_nz fld nz₂ + normalise_nz fld nz₃)%ps.
Proof.
(* à nettoyer sérieusement *)
intros nz₁ nz₂ nz₃ Heqp.
remember (normalise_nz fld nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz fld nz₂) as ps₂ eqn:Hps₂ .
remember (normalise_nz fld nz₃) as ps₃ eqn:Hps₃ .
symmetry in Hps₁, Hps₂, Hps₃.
destruct ps₃ as [nz'₃| ].
 destruct ps₁ as [nz'₁| ].
  destruct ps₂ as [nz'₂| ].
   simpl.
   constructor.
   inversion Heqp.
   clear nz₁0 H.
   clear nz₂0 H0.
   unfold normalise_nz.
   simpl.
   remember (first_nonzero fld (nz_terms_add nz'₁ nz'₃) 0) as n₁ eqn:Hn₁ .
   remember (first_nonzero fld (nz_terms_add nz'₂ nz'₃) 0) as n₂ eqn:Hn₂ .
   symmetry in Hn₁, Hn₂.
   unfold nz_terms_add in Hn₁.
   unfold nz_terms_add in Hn₂.
   unfold cm_factor in Hn₁.
   unfold cm_factor in Hn₂.
   rewrite H1, H2 in Hn₁.
   unfold adjust_series in Hn₁, Hn₂.
   rewrite H3 in Hn₁.
   rewrite Hn₁ in Hn₂.
   move Hn₂ at top; subst n₁.
   destruct n₂ as [n₂| ].
    constructor; simpl.
     unfold nz_valnum_add, gcd_nz; simpl.
     unfold nz_valnum_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H1, H2.
     f_equal.
     f_equal.
     f_equal.
     unfold nz_terms_add.
     unfold cm_factor; simpl.
     rewrite H1, H2.
     unfold adjust_series.
     rewrite H3.
     reflexivity.

     unfold cm; simpl.
     unfold nz_terms_add; simpl.
     unfold cm_factor; simpl.
     rewrite H1, H2.
     unfold adjust_series; simpl.
     rewrite H3.
     f_equal.
     f_equal.
     f_equal.
     unfold gcd_nz.
     simpl.
     unfold nz_valnum_add; simpl.
     rewrite H1.
     unfold cm_factor.
     unfold cm.
     rewrite H2.
     reflexivity.

     unfold gcd_nz; simpl.
     unfold nz_valnum_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H1.
     rewrite H2.
     unfold nz_terms_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H1.
     rewrite H2.
     constructor; simpl.
     unfold adjust_series; simpl.
     intros i.
     rewrite H3 in |- * at 1.
     rewrite H3 in |- * at 1.
     reflexivity.

    constructor.

   simpl.
   constructor.
   unfold normalise_nz.
   simpl.
   inversion Heqp.

  inversion Heqp.
  reflexivity.

 inversion Heqp.
  simpl.
  constructor.
  unfold normalise_nz; simpl.
  rewrite H1.
  remember (first_nonzero fld (nz_terms nz₂0) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | reflexivity ].
  constructor; simpl.
   rewrite H1.
   rewrite H.
   unfold gcd_nz.
   rewrite H0.
   rewrite H.
   reflexivity.

   rewrite H0.
   rewrite H1.
   unfold gcd_nz.
   rewrite H0.
   rewrite H.
   reflexivity.

   unfold gcd_nz.
   rewrite H, H0, H1.
   reflexivity.

  reflexivity.
Qed.

(*
Lemma www : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → nz_valnum_add nz₁ nz₃ = nz_valnum_add nz₂ nz₃.
Proof.
intros nz₁ nz₂ nz₃ Heq.
unfold nz_valnum_add.
unfold cm_factor.
unfold normalise_nz in Heq.
remember (first_nonzero fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
remember (first_nonzero fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
destruct n₁ as [n₁| ].
 destruct n₂ as [n₂| ].
  inversion_clear Heq; simpl in *.
  unfold gcd_nz in H.
bbb.
*)

Definition normalise_ps ps :=
  match ps with
  | NonZero nz => normalise_nz fld nz
  | Zero => Zero _
  end.

Lemma series_nth_normalised : ∀ s n g,
  first_nonzero fld s 0 = fin n
  → ∀ i,
    series_nth_fld fld i (normalise_series n g s) =
    series_nth_fld fld (n + i * Pos.to_nat g) s.
Proof.
intros s n g Hn i.
unfold series_nth_fld; simpl.
do 2 rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
remember (Pos.to_nat g) as gn eqn:Hgn .
remember ((stop s - fin n + fin gn - 1) / fin gn)%Nbar as x.
remember (fin (n + i * gn)) as y.
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁].
 destruct (Nbar.lt_dec y (stop s)) as [H₂| H₂]; [ reflexivity | exfalso ].
 subst x y gn.
 apply H₂; clear H₂.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ]; [ idtac | constructor ].
 simpl in H₁.
 apply Nbar.fin_lt_mono in H₁.
 apply Nbar.fin_lt_mono.
 rewrite Nat_fold_div_sup in H₁.
 apply Nat_lt_div_sup_lt_mul_r in H₁.
 apply Nat.lt_add_lt_sub_l; assumption.

 destruct (Nbar.lt_dec y (stop s)) as [H₂| H₂]; [ exfalso | reflexivity ].
 subst x y gn.
 apply H₁; clear H₁.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ]; [ simpl | constructor ].
 apply Nbar.fin_lt_mono in H₂.
 apply Nbar.fin_lt_mono.
 rewrite Nat_fold_div_sup.
 apply Nat_lt_mul_r_lt_div_sup; [ apply Pos2Nat.is_pos | idtac ].
 apply Nat.lt_add_lt_sub_l; assumption.
Qed.

(* peut-être pas nécessaire... *)
Lemma series_nth_normalised₁ : ∀ nz nz' n k g,
  normalise_nz fld nz = NonZero nz'
  → first_nonzero fld (nz_terms nz) 0 = fin n
    → shrink_factor fld (nz_terms nz) n = k
      → gcd_nz n k nz = g
        → ∀ i,
          series_nth_fld fld i (nz_terms nz') =
          series_nth_fld fld (n + i * Pos.to_nat g) (nz_terms nz).
Proof.
intros nz nz' n k g Heq Hn Hk Hg i.
unfold normalise_nz in Heq.
rewrite Hn in Heq.
injection Heq; clear Heq; intros Heq; subst nz'; simpl.
rewrite Hk, Hg.
eapply series_nth_normalised; assumption.
Qed.

(* pas mieux que sans liste... l'induction par n déconne...
Fixpoint nonzero_list s b n :=
  match first_nonzero fld s b with
  | fin m =>
      match n with
      | O => [m]
      | S n' => [m … nonzero_list s (S m) n']
      end
  | ∞ => []
  end.

Lemma sss : ∀ nz nz' n zl zl',
  normalise_nz fld nz = NonZero nz'
  → zl = nonzero_list (nz_terms nz) 0 n
    → zl' = nonzero_list (nz_terms nz') 0 n
      → List.map (λ i, series_nth_fld fld i (nz_terms nz)) zl =
        List.map (λ i, series_nth_fld fld i (nz_terms nz')) zl'.
Proof.
intros nz nz' n zl zl' Heq Hzl Hzl'.
subst zl zl'.
induction n as [| n]; simpl.
 remember (first_nonzero fld (nz_terms nz) 0) as i eqn:Hi .
 remember (first_nonzero fld (nz_terms nz') 0) as j eqn:Hj .
 symmetry in Hi, Hj.
 destruct i as [i| ].
  destruct j as [j| ]; [ simpl | exfalso ].
   f_equal.
   erewrite series_nth_normalised with (nz' := nz'); eauto .
   eapply first_nonzero_normalised in Heq; [ idtac | eassumption ].
   subst j; rewrite Nat.mul_0_l, Nat.add_0_r; reflexivity.

   eapply series_nth_normalised with (i := O) in Heq; eauto .
   rewrite Nat.mul_0_l, Nat.add_0_r in Heq.
   apply first_nonzero_iff in Hi; simpl in Hi.
   apply first_nonzero_iff in Hj; simpl in Hj.
   destruct Hi as (Hz, Hnz).
   apply Hnz.
   rewrite <- Heq.
   apply Hj; reflexivity.

  destruct j as [j| ]; [ exfalso | reflexivity ].
  unfold normalise_nz in Heq.
  rewrite Hi in Heq; discriminate Heq.
bbb.
*)

Fixpoint nth_nonzero s b n :=
  match n with
  | O => first_nonzero fld s b
  | S n' =>
      match first_nonzero fld s b with
      | fin m => nth_nonzero s (S m) n'
      | ∞ => ∞
      end
  end.

(*
Lemma ttt : ∀ nz nz' n i j,
  normalise_nz fld nz = NonZero nz'
  → nth_nonzero (nz_terms nz) 0 n = fin i
    → nth_nonzero (nz_terms nz') 0 n = fin j
      → series_nth_fld fld i (nz_terms nz) =
        series_nth_fld fld j (nz_terms nz').
Proof.
intros nz nz' n i j Heq Hi Hj.
revert i j Hi Hj.
induction n; intros.
 erewrite series_nth_normalised with (nz' := nz'); eauto .
 eapply first_nonzero_normalised in Heq; [ idtac | eassumption ].
 subst j; rewrite Nat.mul_0_l, Nat.add_0_r; reflexivity.

 simpl in Hi, Hj.
 remember (first_nonzero fld (nz_terms nz) 0) as m eqn:Hm .
 remember (first_nonzero fld (nz_terms nz') 0) as m' eqn:Hm' .
 symmetry in Hm, Hm'.
 destruct m as [m| ]; [ idtac | discriminate Hi ].
 destruct m' as [m'| ]; [ idtac | discriminate Hj ].
 destruct n as [| n].
  simpl in Hi, Hj.
  erewrite series_nth_normalised with (nz' := nz'); eauto .

bbb.
*)

(*
Lemma uuu : ∀ nz nz' n m p k g,
  normalise_nz fld nz = NonZero nz'
  → first_nonzero fld (nz_terms nz) 0 = fin n
    → first_nonzero fld (nz_terms nz) (S n) = fin p
      → first_nonzero fld (nz_terms nz') 1 = fin m
       → shrink_factor fld (nz_terms nz) n = k
         → gcd_nz n k nz = g
           → S p = (S m * Pos.to_nat g)%nat.
Proof.
intros nz nz' n m p k g Heq Hn Hp Hm Hk Hg.
destruct (lt_dec (S p) (S m * Pos.to_nat g)) as [H₁| H₁].
 exfalso.
bbb.
*)

Lemma normalised_shrink_factor : ∀ nz n k g,
  first_nonzero fld (nz_terms nz) 0 = fin n
  → shrink_factor fld (nz_terms nz) n = k
    → gcd_nz n k nz = g
      → shrink_factor fld (normalise_series n g (nz_terms nz)) 0 =
          Pos.of_nat (Pos.to_nat k / Pos.to_nat g).
Proof.
intros nz n k g Hn Hk Hg.
unfold gcd_nz in Hg.
remember (pos_abs (nz_valnum nz + Z.of_nat n)) as vn eqn:Hvn .
pose proof (Pos.gcd_divide_r (Pos.gcd vn (nz_comden nz)) k) as H.
rewrite Hg in H.
destruct H as (k', Hk').
apply shrink_factor_iff.
remember (normalise_series n g (nz_terms nz)) as s eqn:Hs .
remember (first_nonzero fld s 1) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl.
 split.
  intros i H.
  rewrite Nat2Pos.id in H.
   rewrite Hs.
   rewrite series_nth_normalised; [ idtac | assumption ].
   apply shrink_factor_iff in Hk.
   remember (first_nonzero fld (nz_terms nz) (S n)) as p eqn:Hp .
   symmetry in Hp.
   destruct p as [p| ].
    destruct Hk as (Hz, Hnz).
    apply Hz.
    intros H₁; apply H; clear H.
    rewrite Hk' in H₁ |- *.
    rewrite Pos2Nat.inj_mul.
    rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
    rewrite Pos2Nat.inj_mul in H₁.
    rewrite Nat.mul_mod_distr_r in H₁; try apply Pos2Nat_ne_0.
    apply Nat.mul_eq_0_l in H₁; [ assumption | apply Pos2Nat_ne_0 ].

    subst k.
    symmetry in Hk'.
    apply Pos.mul_eq_1_r in Hk'.
    move Hk' at top; subst g.
    exfalso; apply H; reflexivity.

   rewrite Hk'.
   rewrite Pos2Nat.inj_mul.
   rewrite Nat.div_mul; apply Pos2Nat_ne_0.

  intros k₁ Hk₁.
  rewrite Nat2Pos.id in Hk₁.
   rewrite Hk' in Hk₁.
   rewrite Pos2Nat.inj_mul in Hk₁.
   rewrite Nat.div_mul in Hk₁.
    apply shrink_factor_iff in Hk.
    remember (first_nonzero fld (nz_terms nz) (S n)) as p eqn:Hp .
    symmetry in Hp.
    destruct p as [p| ].
     destruct Hk as (Hz, Hnz).
     apply Nat.mul_lt_mono_pos_r with (p := Pos.to_nat g) in Hk₁.
      rewrite <- Pos2Nat.inj_mul, <- Hk' in Hk₁.
      apply Hnz in Hk₁.
      destruct Hk₁ as (j, (Hjm, Hjn)).
      destruct (zerop (j mod Pos.to_nat g)) as [H₁| H₁].
       apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
       destruct H₁ as (j', Hj').
       subst j.
       rewrite Nat.mul_comm in Hjn.
       rewrite <- series_nth_normalised in Hjn; [ idtac | assumption ].
       rewrite <- Hs in Hjn.
       rewrite Nat.mul_comm in Hjm.
       destruct k₁ as [| k₁]; [ exfalso; apply Hjm; reflexivity | idtac ].
       rewrite Nat.mul_mod_distr_r in Hjm.
        apply Nat.neq_mul_0 in Hjm.
        destruct Hjm as (Hjk, Hgz).
        exists j'; split; assumption.

        intros H; discriminate H.

        apply Pos2Nat_ne_0.

       assert (j mod Pos.to_nat k ≠ 0)%nat as H₂.
        intros H.
        apply Nat.mod_divides in H; [ idtac | apply Pos2Nat_ne_0 ].
        destruct H as (j', Hj'); subst j.
        rewrite Hk' in H₁.
        rewrite Pos2Nat.inj_mul, Nat.mul_shuffle0 in H₁.
        rewrite Nat.mod_mul in H₁; [ idtac | apply Pos2Nat_ne_0 ].
        revert H₁; apply Nat.lt_irrefl.

        exfalso; apply Hjn, Hz; assumption.

      apply Pos2Nat.is_pos.

     subst k.
     symmetry in Hk'.
     apply Pos.mul_eq_1_r in Hk'.
     move Hk' at top; subst g.
     exfalso.
     apply first_nonzero_iff in Hm.
     destruct Hm as (Hz, Hnz).
     apply Hnz; simpl.
     rewrite Hs.
     rewrite series_nth_normalised; [ idtac | assumption ].
     apply first_nonzero_iff in Hp.
     rewrite Nat.mul_1_r.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l.
     apply Hp.

    apply Pos2Nat_ne_0.

   rewrite Hk'.
   rewrite Pos2Nat.inj_mul.
   rewrite Nat.div_mul; apply Pos2Nat_ne_0.

 apply shrink_factor_iff in Hk.
 remember (first_nonzero fld (nz_terms nz) (S n)) as p eqn:Hp .
 symmetry in Hp.
 destruct p as [p| ].
  apply first_nonzero_iff in Hm; simpl in Hm.
  apply first_nonzero_iff in Hp; simpl in Hp.
  destruct Hp as (Hz, Hnz).
  rewrite <- Nat.add_succ_r in Hnz.
  destruct (zerop (S p mod Pos.to_nat k)) as [H₁| H₁].
   apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H₁ as (p', Hp').
   rewrite Hp' in Hnz.
   exfalso; apply Hnz.
   rewrite Nat.mul_comm.
   rewrite Hk'.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite <- series_nth_normalised; [ idtac | assumption ].
   rewrite <- Hs.
   remember (p' * Pos.to_nat k')%nat as pk eqn:Hpk .
   symmetry in Hpk.
   destruct pk as [| pk].
    apply Nat.mul_eq_0_l in Hpk; [ idtac | apply Pos2Nat_ne_0 ].
    subst p'.
    rewrite Nat.mul_0_r in Hp'; discriminate Hp'.

    apply Hm.

   destruct Hk as (Hz₁, Hnz₁).
   rewrite Hz₁ in Hnz.
    exfalso; apply Hnz; reflexivity.

    intros H.
    rewrite H in H₁.
    revert H₁; apply Nat.lt_irrefl.

  subst k.
  symmetry in Hk'.
  apply Pos.mul_eq_1_r in Hk'.
  rewrite Hk'; reflexivity.
Qed.

Lemma vvv : ∀ x y, pos_abs (x / y) = Z.to_pos (' pos_abs x / y).
Proof.
intros x y.
unfold pos_abs.
destruct x as [| x| x]; simpl.
 destruct y as [| y| y].
  reflexivity.

  destruct (Pos.eq_dec y 1) as [H₁| H₁].
   subst y.
   reflexivity.

   rewrite Z.div_small; [ reflexivity | idtac ].
   split; [ apply Z.le_0_1 | idtac ].
   apply Pos.succ_pred in H₁.
   rewrite <- H₁; simpl.
   apply Pos.le_succ_l; simpl.
   replace 2%positive with (Pos.succ 1) by reflexivity.
   apply -> Pos.succ_le_mono.
   apply Pos.le_1_l.

bbb.
  symmetry.
  apply Z2Pos.to_pos_nonpos.
  rewrite <- Pos2Z.opp_pos.

Lemma www : ∀ ps, normalise_ps (normalise_ps ps) ≈ normalise_ps ps.
Proof.
intros ps.
destruct ps as [nz| ]; [ simpl | reflexivity ].
remember (normalise_nz fld nz) as ps eqn:Hps .
rewrite Hps in |- * at 2.
symmetry in Hps.
destruct ps as [nz'| ]; simpl.
 unfold normalise_nz; simpl.
 remember (first_nonzero fld (nz_terms nz') 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ].
  eapply first_nonzero_normalised in Hn; [ idtac | eassumption ].
  subst n; simpl.
  rewrite Z.add_0_r.
  remember (first_nonzero fld (nz_terms nz) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ].
   constructor; simpl.
   unfold normalise_nz in Hps.
   rewrite Hn in Hps.
   injection Hps; clear Hps; intros; subst nz'; simpl.
   remember (shrink_factor fld (nz_terms nz) n) as k eqn:Hk .
   remember (gcd_nz n k nz) as g eqn:Hg .
   remember (normalise_series n g (nz_terms nz)) as s eqn:Hs .
   remember (shrink_factor fld s 0) as k₁ eqn:Hk₁ .
   unfold gcd_nz; simpl.
   rewrite Z.add_0_r.
   remember (nz_valnum nz + Z.of_nat n)%Z as vn eqn:Hvn .
   remember (Z.to_pos (' nz_comden nz / ' g)) as cg eqn:Hcg .
   remember (Pos.gcd (Pos.gcd (pos_abs (vn / ' g)) cg) k₁) as g₁ eqn:Hg₁ .
   unfold normalise_nz; simpl.
   remember (first_nonzero fld s 0) as m eqn:Hm .
   rewrite Hs in Hm.
   rewrite normalised_series_first_nonzero in Hm; [ idtac | assumption ].
   subst m.
   rewrite normalised_series_first_nonzero.
    constructor; simpl.
     Focus 1.
     do 2 rewrite Z.add_0_r.
     unfold gcd_nz; simpl.
     do 2 rewrite Z.add_0_r.
     rewrite Hs in Hk₁.
     symmetry in Hk, Hg.
     erewrite normalised_shrink_factor in Hk₁; try eassumption.
     remember (Pos.gcd (pos_abs (vn / ' g)) cg) as g₂ eqn:Hg₂ .
     rewrite Hcg in Hg₂.
     symmetry in Hg.
     unfold gcd_nz in Hg.
     rewrite <- Hvn in Hg.
     remember (Pos.gcd (pos_abs vn) (nz_comden nz)) as g₃ eqn:Hg₃ .
     move Hg₂ at bottom.
     move Hg₃ at bottom.
(* faut prouver que g₁ = 1 *)
bbb.
Z.gcd_div_gcd:
  ∀ a b g : Z, g ≠ 0%Z → g = Z.gcd a b → Z.gcd (a / g) (b / g) = 1%Z

Lemma nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → normalise_nz fld (nz₁ ∔ nz₃) ≐ normalise_nz fld (nz₂ ∔ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
bbb.
unfold normalise_nz; simpl.
remember (first_nonzero fld (nz_terms_add nz₁ nz₃) 0) as n₁₃ eqn:Hn₁₃ .
remember (first_nonzero fld (nz_terms_add nz₂ nz₃) 0) as n₂₃ eqn:Hn₂₃ .
symmetry in Hn₁₃, Hn₂₃.
apply first_nonzero_iff in Hn₁₃.
apply first_nonzero_iff in Hn₂₃.
simpl in Hn₁₃, Hn₂₃.
destruct n₁₃ as [n₁₃| ]; simpl.
 destruct n₂₃ as [n₂₃| ]; simpl.
  constructor; simpl.
   unfold normalise_nz in Heq; simpl in Heq.
   remember (first_nonzero fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
   remember (first_nonzero fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
   symmetry in Hn₁, Hn₂.
   apply first_nonzero_iff in Hn₁.
   apply first_nonzero_iff in Hn₂.
   simpl in Hn₁, Hn₂.
   destruct n₁ as [n₁| ]; simpl.
    destruct n₂ as [n₂| ]; simpl.
     inversion_clear Heq; simpl in *.
     Focus 1.
bbb.

intros nz₁ nz₂ nz₃ Heq.
unfold normalise_nz in Heq; simpl in Heq.
remember (first_nonzero fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
remember (first_nonzero fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
destruct n₁ as [n₁| ].
 destruct n₂ as [n₂| ].
  inversion_clear Heq; simpl in *.
  remember (shrink_factor fld (nz_terms nz₁) n₁) as k₁ eqn:Hk₁ .
  remember (shrink_factor fld (nz_terms nz₂) n₂) as k₂ eqn:Hk₂ .
  symmetry in Hk₁, Hk₂.
  apply shrink_factor_iff in Hk₁.
  apply shrink_factor_iff in Hk₂.
  remember (first_nonzero fld (nz_terms nz₁) (S n₁)) as sn₁ eqn:Hsn₁ .
  remember (first_nonzero fld (nz_terms nz₂) (S n₂)) as sn₂ eqn:Hsn₂ .
  symmetry in Hsn₁, Hsn₂.
  destruct sn₁ as [sn₁| ].
   destruct sn₂ as [sn₂| ].
    destruct Hk₁ as [Hk₁| Hk₁].
     destruct Hk₂ as [Hk₂| Hk₂].
      unfold normalise_nz.
      remember (first_nonzero fld (nz_terms (nz₁ ∔ nz₃)) 0) as n₁₃ eqn:Hn₁₃ .
      remember (first_nonzero fld (nz_terms (nz₂ ∔ nz₃)) 0) as n₂₃ eqn:Hn₂₃ .
      symmetry in Hn₁₃, Hn₂₃.
      simpl in Hn₁₃, Hn₂₃ |- *.
      destruct n₁₃ as [n₁₃| ].
       destruct n₂₃ as [n₂₃| ].
        constructor; simpl.
         unfold cm_factor.
Focus 1.
bbb.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
    destruct k₁₃ as [k₁₃| ].
     apply shrink_factor_iff in Hk₁₃.
     rewrite Hn₁₃ in Hk₁₃.
     destruct Hk₁₃ as (Hk, _).
     exfalso; apply Hk; reflexivity.

     destruct k₂₃ as [k₂₃| ].
      apply shrink_factor_iff in Hk₂₃.
      rewrite Hn₂₃ in Hk₂₃.
      destruct Hk₂₃ as (Hk, _).
      exfalso; apply Hk; reflexivity.

      constructor; [ simpl | simpl | idtac ].
       unfold cm_factor.
    Focus 1.
bbb.
  destruct k₁ as [| k₁]; [ discriminate Hk₁ | idtac ].
  destruct k₂ as [| k₂]; [ discriminate Hk₂ | idtac ].
  unfold normalise_nz; simpl.
  remember (first_nonzero fld (nz_terms_add nz₁ nz₃)) as n₁₃ eqn:Hn₁₃ .
  remember (first_nonzero fld (nz_terms_add nz₂ nz₃)) as n₂₃ eqn:Hn₂₃ .
  symmetry in Hn₁₃, Hn₂₃.
  destruct n₁₃ as [n₁₃| ].
    destruct n₂₃ as [n₂₃| ].
    constructor; simpl.
     Focus 1.
     unfold cm_factor; simpl.
     remember (shrink_factor fld (nz_terms_add nz₁ nz₃)) as k₁₃.
     remember (shrink_factor fld (nz_terms_add nz₂ nz₃)) as k₂₃.
     rename Heqk₁₃ into Hk₁₃.
     rename Heqk₂₃ into Hk₂₃.
     symmetry in Hk₁₃, Hk₂₃.
     apply shrink_factor_iff in Hk₁₃.
     apply shrink_factor_iff in Hk₂₃.
     rewrite Hn₁₃ in Hk₁₃.
     rewrite Hn₂₃ in Hk₂₃.
     destruct k₁₃ as [| k₁₃]; [ discriminate Hk₁₃ | idtac ].
     destruct k₂₃ as [| k₂₃]; [ discriminate Hk₂₃ | idtac ].
bbb.
*)
(*
     assert (nz₃ = nz_zero).
      Focus 2.
      subst nz₃; simpl.
      rewrite nz_add_0_r in Hn₁₃.
      rewrite nz_add_0_r in Hn₂₃.
      rewrite first_nonzero_shift in Hn₁₃.
      rewrite first_nonzero_shift in Hn₂₃.
      do 2 rewrite Z.mul_1_r.
      rewrite Hn₁ in Hn₁₃.
      rewrite Hn₂ in Hn₂₃.
      simpl in Hn₁₃, Hn₂₃.
      injection Hn₁₃; clear Hn₁₃; intros Hn₁₃.
      injection Hn₂₃; clear Hn₂₃; intros Hn₂₃.
      rewrite <- Hn₁₃, <- Hn₂₃.
      do 2 rewrite Nat2Z.inj_add.
      do 2 rewrite Z2Nat_id_max.
*)

Lemma ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → ps_add ps₁ ps₃ ≈ ps_add ps₂ ps₃.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
unfold ps_add.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ].
  destruct ps₃ as [nz₃| ].
   constructor.
   inversion_clear H₁₂.
bbb.

intros ps₁ ps₂ ps₃ H₂₃.
unfold ps_add.
inversion H₂₃ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| a b H₂ H₃]; subst.
 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ].
  destruct v₃ as [v₃| ]; [ idtac | discriminate Hvv₂ ].
  unfold ps_add_nz, cm_factor; simpl.
  rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
  constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
   do 2 rewrite stretch_series_add_distr.
   do 4 rewrite stretch_shift_series_distr.
   do 4 rewrite <- stretch_stretch_series.
   do 4 rewrite Nat.mul_sub_distr_r.
   do 4 rewrite <- Z2Nat_inj_mul_pos_r.
   do 4 rewrite <- Z.mul_assoc; simpl.
   rewrite Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Hck₂.
   replace (k₂₁ * nz_comden ps₁)%positive with
    (nz_comden ps₁ * k₂₁)%positive by apply Pos.mul_comm.
   do 2 rewrite stretch_stretch_series.
   rewrite Hss₂.
   do 2 rewrite <- stretch_stretch_series.
   replace (nz_comden ps₁ * k₂₂)%positive with
    (k₂₂ * nz_comden ps₁)%positive by apply Pos.mul_comm.
   replace (v₂ * ' (nz_comden ps₁ * k₂₁))%Z with
    (v₃ * ' (k₂₂ * nz_comden ps₁))%Z .
    reflexivity.

    do 2 rewrite Pos2Z.inj_mul.
    do 2 rewrite Z.mul_assoc.
    symmetry; rewrite Z.mul_shuffle0.
    apply Z.mul_cancel_r; [ apply Zpos_ne_0 | idtac ].
    inversion Hvv₂; subst.
    reflexivity.

   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   simpl in Hvv₂.
   do 2 f_equal.
    do 2 rewrite <- Z.mul_assoc; simpl.
    rewrite Hck₂; reflexivity.

    rewrite Z.mul_shuffle0.
    injection Hvv₂; clear Hvv₂; intros Hvv₂; rewrite Hvv₂.
    rewrite Z.mul_shuffle0; reflexivity.

   rewrite <- Pos.mul_assoc, Hck₂, Pos.mul_assoc.
   reflexivity.

  destruct v₃ as [v₃| ]; [ discriminate Hvv₂ | reflexivity ].

 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ]; simpl.
  destruct H₂ as [H₂| H₂]; [ idtac | discriminate H₂ ].
  destruct v₃ as [v₃| ]; simpl.
   destruct H₃ as [H₃| H₃]; [ idtac | discriminate H₃ ].
   unfold build_ps; simpl.
   rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
   Focus 1.
bbb.

intros ps₁ ps₃ ps₄ H.
inversion H as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
  do 4 rewrite Z2Nat_inj_mul_pos_r.
  remember (nz_valnum nz₁) as v₁.
  remember (nz_comden nz₁) as c₁.
  remember (nz_comden nz₂₁) as c₂₁.
  remember (nz_comden nz₂₂) as c₂₂.
  remember (nz_valnum nz₂₁) as v₂₁.
  remember (nz_valnum nz₂₂) as v₂₂.
  do 2 rewrite stretch_series_add_distr.
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
-- à nettoyer
  rewrite Nat.mul_sub_distr_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Pos2Nat.inj_mul.
  rewrite Hck₂.
  rewrite Nat.mul_shuffle0.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Hvv₂.
  rewrite Pos2Z.inj_mul.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_assoc.
  remember (v₁ * ' c₂₂ * ' k₂₂)%Z as vck eqn:Hvck .
  remember (v₂₂ * ' k₂₂ * ' c₁)%Z as vkc eqn:Hvkc .
  rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_shuffle0.
  rewrite Hvv₂.
  rewrite <- Hvkc.
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  rewrite <- Hvck.
  do 2 rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Hvck.
  rewrite Z.mul_shuffle0.
  rewrite <- Hvkc.
  do 4 rewrite <- Pos2Nat.inj_mul.
  rewrite Pos.mul_comm.
  rewrite Hck₂.
  rewrite Pos.mul_comm.
  rewrite series_add_comm.
  rewrite Pos2Nat.inj_mul.
  rewrite Nat.mul_comm.
  rewrite stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite Hss₂.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite Nat.mul_comm.
  rewrite <- Pos2Nat.inj_mul.
  rewrite series_add_comm.
  reflexivity.

  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Z.mul_shuffle0, Hvv₂.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  rewrite Z.min_comm, Z.mul_shuffle0, Z.min_comm.
  reflexivity.

  do 2 rewrite <- Pos.mul_assoc.
  apply Pos.mul_cancel_l.
  assumption.

 reflexivity.
Qed.
*)

Theorem ps_mul_ident : ∀ ps, ps_mul fld ps_one ps ≈ ps.
Proof.
intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
apply eq_non_zero_ps with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite stretch_series_1.
rewrite stretch_series_1 in |- * at 2.
apply eq_series_base; simpl.
bbb.
 intros i.
 destruct i; simpl.
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [H| H].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   destruct st as [st| ]; simpl.
    destruct (lt_dec 0 st) as [H₁| H₁].
     rewrite Nat.mod_0_l; simpl.
      rewrite fld_mul_ident; reflexivity.

      apply Pos2Nat_ne_0.

     apply not_gt in H₁.
     apply Nat.le_0_r in H₁.
     subst st.
Focus 1.
bbb.

intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
constructor 1 with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite stretch_series_1.
rewrite stretch_series_1 in |- * at 2.
constructor; simpl.
 intros i.
 remember
  (sum_mul_coeff fld 1 i
     (stretch_series fld (Pos.to_nat (nz_comden nz))
        {| terms := λ _ : nat, one fld; stop := 1 |})
     (stretch_series fld (Pos.to_nat 1) (nz_terms nz))) as x.
 symmetry in Heqx.
 destruct x as [x| ].
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [| Bad].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ].
    destruct (lt_dec i st) as [H| H].
     rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
     rewrite divmod_div.
     rewrite Nat.div_1_r.
     rewrite fld_mul_ident.
bbb.

Definition ps_fld : field (puiseux_series α) :=
  {| zero := ps_zero;
     one := ps_one;
     add := ps_add fld;
     mul := ps_mul fld;
     fld_eq := eq_ps fld;
     fld_eq_refl := eq_ps_refl fld;
     fld_eq_sym := eq_ps_sym (fld := fld);
     fld_eq_trans := eq_ps_trans (fld := fld);
     fld_add_comm := ps_add_comm;
     fld_add_assoc := ps_add_assoc;
     fld_add_0_l := ps_add_ident;
     fld_add_compat := ps_add_compat;
     fld_mul_ident := ps_mul_ident |}.

End fld₄.
