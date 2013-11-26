(* $Id: SandBox.v,v 2.111 2013-11-26 20:56:10 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Field.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.

Set Implicit Arguments.

Section fld.

Variable α : Type.
Variable fld : Field.t α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (Field.eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (Field.zero fld) : fld_scope.
Notation "1" := (Field.one fld) : fld_scope.

(* ps_mul *)

Definition nz_mul nz₁ nz₂ :=
  {| nz_terms :=
       series_mul fld (nz_terms nz₁) (nz_terms nz₂);
     nz_valnum :=
       (nz_valnum nz₁ * ' nz_comden nz₂ + nz_valnum nz₂ * ' nz_comden nz₁)%Z;
     nz_comden :=
       nz_comden nz₁ * nz_comden nz₂ |}.

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_mul nz₁ nz₂)
      | Zero => ps₂
      end
  | Zero => ps₁
  end.

Delimit Scope ps_scope with ps.
Notation "a + b" := (ps_add fld a b) : ps_scope.
Notation "a * b" := (ps_mul a b) : ps_scope.

Lemma nz_norm_mul_comm : ∀ nz₁ nz₂,
  normalise_nz fld (nz_mul nz₁ nz₂) ≐ normalise_nz fld (nz_mul nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
rewrite series_mul_comm.
remember (series_mul fld (nz_terms nz₂) (nz_terms nz₁)) as x.
remember (null_coeff_range_length fld x 0) as n eqn:Hn .
symmetry in Hn; subst x.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 unfold gcd_nz; simpl.
 rewrite series_mul_comm.
 f_equal; [ f_equal; apply Z.add_comm | f_equal ].
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 rewrite Pos.mul_comm; reflexivity.

 rewrite Pos.mul_comm, series_mul_comm.
 unfold gcd_nz; simpl.
 do 3 f_equal.
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 rewrite Pos.mul_comm; reflexivity.

 unfold gcd_nz; simpl.
 rewrite Pos.mul_comm, series_mul_comm.
 remember (nz_valnum nz₁ * ' nz_comden nz₂)%Z as x eqn:Hx .
 remember (nz_valnum nz₂ * ' nz_comden nz₁)%Z as y eqn:Hy .
 replace (x + y)%Z with (y + x)%Z by apply Z.add_comm.
 reflexivity.
Qed.

Theorem ps_mul_comm : ∀ ps₁ ps₂, ps_mul ps₁ ps₂ ≈ ps_mul ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
 constructor.
 apply nz_norm_mul_comm.

 destruct ps₂; reflexivity.
Qed.

Lemma fold_series_1 :
  {| terms := λ _, Field.one fld; stop := 1 |} = series_1 fld.
Proof. reflexivity. Qed.

Theorem ps_mul_1_l : ∀ ps, ps_mul (ps_one fld) ps ≈ ps.
Proof.
intros ps; simpl.
destruct ps as [nz| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite fold_series_1, series_mul_1_l.
remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem ps_mul_1_r : ∀ ps, ps_mul ps (ps_one fld) ≈ ps.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_1_l. Qed.

Theorem ps_mul_0_l : ∀ ps, ps_mul (ps_zero _) ps ≈ (ps_zero _).
Proof. intros ps; constructor. Qed.

Theorem ps_mul_0_r : ∀ ps, ps_mul ps (ps_zero _) ≈ (ps_zero _).
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_0_l. Qed.

Theorem ps_neq_1_0 : not (ps_one fld ≈ ps_zero _).
Proof.
intros H.
inversion_clear H.
inversion_clear H0.
pose proof (H O) as H₁.
unfold series_nth_fld in H₁.
simpl in H₁.
destruct (Nbar.lt_dec 0 0) as [H₂| H₂].
 revert H₂; apply Nbar.lt_irrefl.

 destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
  apply Field.neq_1_0 in H₁; contradiction.

  apply H₃, Nbar.lt_0_1.
Qed.

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  ps_mul ps₁ (ps_mul ps₂ ps₃) ≈ ps_mul (ps_mul ps₁ ps₂) ps₃.
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite series_mul_assoc.
remember (series_mul fld (nz_terms nz₁) (nz_terms nz₂)) as s₁₂.
remember (series_mul fld s₁₂ (nz_terms nz₃)) as s₁₂₃; subst s₁₂.
remember (null_coeff_range_length fld s₁₂₃ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite series_mul_assoc, <- Heqs₁₂₃.
 unfold gcd_nz; simpl.
 f_equal.
  apply Z.add_cancel_r.
  do 2 rewrite Pos2Z.inj_mul; ring.

  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 do 2 f_equal.
  do 4 rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc; reflexivity.

  unfold gcd_nz; simpl.
  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 apply eq_series_eq.
 do 2 f_equal.
 unfold gcd_nz; simpl.
 do 2 f_equal.
  do 2 rewrite Pos2Z.inj_mul; ring.

  rewrite Pos.mul_assoc; reflexivity.
Qed.

Theorem ps_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₁ * ps₃)%ps ≈ (ps₂ * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
destruct ps₃ as [nz₃| ]; [ idtac | do 2 rewrite ps_mul_0_r; reflexivity ].
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | simpl ].
  constructor.
bbb.

Definition ps_fld α : Field.t (puiseux_series α) :=
  {| Field.zero := @ps_zero α;
     Field.one := @ps_one α fld;
     Field.add := @ps_add α fld;
     Field.mul := @ps_mul;
     Field.opp := @ps_opp α fld;
(*
     Field.inv := 0;
*)
     Field.eq := @eq_ps α fld;
     Field.eq_refl := @eq_ps_refl α fld;
     Field.eq_sym := @eq_ps_sym α fld;
     Field.eq_trans := @eq_ps_trans α fld;
     Field.neq_1_0 := @ps_neq_1_0;
     Field.add_comm := @ps_add_comm α fld;
     Field.add_assoc := @ps_add_assoc α fld;
     Field.add_0_l := @ps_add_0_l α fld;
     Field.add_opp_l := @ps_add_opp_l α fld;
     Field.add_compat_l := @ps_add_compat_l α fld;
     Field.mul_comm := @ps_mul_comm;
     Field.mul_assoc := @ps_mul_assoc;
     Field.mul_1_l := @ps_mul_1_l;
     Field.mul_compat_l := @ps_mul_compat_l
(*
     Field.mul_inv_l := 0;
     Field.mul_add_distr_l := 0
*)
   |}.

End fld.

Add Parametric Morphism α (fld : Field.t α) : (ps_mul fld)
with signature eq_ps fld ==> eq_ps fld ==> eq_ps fld
as ps_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
bbb.
