(* $Id: SandBox.v,v 2.106 2013-11-23 12:06:24 deraugla Exp $ *)

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

Definition ps_fld : Field.t (puiseux_series α) :=
  {| Field.zero := @ps_zero α;
     Field.one := @ps_one α fld;
     Field.add := @ps_add α fld;
     Field.mul := @ps_mul;
     Field.opp := 0;
     Field.inv := 0;
     Field.eq := eq_ps fld;
     Field.eq_refl := 0;
     Field.eq_sym := 0;
     Field.eq_trans := 0;
     Field.neq_1_0 := 0;
     Field.add_comm := 0;
     Field.add_assoc := 0;
     Field.add_0_l := 0;
     Field.add_opp_l := 0;
     Field.add_compat_l := 0;
     Field.mul_comm := 0;
     Field.mul_assoc := 0;
     Field.mul_1_l := 0;
     Field.mul_compat_l := 0;
     Field.mul_inv_l := 0;
     Field.mul_add_distr_l := 0 |}.

End fld₄.
