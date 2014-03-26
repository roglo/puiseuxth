(* Q_field.v *)

Require Import Utf8.
Require Import QArith.

Require Import Field.

Theorem Qplus_opp_l : ∀ a, -a + a == 0.
Proof. intros a; rewrite Qplus_comm; apply Qplus_opp_r. Qed.

Theorem Qmul_inv_l : ∀ a, ¬a == 0 → /a * a == 1.
Proof. intros a; rewrite Qmult_comm; apply Qmult_inv_r; assumption. Qed.

Theorem Qplus_compat_l : ∀ a b c, a == b → c + a == c + b.
Proof. intros a b c H; apply Qplus_inj_l; assumption. Qed.

Theorem Qmult_compat_l : ∀ a b c, a == b → c * a == c * b.
Proof.
intros a b c H.
destruct (Qeq_dec c 0) as [Hz| ]; [ rewrite Hz; reflexivity | idtac ].
apply Qmult_inj_l; assumption.
Qed.

Definition Q_field :=
  {| rng_zero := 0;
     rng_one := 1;
     rng_add := Qplus;
     rng_mul := Qmult;
     rng_opp := Qopp;
     rng_eq := Qeq;
     rng_eq_refl := Qeq_refl;
     rng_eq_sym := Qeq_sym;
     rng_eq_trans := Qeq_trans;
     rng_add_comm := Qplus_comm;
     rng_add_assoc := Qplus_assoc;
     rng_add_0_l := Qplus_0_l;
     rng_add_opp_l := Qplus_opp_l;
     rng_add_compat_l := Qplus_compat_l;
     rng_mul_comm := Qmult_comm;
     rng_mul_assoc := Qmult_assoc;
     rng_mul_1_l := Qmult_1_l;
     rng_mul_compat_l := Qmult_compat_l;
     rng_mul_add_distr_l := Qmult_plus_distr_r;
     fld_inv := Qinv;
     rng_mul_inv_l := Qmul_inv_l |}.
