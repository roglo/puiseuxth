(* Q_field.v *)

From Stdlib Require Import Utf8.

Require Import A_QArith.
Require Import Field2.
Open Scope Q_scope.

Check Q.add_opp_l.
...
Theorem Qplus_opp_l : ∀ a, -a + a == 0.
Proof. intros a; rewrite Q.add_comm; apply Q.add_opp_r. Qed.

Theorem Qplus_compat_l : ∀ a b c, a == b → c + a == c + b.
Proof. intros a b c H; apply Qplus_inj_l; assumption. Qed.

Theorem Qmult_compat_l : ∀ a b c, a == b → c * a == c * b.
Proof.
intros a b c H.
destruct (Qeq_dec c 0) as [Hz| ]; [ rewrite Hz; reflexivity | idtac ].
apply Qmult_inj_l; assumption.
Qed.

Definition Q_ring :=
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
     rng_mul_add_distr_l := Qmult_plus_distr_r |}.

Canonical Structure Q_ring.
