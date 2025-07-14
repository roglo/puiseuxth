(* Q_field.v *)

From Stdlib Require Import Utf8.

Require Import A_QArith.
Require Import Field2.
Open Scope Q_scope.

Definition Q_ring :=
  {| rng_zero := 0;
     rng_one := 1;
     rng_add := Q.add;
     rng_mul := Q.mul;
     rng_opp := Q.opp;
     rng_eq := Q.eq;
     rng_eq_refl := Q.eq_refl;
     rng_eq_sym := Q.eq_symm;
     rng_eq_trans := Q.eq_trans;
     rng_add_comm a b := eq_qeq _ _ (Q.add_comm a b);
     rng_add_assoc a b c := eq_qeq _ _ (Q.add_assoc a b c);
     rng_add_0_l a := eq_qeq _ _ (Q.add_0_l a);
     rng_add_opp_l := Q.add_opp_diag_l;
     rng_add_compat_l a b c := Q.add_compat_l_if c a b;
     rng_mul_comm a b := eq_qeq _ _ (Q.mul_comm a b);
     rng_mul_assoc a b c := eq_qeq _ _ (Q.mul_assoc a b c);
     rng_mul_1_l a := eq_qeq _ _ (Q.mul_1_l a);
     rng_mul_compat_l a b c := Q.mul_compat_l c a b;
     rng_mul_add_distr_l := Q.mul_add_distr_l |}.

Canonical Structure Q_ring.
