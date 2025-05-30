From Stdlib Require Import Utf8 Arith.
Require Import MyZArith.

Record Q := mk_q
  { q_num : Z;
    q_den : nat }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Module Q.

Definition eq a b :=
  q_num a * Z.of_nat (q_den b) = q_num b * Z.of_nat (q_den a).

Definition add a b :=
  mk_q (q_num a * Z.of_nat (q_den b) + q_num b * Z.of_nat (q_den a))
    (q_den a * q_den b).

Definition opp a := mk_q (- q_num a) (q_den a).
Definition sub a b := add a (opp b).

Definition mul a b := mk_q (q_num a * q_num b) (q_den a * q_den b).

Definition inv a :=
  mk_q (mk_z (z_sign (q_num a)) (q_den a)) (z_val (q_num a)).

Definition div a b := mul a (inv b).

Definition compare a b :=
  q_num a * Z.of_nat (q_den b) ?= q_num b * Z.of_nat (q_den a).

Theorem add_comm : ∀ a b, add a b = add b a.
Proof.
intros.
progress unfold add.
rewrite Z.add_comm.
rewrite (Nat.mul_comm (q_den b)).
easy.
Qed.

Theorem add_assoc : ∀ a b c, add a (add b c) = add (add a b) c.
Proof.
intros.
progress unfold add.
cbn.
f_equal; [ | now rewrite Nat.mul_assoc ].
do 2 rewrite Nat2Z.inj_mul.
... ...
rewrite Z.mul_add_distr_r.
...
progress unfold Qplus.
cbn.
rewrite Pos.mul_assoc.
progress f_equal.
do 2 rewrite Pos2Z.inj_mul.
ring.
Qed.

End Q.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.

Close Scope Z_scope.
Open Scope Q_scope.
