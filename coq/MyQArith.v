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
  match q_num a with
  | z_zero => mk_q 0 0
  | z_val s v => mk_q (z_val s (q_den a)) v
  end.

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
progress unfold add; cbn.
f_equal; [ | now rewrite Nat.mul_assoc ].
do 2 rewrite Nat2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
rewrite <- Z.add_assoc.
f_equal; [ apply Z.mul_assoc | ].
f_equal; [ apply Z.mul_mul_swap | ].
rewrite <- Z.mul_assoc.
f_equal; apply Z.mul_comm.
Qed.

Theorem add_0_l : ∀ a, add (mk_q 0 1) a = a.
Proof.
intros.
progress unfold add; cbn.
rewrite Z.mul_1_r, Nat.add_0_r.
now destruct a.
Qed.

Theorem add_0_r : ∀ a, add a (mk_q 0 1) = a.
Proof.
intros.
rewrite add_comm.
apply add_0_l.
Qed.

Theorem mul_comm : ∀ a b, mul a b = mul b a.
Proof.
intros.
progress unfold mul.
now rewrite Z.mul_comm, Nat.mul_comm.
Qed.

Theorem mul_assoc : ∀ a b c, mul a (mul b c) = mul (mul a b) c.
Proof.
intros.
progress unfold mul; cbn.
now rewrite Z.mul_assoc, Nat.mul_assoc.
Qed.

Theorem mul_1_l : ∀ a, mul (mk_q 1 1) a = a.
Proof.
intros.
progress unfold mul; cbn.
destruct a as (na, da); cbn.
rewrite Nat.add_0_r.
progress f_equal.
destruct na as [| sa va]; [ easy | ].
rewrite Nat.add_0_r, Nat.add_sub.
now destruct sa.
Qed.

Theorem mul_1_r : ∀ a, mul a (mk_q 1 1) = a.
Proof.
intros.
rewrite mul_comm.
apply mul_1_l.
Qed.

Theorem opp_involutive : ∀ a, opp (opp a) = a.
Proof.
intros.
progress unfold opp; cbn.
...
rewrite Z.opp_involutive.
...

Definition of_number (n : Number.int) : option Q :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_q (Z.of_nat (Nat.of_uint n)) 1)
      | Decimal.Neg n => Some (mk_q (- Z.of_nat (Nat.of_uint n)) 1)
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Q) : option Number.int :=
  match q_den a with
  | 1%nat => Some (Z.to_number (q_num a))
  | _ => None
  end.

End Q.

Number Notation Q Q.of_number Q.to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.

Close Scope Z_scope.
Open Scope Q_scope.
