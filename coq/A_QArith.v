(** * A ℚ arithmetics *)

From Stdlib Require Import Utf8 Arith.
Require Import A_ZArith.

Record Q := mk_q
  { q_num : Z;
    q_den : nat }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Definition q_Den a := Z.of_nat (q_den a).

Module Q.

Open Scope Z_scope.

Definition eq a b := q_num a * q_Den b = q_num b * q_Den a.

Definition add a b :=
  mk_q (q_num a * q_Den b + q_num b * q_Den a) (q_den a * q_den b).

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
  q_num a * q_Den b ?= q_num b * q_Den a.

Definition le x y := (q_num x * q_Den y ≤ q_num y * q_Den x)%Z.
Definition lt x y := (q_num x * q_Den y < q_num y * q_Den x)%Z.

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

Number Notation Q of_number to_number : Q_scope.

Notation "a == b" := (eq a b) (at level 70) : Q_scope.
Notation "a + b" := (add a b) : Q_scope.
Notation "a * b" := (mul a b) : Q_scope.
Notation "- a" := (opp a) : Q_scope.
Notation "a ≤ b" := (le a b) : Q_scope.
Notation "a < b" := (lt a b) : Q_scope.

Theorem add_comm : ∀ a b, (a + b)%Q = (b + a)%Q.
Proof.
intros.
progress unfold add.
rewrite Z.add_comm.
rewrite (Nat.mul_comm (q_den b)).
easy.
Qed.

Theorem add_assoc : ∀ a b c, (a + (b + c))%Q = ((a + b) + c)%Q.
Proof.
intros.
progress unfold add; cbn.
f_equal; [ | now rewrite Nat.mul_assoc ].
progress unfold q_Den; cbn.
do 2 rewrite Nat2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
rewrite <- Z.add_assoc.
f_equal; [ apply Z.mul_assoc | ].
f_equal; [ apply Z.mul_mul_swap | ].
rewrite <- Z.mul_assoc.
f_equal; apply Z.mul_comm.
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Q = a.
Proof.
intros.
progress unfold add; cbn.
rewrite Z.mul_1_r, Nat.add_0_r.
now destruct a.
Qed.

Theorem add_0_r : ∀ a, (a + 0)%Q = a.
Proof.
intros.
rewrite add_comm.
apply add_0_l.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%Q = (b * a)%Q.
Proof.
intros.
progress unfold mul.
now rewrite Z.mul_comm, Nat.mul_comm.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Q = ((a * b) * c)%Q.
Proof.
intros.
progress unfold mul; cbn.
now rewrite Z.mul_assoc, Nat.mul_assoc.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Q = a.
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

Theorem mul_1_r : ∀ a, (a * 1)%Q = a.
Proof.
intros.
rewrite mul_comm.
apply mul_1_l.
Qed.

Theorem opp_involutive : ∀ a, (- - a)%Q = a.
Proof.
intros.
progress unfold opp; cbn.
rewrite Z.opp_involutive.
now destruct a.
Qed.

Theorem nle_gt : ∀ a b, ¬ (a ≤ b)%Q ↔ (b < a)%Q.
Proof. intros; apply Z.nle_gt. Qed.

Theorem le_antisymm : ∀ a b, (a ≤ b)%Q → (b ≤ a)%Q → (a == b)%Q.
Proof.
intros * Hab Hba.
progress unfold le in Hab, Hba.
progress unfold eq.
now apply Z.le_antisymm.
Qed.

End Q.

Number Notation Q Q.of_number Q.to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "a <= b" := (Q.le a b) : Q_scope.
Notation "a ≤ b" := (Q.le a b) : Q_scope.
Notation "a < b" := (Q.lt a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.
