Require Import MyZArith.

Record Q := mk_q
  { q_num : Z;
    q_den : nat }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Definition q_eq a b :=
  q_num a * Z_of_nat (q_den b) = q_num b * Z_of_nat (q_den a).

Definition q_add a b :=
  mk_q (q_num a * Z_of_nat (q_den b) + q_num b * Z_of_nat (q_den a))
    (q_den a * q_den b).

Definition q_opp a := mk_q (- q_num a) (q_den a).
Definition q_sub a b := q_add a (q_opp b).

Notation "a == b" := (q_eq a b) (at level 70) : Q_scope.
Notation "a + b" := (q_add a b) : Q_scope.
Notation "a - b" := (q_sub a b) : Q_scope.
Notation "- a" := (q_opp a) : Q_scope.

Close Scope Z_scope.
Open Scope Q_scope.
