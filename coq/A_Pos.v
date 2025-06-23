(* positive natural, represented by nat *)

From Stdlib Require Import Utf8 Arith.

Record pos := { p_val : nat }.

Declare Scope pos_scope.
Delimit Scope pos_scope with pos.
Bind Scope pos_scope with pos.

Module Pos.

Definition of_nat n := {| p_val := n - 1 |}.
Definition to_nat p := p_val p + 1.

Definition of_number (n : Number.int) : option pos :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos (Decimal.D0 Decimal.Nil) => None
      | Decimal.Pos n => Some (Pos.of_nat (Nat.of_uint n))
      | Decimal.Neg n => None
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : pos) : Number.int :=
  Number.IntDecimal (Decimal.Pos (Nat.to_uint (Pos.to_nat a))).

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Definition add a b := {| p_val := p_val a + p_val b + 1 |}.
Definition sub a b := {| p_val := p_val a - p_val b - 1 |}.
Definition mul a b := {| p_val := (p_val a + 1) * (p_val b + 1) - 1 |}.

Definition compare a b := p_val a ?= p_val b.
Definition eqb a b := p_val a =? p_val b.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
Notation "a =? b" := (Pos.eqb a b) : pos_scope.

Theorem add_comm : ∀ a b, Pos.add a b = Pos.add b a.
Proof.
intros.
progress unfold Pos.add.
now rewrite (Nat.add_comm (p_val a)).
Qed.

Theorem eq_dec : ∀ a b : pos, {a = b} + {a ≠ b}.
Proof.
intros.
destruct (Nat.eq_dec (p_val a) (p_val b)) as [Hab| Hab]. {
  left.
  destruct a as (a).
  destruct b as (b).
  now cbn in Hab; subst.
} {
  right; intros H; apply Hab; clear Hab.
  now subst.
}
Qed.

Theorem compare_antisym : ∀ a b, ((a ?= b) = CompOpp (b ?= a))%pos.
Proof. intros; apply Nat.compare_antisym. Qed.

End Pos.

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
Notation "a =? b" := (Pos.eqb a b) : pos_scope.
