(* positive natural, represented by nat *)

From Stdlib Require Import Arith.

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

End Pos.

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
