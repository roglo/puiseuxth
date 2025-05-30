From Stdlib Require Import Utf8 Nat.

Record Z := mk_z { z_sign : bool; z_val : nat }.

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.

Module Z.

Definition of_nat := mk_z true.

Definition add a b :=
  match z_sign a with
  | true =>
      match z_sign b with
     | true => mk_z true (z_val a + z_val b)
     | false =>
         if Nat.ltb (z_val a) (z_val b) then mk_z false (z_val b - z_val a)
         else mk_z true (z_val a - z_val b)
      end
  | false =>
      match z_sign b with
     | true =>
         if Nat.leb (z_val a) (z_val b) then mk_z true (z_val b - z_val a)
         else mk_z false (z_val a - z_val b)
     | false => mk_z false (z_val a + z_val b)
      end
  end.

Definition opp a := mk_z (negb (z_sign a)) (z_val a).
Definition mul a b := mk_z (xorb (z_sign a) (z_sign b)) (z_val a * z_val b).

Definition compare a b :=
  if z_sign a then
    if z_sign b then z_val a ?= z_val b else Gt
  else
    if z_sign b then Lt else z_val b ?= z_val a.

End Z.

Definition of_number (n : Number.int) : option Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_z true (Nat.of_uint n))
      | Decimal.Neg n => Some (mk_z false (Nat.of_uint n))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (n : Z) : option Number.int :=
  if z_sign n then
    Some (Number.IntDecimal (Decimal.Pos (Nat.to_uint (z_val n))))
  else
    Some (Number.IntDecimal (Decimal.Neg (Nat.to_uint (z_val n)))).

Number Notation Z of_number to_number : Z_scope.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a ?= b" := (Z.compare a b) : Z_scope.

Open Scope Z_scope.
