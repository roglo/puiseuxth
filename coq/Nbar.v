(* $Id: Nbar.v,v 1.5 2013-08-14 15:25:03 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Set Implicit Arguments.

Inductive Nbar : Set :=
  | nfin : ∀ x : nat, Nbar
  | ninf : Nbar.

Definition Nbar_S n :=
  match n with
  | nfin n => nfin (S n)
  | ninf => ninf
  end.

Delimit Scope Nbar_scope with Nbar.
Bind Scope Nbar_scope with Nbar.

Notation "∞" := ninf.
Notation "0" := (nfin 0) : Nbar_scope.

Module Nbar.

Definition binop f dx dy xb yb :=
  match xb with
  | nfin x =>
      match yb with
      | nfin y => nfin (f x y)
      | ∞ => dx
      end
  | ∞ => dy
  end.

Definition add := binop plus ∞ ∞.
Definition sub := binop minus (nfin 0) ∞.
Definition mul := binop mult ∞ ∞.

Infix "+" := add : Nbar_scope.
Infix "-" := sub : Nbar_scope.
Infix "*" := mul : Nbar_scope.

Open Scope Nbar_scope.

Inductive le : Nbar → Nbar → Prop :=
  | le_n : ∀ n, n <= n
  | le_S : ∀ n m, nfin n <= nfin m → nfin n <= nfin (S m)
  | le_ninf : ∀ n, n <= ∞

where "n <= m" := (le n m) : Nbar_scope.

Definition lt n m := Nbar_S n <= m.

Definition to_nat nb :=
  match nb with
  | nfin n => n
  | ninf => O
  end.

Infix "<" := lt : Nbar_scope.

Theorem lt_dec : ∀ (n m : Nbar), {n < m} + {~ n < m}.
Admitted.

Close Scope Nbar_scope.

End Nbar.

Infix "+" := Nbar.add : Nbar_scope.
Infix "-" := Nbar.sub : Nbar_scope.
Infix "*" := Nbar.mul : Nbar_scope.
Infix "<" := Nbar.lt : Nbar_scope.
