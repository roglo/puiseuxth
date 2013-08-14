(* $Id: Nbar.v,v 1.2 2013-08-14 12:51:47 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Set Implicit Arguments.

Inductive Nbar : Set :=
  | nfin : ∀ x : nat, Nbar
  | ninf : Nbar.

Notation "∞" := ninf.

Delimit Scope Nbar_scope with Nbar.
Bind Scope Nbar_scope with Nbar.

Open Scope Nbar_scope.

Definition Nbar_sub x y :=
  match x with
  | nfin n =>
      match y with
      | nfin m => nfin (n - m)
      | ninf => nfin 0
      end
  | ∞ => ∞
  end.

Definition Nbar_S n :=
  match n with
  | nfin n => nfin (S n)
  | ∞ => ∞
  end.

Inductive Nbar_le : Nbar → Nbar → Prop :=
  | le_n : ∀ n, n <= n
  | le_S : ∀ n m, nfin n <= nfin m → nfin n <= nfin (S m)
  | le_inf : ∀ n, n <= ∞

where "n <= m" := (Nbar_le n m) : Nbar_scope.

Definition Nbar_lt n m := Nbar_S n <= m.

Notation "0" := (nfin 0) : Nbar_scope.
Infix "-" := Nbar_sub : Nbar_scope.
Infix "<" := Nbar_lt : Nbar_scope.

Definition Nbar_to_nat nb :=
  match nb with
  | nfin n => n
  | ninf => O
  end.

Theorem Nbar_lt_dec : ∀ n m, {n < m} + {~ n < m}.
Admitted.

Close Scope Nbar_scope.
