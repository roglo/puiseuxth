(* $Id: Nbar.v,v 1.3 2013-08-14 13:07:55 deraugla Exp $ *)

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

Module Nbar.

Open Scope Nbar_scope.

Definition sub x y :=
  match x with
  | nfin n =>
      match y with
      | nfin m => nfin (n - m)
      | ninf => nfin 0
      end
  | ∞ => ∞
  end.

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

Notation "0" := (nfin 0) : Nbar_scope.
Infix "-" := Nbar.sub : Nbar_scope.
Infix "<" := Nbar.lt : Nbar_scope.
