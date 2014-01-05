(* Pbar.v *)

Require Import Utf8.
Require Import ZArith.
Require Import NPeano.

Set Implicit Arguments.

Inductive Pbar : Set :=
  | pfin : ∀ x : positive, Pbar
  | pinf : Pbar.

Delimit Scope Pbar_scope with Pbar.
Bind Scope Pbar_scope with Pbar.

Notation "∞" := pinf.
Notation "1" := (pfin xH) : Pbar_scope.

Open Scope Pbar_scope.

Module Pbar.

Definition binop f dx dy xb yb :=
  match xb with
  | pfin x =>
      match yb with
      | pfin y => pfin (f x y)
      | ∞ => dx
      end
  | ∞ => dy
  end.

Definition add := binop Pos.add ∞ ∞.
Definition mul := binop Pos.mul ∞ ∞.

Inductive le : Pbar → Pbar → Prop :=
  | le_pfin : ∀ n m, (n <= m)%positive → pfin n ≤ pfin m
  | le_pinf : ∀ n, n ≤ ∞

where "n ≤ m" := (le n m) : Pbar_scope.

Definition lt n m := Pbar.add 1 n ≤ m.

Definition to_pos pb :=
  match pb with
  | pfin n => n
  | ∞ => xH
  end.

Definition to_nat pb :=
  match pb with
  | pfin n => Pos.to_nat n
  | ∞ => O
  end.

End Pbar.

Infix "+" := Pbar.add : Pbar_scope.
Infix "*" := Pbar.mul : Pbar_scope.

Module Pbar2Nat.

(*
Theorem is_pos : ∀ a, (0 < Pbar.to_nat a)%nat.
Proof.
intros a.
bbb.

Theorem ne_0 : ∀ a, (Pbar.to_nat a ≠ 0)%nat.
Proof.
intros a H.
pose proof is_pos a as HH.
rewrite H in HH.
revert HH; apply lt_irrefl.
Qed.
*)

Theorem inj_mul : ∀ p q,
  Pbar.to_nat (p * q) = (Pbar.to_nat p * Pbar.to_nat q)%nat.
Proof.
intros p q.
destruct p as [p| ]; [ simpl | reflexivity ].
destruct q as [q| ]; [ simpl | rewrite Nat.mul_comm; reflexivity ].
apply Pos2Nat.inj_mul.
Qed.

End Pbar2Nat.

Close Scope Pbar_scope.
