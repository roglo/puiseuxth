(* $Id: Nbar.v,v 1.6 2013-08-14 19:15:43 deraugla Exp $ *)

Require Import Utf8.
Require Import NPeano.

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
  | le_nfin : ∀ n m, (n <= m)%nat → nfin n <= nfin m
  | le_ninf : ∀ n, n <= ∞

where "n <= m" := (le n m) : Nbar_scope.

Definition lt n m := Nbar_S n <= m.
Infix "<" := lt : Nbar_scope.

Definition to_nat nb :=
  match nb with
  | nfin n => n
  | ninf => O
  end.

Theorem mul_lt_mono_pos_r : ∀ p n m, 0 < p → p ≠ ∞ → n ≠ ∞ →
  n < m ↔ n * p < m * p.
Proof.
intros p n m Hp Hpi Hni.
destruct p as [p| ]; [ simpl | exfalso; apply Hpi; reflexivity ].
destruct n as [n| ]; [ simpl | exfalso; apply Hni; reflexivity ].
destruct m as [m| ]; simpl.
 split; intros.
  constructor.
  apply Nat.mul_lt_mono_pos_r; [ inversion Hp | inversion H ]; assumption.

  constructor.
  eapply Nat.mul_lt_mono_pos_r; [ inversion Hp | inversion H ]; eassumption.

 split; intros H; constructor.
Qed.

Theorem nfin_inj_mul : ∀ n m, nfin (n * m) = nfin n * nfin m.
Proof. reflexivity. Qed.

Theorem lt_dec : ∀ (n m : Nbar), {n < m} + {~ n < m}.
Proof.
Admitted. (*
bbb.
*)

Close Scope Nbar_scope.

End Nbar.

Infix "+" := Nbar.add : Nbar_scope.
Infix "-" := Nbar.sub : Nbar_scope.
Infix "*" := Nbar.mul : Nbar_scope.
Infix "<" := Nbar.lt : Nbar_scope.
