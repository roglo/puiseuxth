(* $Id: Nbar.v,v 1.9 2013-08-15 02:26:36 deraugla Exp $ *)

Require Import Utf8.
Require Import Compare_dec.
Require Import NPeano.

Set Implicit Arguments.

Inductive Nbar : Set :=
  | nfin : ∀ x : nat, Nbar
  | ninf : Nbar.

Delimit Scope Nbar_scope with Nbar.
Bind Scope Nbar_scope with Nbar.

Notation "∞" := ninf.
Notation "0" := (nfin 0) : Nbar_scope.

Open Scope Nbar_scope.

Module Nbar.

Definition S n :=
  match n with
  | nfin n => nfin (S n)
  | ninf => ninf
  end.

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

Inductive le : Nbar → Nbar → Prop :=
  | le_nfin : ∀ n m, (n <= m)%nat → nfin n <= nfin m
  | le_ninf : ∀ n, n <= ∞

where "n <= m" := (le n m) : Nbar_scope.

Definition lt n m := S n <= m.
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

Theorem nfin_inj_S : ∀ n, nfin (Datatypes.S n) = S (nfin n).
Proof. reflexivity. Qed.

Theorem lt_dec : ∀ (n m : Nbar), {n < m} + {~ n < m}.
Proof.
intros n m.
destruct n as [n| ].
 destruct m as [m| ].
  destruct (lt_dec n m) as [Hlt| Hge].
   left; constructor; assumption.

   right; intros H; apply Hge; clear Hge.
   inversion H; assumption.

  left; constructor.

 destruct m as [m| ]; [ right; intros H; inversion H | left; constructor ].
Qed.

Theorem lt_0_succ: ∀ n : Nbar, 0 < S n.
Proof.
intros n.
destruct n; [ constructor; apply Nat.lt_0_succ | constructor ].
Qed.

End Nbar.

Module Nbar2Nat.

Infix "*" := Nbar.mul : Nbar_scope.

Theorem inj_mul : ∀ p q : Nbar,
  Nbar.to_nat (p * q) = (Nbar.to_nat p * Nbar.to_nat q)%nat.
Proof.
intros p q.
destruct p as [p| ]; [ simpl | reflexivity ].
destruct q as [q| ]; [ reflexivity | simpl ].
rewrite Nat.mul_0_r; reflexivity.
Qed.

End Nbar2Nat.

Close Scope Nbar_scope.

Infix "+" := Nbar.add : Nbar_scope.
Infix "-" := Nbar.sub : Nbar_scope.
Infix "*" := Nbar.mul : Nbar_scope.
Infix "<" := Nbar.lt : Nbar_scope.
