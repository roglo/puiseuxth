(* $Id: Zbar.v,v 1.13 2013-08-15 17:20:48 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Require Import Nbar.

Set Implicit Arguments.

Inductive Zbar : Set :=
  | zfin : ∀ x : Z, Zbar
  | zinf : Zbar.

Delimit Scope Zbar_scope with Zbar.
Bind Scope Zbar_scope with Zbar.

Notation "∞" := zinf.
Notation "0" := (zfin 0) : Zbar_scope.
Notation "'' a" := (zfin (Zpos a)) (at level 20).

Open Scope Zbar_scope.

Module Zbar.

Definition binop f dx dy xb yb :=
  match xb with
  | zfin x =>
      match yb with
      | zfin y => zfin (f x y)
      | ∞ => dx
      end
  | ∞ => dy
  end.

Definition add := binop Z.add ∞ ∞.
Definition mul := binop Z.mul ∞ ∞.
Definition min x y := binop Z.min x y x y.

Infix "+" := add : Zbar_scope.
Infix "*" := mul : Zbar_scope.

Inductive le : Zbar → Zbar → Prop :=
  | le_zfin : ∀ n m, (n <= m)%Z → zfin n ≤ zfin m
  | le_zinf : ∀ n, n ≤ ∞

where "n ≤ m" := (le n m) : Zbar_scope.

Definition not_0_inf x := x ≠ 0 ∧ x ≠ ∞.

Definition to_Nbar zb :=
  match zb with
  | zfin z => nfin (Z.to_nat z)
  | ∞ => ninf
  end.

Theorem pos_ne_0 : ∀ p, not_0_inf ('' p).
Proof.
intros p.
unfold not_0_inf.
split; intros H; discriminate H.
Qed.

Theorem mul_comm : ∀ n m, n * m = m * n.
Proof.
intros n m.
unfold mul.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ idtac | reflexivity ].
rewrite Z.mul_comm; reflexivity.
Qed.

Theorem mul_assoc : ∀ n m p, n * (m * p) = n * m * p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ rewrite Z.mul_assoc; reflexivity | reflexivity ].
Qed.

Theorem mul_cancel_r : ∀ n m p, not_0_inf p →
  n * p = m * p ↔ n = m.
Proof.
intros n m p (Hp, Hpi).
destruct p as [p| ]; [ clear Hpi | exfalso; apply Hpi; reflexivity ].
induction n as [n| ]; simpl.
 induction m as [m| ]; simpl.
  split; intros H.
   injection H; clear H; intros.
   apply Z.mul_cancel_r in H.
    subst; reflexivity.

    clear H; intros H; apply Hp; clear Hp.
    subst p; reflexivity.

   injection H; clear H; intros H; subst n; reflexivity.

  split; intros H; discriminate H.

 induction m as [m| ]; simpl.
  split; intros H; discriminate H.

  split; intros H; reflexivity.
Qed.

Theorem mul_cancel_l : ∀ n m p : Zbar, not_0_inf p →
  p * n = p * m ↔ n = m.
Proof.
intros n m p Hp.
split; intros H.
 rewrite mul_comm in H; symmetry in H.
 rewrite mul_comm in H; symmetry in H.
 apply -> mul_cancel_r; eassumption.

 subst; reflexivity.
Qed.

Theorem mul_shuffle0 : ∀ n m p, n * m * p = n * p * m.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | destruct p; reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
rewrite Z.mul_shuffle0; reflexivity.
Qed.

Theorem mul_1_r : ∀ n, n * ''1 = n.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem min_comm : ∀ n m, min n m = min m n.
Proof.
intros n m.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
rewrite Z.min_comm; reflexivity.
Qed.

Theorem mul_min_distr_nonneg_r : ∀ n m p, 0 ≤ p →
  min (n * p) (m * p) = min n m * p.
Proof.
intros n m p H.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | destruct p; reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
rewrite Z.mul_min_distr_nonneg_r; [ reflexivity | idtac ].
inversion H; assumption.
Qed.

End Zbar.

Close Scope Zbar_scope.

Infix "+" := Zbar.add : Zbar_scope.
Infix "*" := Zbar.mul : Zbar_scope.
