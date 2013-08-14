(* $Id: Zbar.v,v 1.7 2013-08-14 12:14:29 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Require Import Nbar.

Set Implicit Arguments.

Inductive Zbar : Set :=
  | zfin : ∀ x : Z, Zbar
  | zinf : Zbar.

Notation "∞" := zinf.

Definition Zbar_mul x y :=
  match x with
  | zfin xf =>
      match y with
      | zfin yf => zfin (xf * yf)
      | ∞ => ∞
      end
  | ∞ => ∞
  end.

Delimit Scope Zbar_scope with Zbar.
Bind Scope Zbar_scope with Zbar.

Notation "0" := (zfin 0) : Zbar_scope.
Notation "'' a" := (zfin (Zpos a)) (at level 20).
Infix "*" := Zbar_mul : Zbar_scope.

Open Scope Zbar_scope.

Definition not_0_inf x := x ≠ 0 ∧ x ≠ ∞.

Theorem Zbpos_ne_0 : ∀ p, not_0_inf ('' p).
Proof.
intros p.
unfold not_0_inf.
split; intros H; discriminate H.
Qed.

Theorem Zbar_mul_comm : ∀ n m : Zbar, n * m = m * n.
Proof.
intros n m.
unfold Zbar_mul.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ idtac | reflexivity ].
rewrite Z.mul_comm; reflexivity.
Qed.

Theorem Zbar_mul_assoc : ∀ n m p : Zbar, n * (m * p) = n * m * p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ rewrite Z.mul_assoc; reflexivity | reflexivity ].
Qed.

Theorem Zbar_mul_cancel_r : ∀ n m p : Zbar, not_0_inf p →
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

Theorem Zbar_mul_cancel_l : ∀ n m p : Zbar, not_0_inf p →
  p * n = p * m ↔ n = m.
Proof.
intros n m p Hp.
split; intros H.
 rewrite Zbar_mul_comm in H; symmetry in H.
 rewrite Zbar_mul_comm in H; symmetry in H.
 apply -> Zbar_mul_cancel_r; eassumption.

 subst; reflexivity.
Qed.

Theorem Zbar_mul_shuffle0 : ∀ n m p : Zbar, n * m * p = n * p * m.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; simpl.
 destruct p as [p| ]; [ simpl | reflexivity ].
 rewrite Z.mul_shuffle0; reflexivity.

 destruct p; reflexivity.
Qed.

Close Scope Zbar_scope.
