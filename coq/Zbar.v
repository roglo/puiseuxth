(* $Id: Zbar.v,v 1.4 2013-08-14 04:34:40 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Set Implicit Arguments.

Inductive Zbar : Set :=
  | fin : ∀ x : Z, Zbar
  | inf : Zbar.

Notation "∞" := inf.

Definition Zbar_mul x y :=
  match x with
  | fin xf =>
      match y with
      | fin yf => fin (xf * yf)
      | ∞ => ∞
      end
  | ∞ => ∞
  end.

Delimit Scope Zbar_scope with Zbar.
Bind Scope Zbar_scope with Zbar.

Notation "0" := (fin 0) : Zbar_scope.
Notation "'' a" := (fin (Zpos a)) (at level 20).
Infix "*" := Zbar_mul : Zbar_scope.

Open Scope Zbar_scope.

Definition not_0_inf x := x ≠ 0 ∧ x ≠ ∞.

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

Lemma Zbpos_ne_0 : ∀ p, not_0_inf ('' p).
Proof.
intros p.
unfold not_0_inf.
split; intros H; discriminate H.
Qed.

Close Scope Zbar_scope.
