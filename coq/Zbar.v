(* $Id: Zbar.v,v 1.1 2013-08-13 20:44:15 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Set Implicit Arguments.

Inductive Zbar : Set :=
  | Zfin : ∀ x : Z, Zbar
  | Zinf : Zbar.

Definition Zbar_mul x y :=
  match x with
  | Zfin xf =>
      match y with
      | Zfin yf => Zfin (xf * yf)
      | Zinf => Zinf
      end
  | Zinf => Zinf
  end.

Delimit Scope Zbar_scope with Zbar.
Bind Scope Zbar_scope with Zbar.

Notation "0" := (Zfin 0).
Notation "'' a" := (Zfin (Zpos a)) (at level 20).
Infix "*" := Zbar_mul : Zbar_scope.

Definition not_0_inf x := x ≠ 0 ∧ x ≠ Zinf.

Theorem Zbar_mul_cancel_r : ∀ n m p : Zbar, not_0_inf p →
  (n * p)%Zbar = (m * p)%Zbar ↔ n = m.
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
