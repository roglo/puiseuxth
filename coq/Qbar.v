(* Qbar.v *)

Require Import Utf8.
Require Import QArith.

Set Implicit Arguments.

Inductive Qbar : Set :=
  | qfin : ∀ x : Q, Qbar
  | qinf : Qbar.

Delimit Scope Qbar_scope with Qbar.

Notation "∞" := qinf : Qbar_scope.
Notation "0" := (qfin 0) : Qbar_scope.

Open Scope Qbar_scope.

Module Qbar.

Definition binop f dx dy xb yb :=
  match xb with
  | qfin x =>
      match yb with
      | qfin y => qfin (f x y)
      | ∞ => dx
      end
  | ∞ => dy
  end.

Definition add := binop Qplus ∞ ∞.
Definition mul := binop Qmult ∞ ∞.

Definition qeq a b :=
  match a with
  | qfin x =>
      match b with
      | qfin y => x == y
      | ∞ => False
      end
  | ∞ =>
      match b with
      | qfin y => False
      | ∞ => True
      end
  end.

Infix "+" := add : Qbar_scope.
Infix "*" := mul : Qbar_scope.

Inductive lt : Qbar → Qbar → Prop :=
  | lt_qfin : ∀ q r, (q < r)%Q → qfin q < qfin r
  | lt_qinf : ∀ q, qfin q < ∞
where "q < r" := (lt q r) : Qbar_scope.

Definition gt q r := lt r q.

Theorem qfin_lt_mono : ∀ n m, (n < m)%Q ↔ qfin n < qfin m.
Proof.
intros n m.
split; intros H; [ constructor; assumption | idtac ].
inversion H; assumption.
Qed.

Theorem eq_refl : reflexive _ qeq.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem eq_sym : symmetric _ qeq.
Proof.
intros a b Hab.
destruct a; [ idtac | assumption ].
destruct b; [ symmetry; assumption | contradiction ].
Qed.

Theorem eq_trans : transitive _ qeq.
Proof.
intros a b c Hab Hbc.
destruct a as [a| ]; simpl in Hab; simpl.
 destruct b as [b| ]; simpl in Hab, Hbc; [ idtac | contradiction ].
 destruct c as [c| ]; [ rewrite Hab; assumption | assumption ].

 destruct b as [b| ]; simpl in Hab, Hbc; [ contradiction | assumption ].
Qed.

End Qbar.

Close Scope Qbar_scope.

Add Parametric Relation : Qbar Qbar.qeq
 reflexivity proved by Qbar.eq_refl
 symmetry proved by Qbar.eq_sym
 transitivity proved by Qbar.eq_trans
 as qbar_qeq_rel.

Infix "<" := Qbar.lt : Qbar_scope.
Infix ">" := Qbar.gt : Qbar_scope.
Infix "+" := Qbar.add : Qbar_scope.
Infix "*" := Qbar.mul : Qbar_scope.
Infix "=" := Qbar.qeq : Qbar_scope.
