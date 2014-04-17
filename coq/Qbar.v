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

Definition Qmin x y := if Qlt_le_dec x y then x else y.

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
Definition min x y := binop Qmin x y x y.

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

Inductive le : Qbar → Qbar → Prop :=
  | le_qfin : ∀ q r, (q <= r)%Q → qfin q ≤ qfin r
  | le_qinf : ∀ q, q ≤ ∞
where "q ≤ r" := (le q r) : Qbar_scope.

Inductive lt : Qbar → Qbar → Prop :=
  | lt_qfin : ∀ q r, (q < r)%Q → qfin q < qfin r
  | lt_qinf : ∀ q, qfin q < ∞
where "q < r" := (lt q r) : Qbar_scope.

Definition gt q r := lt r q.
Definition ge q r := le r q.

Theorem qfin_lt_mono : ∀ n m, (n < m)%Q ↔ qfin n < qfin m.
Proof.
intros n m.
split; intros H; [ constructor; assumption | idtac ].
inversion H; assumption.
Qed.

Theorem qfin_inj : ∀ a b, qeq (qfin a) (qfin b) → a == b.
Proof. intros a b Hab; assumption. Qed.

Theorem qfin_inj_wd : ∀ a b, qeq (qfin a) (qfin b) ↔ a == b.
Proof. intros a b; split; intros H; assumption. Qed.

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

Add Parametric Morphism : Qbar.add
  with signature Qbar.qeq ==> Qbar.qeq ==> Qbar.qeq
  as qbar_add_morph.
Proof.
intros a b Hab c d Hcd.
destruct a as [a| ]; simpl.
 destruct c as [c| ]; simpl.
  destruct b as [b| ]; [ simpl | contradiction ].
  destruct d as [d| ]; [ simpl | contradiction ].
  apply Qbar.qfin_inj in Hab.
  apply Qbar.qfin_inj in Hcd.
  rewrite Hab, Hcd; reflexivity.

  destruct b as [b| ]; [ simpl | constructor ].
  destruct d as [d| ]; [ contradiction | constructor ].

 destruct b as [b| ]; [ contradiction | constructor ].
Qed.

Infix "<" := Qbar.lt : Qbar_scope.
Infix ">" := Qbar.gt : Qbar_scope.
Infix "≤" := Qbar.le : Qbar_scope.
Infix "≥" := Qbar.ge : Qbar_scope.
Infix "+" := Qbar.add : Qbar_scope.
Infix "*" := Qbar.mul : Qbar_scope.
Infix "=" := Qbar.qeq : Qbar_scope.

Theorem Qbar_le_compat_l : ∀ a b c,
  (a = b)%Qbar
  → (a ≤ c)%Qbar
    → (b ≤ c)%Qbar.
Proof.
intros a b c Hab Hac.
destruct a as [a| ].
 destruct b as [b| ]; [ idtac | inversion Hab ].
 apply Qbar.qfin_inj in Hab.
 destruct c as [c| ]; [ idtac | constructor ].
 apply Qbar.le_qfin.
 inversion Hac; subst.
 rewrite Hab in H1; assumption.

 destruct b as [b| ]; [ inversion Hab | idtac ].
 destruct c as [c| ]; [ inversion Hac | idtac ].
 constructor.
Qed.
