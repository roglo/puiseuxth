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

Theorem Qbar_le_compat : ∀ a b c d,
  (a = b)%Qbar
  → (c = d)%Qbar
    → (a ≤ c)%Qbar
      → (b ≤ d)%Qbar.
Proof.
intros a b c d Hab Hcd Hac.
destruct d as [d| ]; [ idtac | constructor ].
destruct b as [b| ].
 apply Qbar.le_qfin.
 destruct c as [c| ]; [ idtac | inversion Hcd ].
 unfold Qbar.qeq in Hcd.
 rewrite <- Hcd.
 destruct a as [a| ]; [ idtac | inversion Hab ].
 unfold Qbar.qeq in Hab.
 rewrite <- Hab.
 inversion Hac; assumption.

 destruct c as [c| ]; [ idtac | inversion Hcd ].
 unfold Qbar.qeq in Hcd.
 destruct a as [a| ]; [ inversion Hab | inversion Hac ].
Qed.

Theorem Qbar_lt_compat : ∀ a b c d,
  (a = b)%Qbar
  → (c = d)%Qbar
    → (a < c)%Qbar
      → (b < d)%Qbar.
Proof.
intros a b c d Hab Hcd Hac.
destruct a as [a| ]; [ idtac | inversion Hac ].
destruct b as [b| ]; [ idtac | inversion Hab ].
unfold Qbar.qeq in Hab.
destruct d as [d| ]; [ idtac | constructor ].
apply Qbar.lt_qfin.
destruct c as [c| ]; [ idtac | inversion Hcd ].
unfold Qbar.qeq in Hcd.
rewrite <- Hab, <- Hcd.
inversion Hac; assumption.
Qed.

Lemma Qmin_same_den : ∀ a b c, Qmin (a # c) (b # c) = Z.min a b # c.
Proof.
intros a b c.
unfold Qmin; simpl.
destruct (Qlt_le_dec (a # c) (b # c)) as [Hlt| Hge]; f_equal.
 unfold Qlt in Hlt; simpl in Hlt.
 apply Zmult_lt_reg_r in Hlt; [ idtac | apply Pos2Z.is_pos ].
 rewrite Z.min_l; [ reflexivity | apply Z.lt_le_incl; assumption ].

 unfold Qle in Hge; simpl in Hge.
 apply Zmult_le_reg_r in Hge; [ idtac | apply Z.lt_gt, Pos2Z.is_pos ].
 rewrite Z.min_r; [ reflexivity | assumption ].
Qed.

Add Parametric Morphism : Qbar.le
  with signature Qbar.qeq ==> Qbar.qeq ==> iff
  as qbar_le_morph.
Proof.
intros a b Hab c d Hcd.
split; intros H.
 eapply Qbar_le_compat; eassumption.

 symmetry in Hab, Hcd.
 eapply Qbar_le_compat; eassumption.
Qed.

Add Parametric Morphism : Qbar.lt
  with signature Qbar.qeq ==> Qbar.qeq ==> iff
  as qbar_lt_morph.
Proof.
intros a b Hab c d Hcd.
split; intros H.
 eapply Qbar_lt_compat; eassumption.

 symmetry in Hab, Hcd.
 eapply Qbar_lt_compat; eassumption.
Qed.

Add Parametric Morphism : Qbar.min
  with signature Qbar.qeq ==> Qbar.qeq ==> Qbar.qeq
  as qbar_min_morph.
Proof.
intros a b Hab c d Hcd.
unfold Qbar.min, Qbar.binop.
destruct a as [a| ].
 destruct b as [b| ]; [ idtac | inversion Hab ].
 apply Qbar.qfin_inj in Hab.
 destruct c as [c| ].
  destruct d as [d| ]; [ idtac | inversion Hcd ].
  apply Qbar.qfin_inj in Hcd.
  unfold Qmin; simpl.
  destruct (Qlt_le_dec a c) as [Hlt| Hge]; [ idtac | inversion Hcd ].
   destruct (Qlt_le_dec b d) as [Hlt'| Hge]; [ assumption | idtac ].
   rewrite Hab, Hcd in Hlt.
   apply Qle_not_lt in Hge.
   contradiction.

   destruct (Qlt_le_dec b d) as [Hlt| Hge']; [ idtac | assumption ].
   rewrite Hab, Hcd in Hge.
   apply Qle_not_lt in Hge.
   contradiction.

  destruct d as [d| ]; [ inversion Hcd | assumption ].

 destruct b as [b| ]; [ inversion Hab | assumption ].
Qed.
