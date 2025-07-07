(* Qbar.v *)

From Stdlib Require Import Utf8 Relations Morphisms.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.

Set Implicit Arguments.

Inductive Qbar : Set :=
  | qfin : ∀ x : Q, Qbar
  | qinf : Qbar.

Declare Scope Qbar_scope.
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

Definition add := binop Q.add ∞ ∞.
Definition mul := binop Q.mul ∞ ∞.
Definition min x y := binop Q.min x y x y.

Definition sub xb yb :=
  match yb with
  | qfin y =>
      match xb with
      | qfin x => qfin (Q.sub x y)
      | ∞ => ∞
      end
  | ∞ => 0
  end.

Definition opp x :=
  match x with
  | qfin x => qfin (-x)
  | ∞ => 0
  end.

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
Infix "-" := sub : Qbar_scope.
Infix "*" := mul : Qbar_scope.
Notation "- a" := (opp a) : Qbar_scope.

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

Theorem qfin_le_mono : ∀ n m, (n <= m)%Q ↔ qfin n ≤ qfin m.
Proof.
intros n m.
split; intros H; [ constructor; assumption | idtac ].
inversion H; assumption.
Qed.

Theorem qfin_inj : ∀ a b, qeq (qfin a) (qfin b) → a == b.
Proof. intros a b Hab; assumption. Qed.

Theorem qfin_inj_add : ∀ n m, qfin (n + m) = qfin n + qfin m.
Proof. reflexivity. Qed.

Theorem qfin_inj_wd : ∀ a b, qeq (qfin a) (qfin b) ↔ a == b.
Proof. intros a b; split; intros H; assumption. Qed.

Theorem eq_dec : ∀ a b, {qeq a b} + {not (qeq a b)}.
Proof.
intros a b.
destruct a as [a| ]; simpl. {
  destruct b as [b| ]; [ apply Q.eq_dec | now right ].
}
destruct b as [b| ]; [ now right | now left ].
Qed.

Theorem min_dec : ∀ n m, {min n m = n} + {min n m = m}.
Proof.
intros n m.
destruct n as [n| ]; [ idtac | destruct m; right; reflexivity ].
destruct m as [m| ]; [ idtac | left; reflexivity ].
destruct (Q.min_dec n m) as [H| H]; simpl; rewrite H. {
  left; reflexivity.
} {
  right; reflexivity.
}
Qed.

Theorem min_comm : ∀ n m, qeq (min n m) (min m n).
Proof.
intros n m.
destruct n as [n| ]; [ | now destruct m; cbn ].
destruct m as [m| ]; [ | now cbn ].
progress unfold qeq; cbn.
apply Q.min_comm.
Qed.

Theorem min_l : ∀ n m, n ≤ m → qeq (min n m) n.
Proof.
intros n m H.
destruct m as [m| ]; [ | now destruct n; cbn ].
destruct n as [n| ]; [ simpl | inversion H ].
rewrite Q.min_l; [ reflexivity | inversion H; assumption ].
Qed.

Theorem min_glb : ∀ n m p, p ≤ n → p ≤ m → p ≤ min n m.
Proof.
intros n m p Hpn Hpm.
destruct (min_dec n m) as [H| H]; rewrite H; assumption.
Qed.

Theorem min_glb_lt : ∀ n m p, p < n → p < m → p < min n m.
Proof.
intros n m p Hpn Hpm.
destruct (min_dec n m) as [H| H]; rewrite H; assumption.
Qed.

Theorem lt_irrefl : ∀ x, ¬(x < x).
Proof.
intros x H.
destruct x as [x| ]; [ idtac | inversion H ].
apply qfin_lt_mono in H.
revert H; apply Q.lt_irrefl.
Qed.

Theorem lt_neq : ∀ n m, n < m → not (qeq n m).
Proof.
intros n m Hlt.
intros H.
destruct n as [n| ]. {
  destruct m as [m| ]; [ idtac | inversion H ].
  apply qfin_lt_mono in Hlt.
  apply qfin_inj in H.
  rewrite H in Hlt.
  revert Hlt; apply Q.lt_irrefl.
}
destruct m as [m| ]; [ inversion H | inversion Hlt ].
Qed.

Theorem le_trans : ∀ n m p, n ≤ m → m ≤ p → n ≤ p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ]. {
  destruct m as [m| ]; [ simpl | inversion Hmp ].
  destruct n as [n| ]; [ simpl | inversion Hnm ].
  inversion Hnm; inversion Hmp; constructor.
  eapply Q.le_trans; eassumption.
}
destruct n as [n| ]; [ constructor | idtac ].
inversion Hnm; subst; assumption.
Qed.

Theorem lt_le_trans : ∀ n m p, n < m → m ≤ p → n < p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ]. {
  destruct m as [m| ]; [ simpl | inversion Hmp ].
  destruct n as [n| ]; [ simpl | inversion Hnm ].
  inversion Hnm; inversion Hmp; constructor.
  eapply Q.lt_le_trans; eassumption.
}
destruct n as [n| ]; [ constructor | inversion Hnm ].
Qed.

Theorem le_lt_trans : ∀ n m p, n ≤ m → m < p → n < p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ]. {
  destruct m as [m| ]; [ simpl | inversion Hmp ].
  destruct n as [n| ]; [ simpl | inversion Hnm ].
  inversion Hnm; inversion Hmp; constructor.
  eapply Q.le_lt_trans; eassumption.
}
destruct n as [n| ]; [ constructor | idtac ].
inversion Hnm; subst; assumption.
Qed.

Theorem add_comm : ∀ n m, n + m = m + n.
Proof.
intros n m.
destruct n; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
progress f_equal.
apply Q.add_comm.
Qed.

Theorem add_0_l : ∀ a, qeq (0 + a) a.
Proof.
intros a.
destruct a as [a| ]; [ simpl | constructor ].
rewrite Q.add_0_l; reflexivity.
Qed.

Theorem add_lt_mono_r : ∀ n m p, p ≠ ∞ → n < m ↔ n + p < m + p.
Proof.
intros n m p Hp.
split; intros H. {
  destruct n as [n| ]. {
    destruct m as [m| ]. {
      destruct p as [p| ]. {
        now constructor; apply Q.add_lt_mono_r; inversion H.
      }
      exfalso; apply Hp; reflexivity.
    }
    destruct p as [p| ]; [ constructor | exfalso; apply Hp; reflexivity ].
  }
  inversion H.
}
destruct n as [n| ]; [ idtac | inversion H ].
destruct m as [m| ]; [ idtac | constructor ].
destruct p as [p| ]; [ idtac | inversion H ].
constructor; inversion H.
now apply Q.add_lt_mono_r in H2.
Qed.

Theorem add_lt_le_mono : ∀ n m p q,
  p ≠ ∞
  → n < m
  → p ≤ q
  → n + p < m + q.
Proof.
intros n m p q Hp Hnm Hpq.
destruct m as [m| ]; simpl. {
  destruct n as [n| ]; [ idtac | inversion Hnm ].
  apply qfin_lt_mono in Hnm.
  destruct q as [q| ]; simpl. {
    destruct p as [p| ]; [ idtac | inversion Hpq ].
    apply qfin_le_mono in Hpq.
    apply qfin_lt_mono.
    now apply Q.add_lt_le_compat.
  }
  destruct p as [p| ]; [ constructor | idtac ].
  exfalso; apply Hp; reflexivity.
}
destruct p as [p| ]; [ idtac | exfalso; apply Hp; reflexivity ].
destruct n as [n| ]; [ idtac | inversion Hnm ].
constructor.
Qed.

Theorem add_le_mono_r : ∀ n m p, p ≠ ∞ → n ≤ m ↔ n + p ≤ m + p.
Proof.
intros n m p Hp.
split; intros H. {
  destruct n as [n| ]. {
    destruct m as [m| ]. {
      destruct p as [p| ]. {
        now constructor; apply Q.add_le_mono_r; inversion H.
      }
      exfalso; apply Hp; reflexivity.
    }
    destruct p as [p| ]; [ constructor | exfalso; apply Hp; reflexivity ].
  }
  inversion H; constructor.
}
destruct n as [n| ]. {
  destruct m as [m| ]; [ idtac | constructor ].
  destruct p as [p| ]; [ idtac | exfalso; apply Hp; reflexivity ].
  constructor; inversion H.
  now apply Q.add_le_mono_r in H2.
} {
  destruct m as [m| ]; [ idtac | constructor ].
  destruct p as [p| ]; [ idtac | exfalso; apply Hp; reflexivity ].
  inversion H.
}
Qed.

Theorem lt_sub_lt_add_l : ∀ n m p, n ≠ ∞ → n - m < p → n < m + p.
Proof.
intros n m p Hn H.
destruct m as [m| ]. {
  destruct p as [p| ]. {
    destruct n as [n| ]; [ simpl in H; simpl | inversion H ].
    apply lt_qfin.
    apply qfin_lt_mono in H.
    apply Qlt_sub_lt_add_l; assumption.
  }
  destruct n as [n| ]; [ constructor | inversion H ].
}
destruct n as [n| ]; [ constructor | idtac ].
exfalso; apply Hn; reflexivity.
Qed.

Theorem le_sub_le_add_l : ∀ n m p, n - m ≤ p → n ≤ m + p.
Proof.
intros n m p H.
destruct m as [m| ]; [ idtac | constructor ].
destruct p as [p| ]; [ idtac | rewrite add_comm; constructor ].
destruct n as [n| ]; [ simpl in H; simpl | inversion H ].
apply le_qfin.
apply qfin_le_mono in H.
apply Qle_sub_le_add_l; assumption.
Qed.

Theorem lt_le_incl : ∀ n m, n < m → n ≤ m.
Proof.
intros n m H.
destruct n as [n| ]; [ idtac | inversion H ].
destruct m as [m| ]; [ idtac | constructor ].
constructor; apply Q.lt_le_incl; inversion H; assumption.
Qed.

Theorem sub_diag : ∀ n, qeq (n - n) 0.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
apply Q.sub_diag.
Qed.

Theorem sub_0_l : ∀ n, qeq (0 - n) (-n).
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
progress unfold Q.sub.
now rewrite Q.add_0_l.
Qed.

Theorem mul_0_r : ∀ a, a ≠ ∞ → qeq (a * 0) 0.
Proof.
intros a Ha.
destruct a as [a| ]; simpl; [ idtac | apply Ha; reflexivity ].
now rewrite Q.mul_0_r.
Qed.

Theorem eq_refl : reflexive _ qeq.
Proof.
intros a.
destruct a; [ now cbn | easy ].
Qed.

Theorem eq_sym : symmetric _ qeq.
Proof.
intros a b Hab.
destruct a; [ idtac | assumption ].
destruct b; [ now cbn | easy ].
Qed.

Theorem eq_trans : transitive _ qeq.
Proof.
intros a b c Hab Hbc.
destruct a as [a| ]; simpl in Hab; simpl. {
  destruct b as [b| ]; simpl in Hab, Hbc; [ idtac | contradiction ].
  destruct c as [c| ]; [ rewrite Hab; assumption | assumption ].
}
destruct b as [b| ]; simpl in Hab, Hbc; [ contradiction | assumption ].
Qed.

End Qbar.

Close Scope Qbar_scope.

Add Parametric Relation : Qbar Qbar.qeq
  reflexivity proved by Qbar.eq_refl
  symmetry proved by Qbar.eq_sym
  transitivity proved by Qbar.eq_trans
  as qbar_qeq_rel.

Global Instance qbar_qfin_morph : Proper (Q.eq ==> Qbar.qeq) qfin.
Proof. easy. Qed.

Global Instance qbar_add_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> Qbar.qeq) Qbar.add.
Proof.
intros a b Hab c d Hcd.
destruct a as [a| ]; simpl. {
 destruct c as [c| ]; simpl. {
   destruct b as [b| ]; [ simpl | contradiction ].
   destruct d as [d| ]; [ simpl | contradiction ].
   apply Qbar.qfin_inj in Hab.
   apply Qbar.qfin_inj in Hcd.
   rewrite Hab, Hcd; reflexivity.
 }
 destruct b as [b| ]; [ simpl | constructor ].
 destruct d as [d| ]; [ contradiction | constructor ].
}
destruct b as [b| ]; [ contradiction | constructor ].
Qed.

Infix "<" := Qbar.lt : Qbar_scope.
Infix ">" := Qbar.gt : Qbar_scope.
Infix "≤" := Qbar.le : Qbar_scope.
Infix "≥" := Qbar.ge : Qbar_scope.
Infix "+" := Qbar.add : Qbar_scope.
Infix "-" := Qbar.sub : Qbar_scope.
Infix "*" := Qbar.mul : Qbar_scope.
Infix "=" := Qbar.qeq : Qbar_scope.
Notation "- a" := (Qbar.opp a) : Qbar_scope.
Notation "a ≠ b" := (¬Qbar.qeq a b) : Qbar_scope.

Theorem Qbar_le_compat : ∀ a b c d,
  (a = b)%Qbar
  → (c = d)%Qbar
  → (a ≤ c)%Qbar
  → (b ≤ d)%Qbar.
Proof.
intros a b c d Hab Hcd Hac.
destruct d as [d| ]; [ idtac | constructor ].
destruct b as [b| ]. {
  apply Qbar.le_qfin.
  destruct c as [c| ]; [ idtac | inversion Hcd ].
  unfold Qbar.qeq in Hcd.
  rewrite <- Hcd.
  destruct a as [a| ]; [ idtac | inversion Hab ].
  unfold Qbar.qeq in Hab.
  rewrite <- Hab.
  inversion Hac; assumption.
}
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

Theorem Qmin_same_den : ∀ a b c, Q.min (a # c) (b # c) = Z.min a b # c.
Proof.
intros a b c.
unfold Q.min; simpl.
destruct (Q.lt_le_dec (a # c) (b # c)) as [Hlt| Hge]; f_equal. {
  apply -> Z.compare_lt_iff in Hlt.
  cbn in Hlt.
  do 2 rewrite q_Den_num_den in Hlt.
  apply Z.mul_lt_mono_pos_r in Hlt; [ | easy ].
  symmetry.
  now apply Z.min_l, Z.lt_le_incl.
} {
  apply -> Z.compare_le_iff in Hge.
  cbn in Hge.
  do 2 rewrite q_Den_num_den in Hge.
  apply Z.mul_le_mono_pos_r in Hge; [ | easy ].
  symmetry.
  now apply Z.min_r.
}
Qed.

Theorem eq_Qbar_qinf : ∀ a, (a = ∞)%Qbar → a = ∞%Qbar.
Proof. intros a H; destruct a; auto; inversion H. Qed.

Global Instance qbar_le_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> iff) Qbar.le.
Proof.
intros a b Hab c d Hcd.
split; intros H. {
  eapply Qbar_le_compat; eassumption.
}
symmetry in Hab, Hcd.
eapply Qbar_le_compat; eassumption.
Qed.

Global Instance qbar_ge_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> iff) Qbar.ge.
Proof.
intros a b Hab c d Hcd.
apply qbar_le_morph; assumption.
Qed.

Global Instance qbar_lt_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> iff) Qbar.lt.
Proof.
intros a b Hab c d Hcd.
split; intros H. {
  eapply Qbar_lt_compat; eassumption.
}
symmetry in Hab, Hcd.
eapply Qbar_lt_compat; eassumption.
Qed.

Global Instance qbar_gt_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> iff) Qbar.gt.
Proof.
intros a b Hab c d Hcd.
apply qbar_lt_morph; assumption.
Qed.

Global Instance qbar_min_morph :
  Proper (Qbar.qeq ==> Qbar.qeq ==> Qbar.qeq) Qbar.min.
Proof.
intros a b Hab c d Hcd.
unfold Qbar.min, Qbar.binop.
destruct a as [a| ]. {
  destruct b as [b| ]; [ idtac | inversion Hab ].
  apply Qbar.qfin_inj in Hab.
  destruct c as [c| ]. {
    destruct d as [d| ]; [ idtac | inversion Hcd ].
    apply Qbar.qfin_inj in Hcd.
    unfold Q.min; simpl.
    destruct (Q.lt_le_dec a c) as [Hlt| Hge]; [ idtac | inversion Hcd ]. {
      destruct (Q.lt_le_dec b d) as [Hlt'| Hge]; [ assumption | idtac ].
      rewrite Hab, Hcd in Hlt.
      now apply Q.nlt_ge in Hge.
    }
    destruct (Q.lt_le_dec b d) as [Hlt| Hge']; [ idtac | assumption ].
    rewrite Hab, Hcd in Hge.
    now apply Q.nlt_ge in Hge.
  }
  destruct d as [d| ]; [ inversion Hcd | assumption ].
}
destruct b as [b| ]; [ inversion Hab | assumption ].
Qed.
