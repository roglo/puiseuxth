(* Nbar.v *)

Require Import Utf8.
Require Import Compare_dec.
Require Import Arith.

Require Import Misc.

Ltac negation H := exfalso; apply H; reflexivity.

Set Implicit Arguments.

Inductive Nbar : Set :=
  | fin : ∀ x : nat, Nbar
  | inf : Nbar.

Declare Scope Nbar_scope.
Delimit Scope Nbar_scope with Nbar.
Bind Scope Nbar_scope with Nbar.

Notation "∞" := inf.
Notation "0" := (fin 0) : Nbar_scope.
Notation "1" := (fin 1) : Nbar_scope.

Definition NS n :=
  match n with
  | fin n => fin (S n)
  | ∞ => ∞
  end.

Open Scope Nbar_scope.

Module Nbar.

Definition binop f dx dy xb yb :=
  match xb with
  | fin x =>
      match yb with
      | fin y => fin (f x y)
      | ∞ => dx
      end
  | ∞ => dy
  end.

Definition add := binop plus ∞ ∞.
Definition mul := binop mult ∞ ∞.
Definition max := binop max ∞ ∞.
Definition min x y := binop min x y x y.

Definition sub xb yb :=
  match yb with
  | fin y =>
      match xb with
      | fin x => fin (minus x y)
      | ∞ => ∞
      end
  | ∞ => 0
  end.

Definition div xb yb :=
  match yb with
  | fin y =>
      match xb with
      | fin x => fin (Nat.div x y)
      | ∞ => ∞
      end
  | ∞ => 0
  end.

Infix "+" := add : Nbar_scope.
Infix "-" := sub : Nbar_scope.
Infix "*" := mul : Nbar_scope.
Infix "/" := div : Nbar_scope.

Inductive le : Nbar → Nbar → Prop :=
  | le_fin : ∀ n m, (n <= m)%nat → fin n ≤ fin m
  | le_inf : ∀ n, n ≤ ∞
where "n ≤ m" := (le n m) : Nbar_scope.

Inductive lt : Nbar → Nbar → Prop :=
  | lt_fin : ∀ n m, (n < m)%nat → fin n < fin m
  | lt_inf : ∀ n, fin n < ∞
where "n < m" := (lt n m) : Nbar_scope.

Theorem fin_inj_wd : ∀ n1 n2, fin n1 = fin n2 ↔ n1 = n2.
Proof.
intros n₁ n₂.
split; intros H; [ inversion H | subst ]; reflexivity.
Qed.

Theorem add_comm : ∀ n m, n + m = m + n.
Proof.
intros n m.
destruct n; [ simpl | destruct m; reflexivity ].
destruct m; [ rewrite Nat.add_comm; reflexivity | reflexivity ].
Qed.

Theorem mul_comm : ∀ n m, n * m = m * n.
Proof.
intros n m.
destruct n; [ simpl | destruct m; reflexivity ].
destruct m; [ rewrite Nat.mul_comm; reflexivity | reflexivity ].
Qed.

Theorem lt_irrefl : ∀ n, ¬(n < n).
Proof.
intros n.
destruct n as [n| ].
 intros H.
 inversion H; revert H2; apply Nat.lt_irrefl.

 intros H; inversion H.
Qed.

Theorem fin_le_mono : ∀ n m, (n <= m)%nat ↔ fin n ≤ fin m.
Proof.
intros n m.
split; intros H; [ constructor; assumption | idtac ].
inversion H; assumption.
Qed.

Theorem fin_lt_mono : ∀ n m, (n < m)%nat ↔ fin n < fin m.
Proof.
intros n m.
split; intros H; [ constructor; assumption | idtac ].
inversion H; assumption.
Qed.

Theorem succ_lt_mono : ∀ n m, n < m ↔ NS n < NS m.
Proof.
intros n m.
split; intros H.
 destruct n as [n| ]; [ simpl | destruct m; inversion H ].
 destruct m as [m| ]; [ simpl | constructor ].
 apply fin_lt_mono, Nat.succ_lt_mono in H.
 apply fin_lt_mono; assumption.

 destruct n as [n| ]; [ simpl | destruct m; inversion H ].
 destruct m as [m| ]; [ simpl in H | constructor ].
 apply fin_lt_mono, Nat.succ_lt_mono.
 apply fin_lt_mono; assumption.
Qed.

Theorem add_lt_mono_r : ∀ n m p, p ≠ ∞ → n < m ↔ n + p < m + p.
Proof.
intros n m p Hp.
split; intros H.
 destruct n as [n| ].
  destruct m as [m| ].
   destruct p as [p| ].
    constructor; apply Nat.add_lt_mono_r; inversion H; assumption.

    negation Hp.

   destruct p as [p| ]; [ constructor | negation Hp ].

  destruct m; inversion H.

 destruct n as [n| ]; [ idtac | inversion H ].
 destruct m as [m| ]; [ idtac | constructor ].
 destruct p as [p| ]; [ idtac | inversion H ].
 constructor; inversion H; apply Nat.add_lt_mono_r in H2; assumption.
Qed.

Theorem add_lt_mono_l : ∀ n m p, p ≠ ∞ → n < m ↔ p + n < p + m.
Proof.
intros n m p Hp.
rewrite add_comm.
replace (p + m) with (m + p) by apply add_comm.
apply add_lt_mono_r; assumption.
Qed.

Theorem mul_lt_mono_pos_r : ∀ p n m, 0 < p → p ≠ ∞ → n ≠ ∞ →
  n < m ↔ n * p < m * p.
Proof.
intros p n m Hp Hpi Hni.
destruct p as [p| ]; [ simpl | negation Hpi ].
destruct n as [n| ]; [ simpl | negation Hni ].
destruct m as [m| ]; simpl.
 split; intros.
  constructor.
  apply Nat.mul_lt_mono_pos_r; [ inversion Hp | inversion H ]; assumption.

  constructor.
  eapply Nat.mul_lt_mono_pos_r; [ inversion Hp | inversion H ]; eassumption.

 split; intros H; constructor.
Qed.

Theorem mul_0_r : ∀ n, n ≠ inf → n * 0 = 0.
Proof.
intros n Hn.
destruct n; [ apply mul_comm; reflexivity | negation Hn ].
Qed.

Theorem eq_dec : ∀ n m : Nbar, {n = m} + {n ≠ m}.
Proof.
intros n m.
destruct n as [n| ].
 destruct m as [m| ].
  destruct (Nat.eq_dec n m) as [Hlt| Hge].
   left; subst; reflexivity.

   right; intros H; apply Hge.
   inversion H; subst; reflexivity.

  right; intros H; discriminate H.

 destruct m as [m| ].
  right; intros H; discriminate H.

  left; reflexivity.
Qed.

Theorem le_dec : ∀ (n m : Nbar), {n ≤ m} + {~ n ≤ m}.
Proof.
intros n m.
destruct n as [n| ].
 destruct m as [m| ].
  destruct (le_dec n m) as [Hlt| Hge].
   left; constructor; assumption.

   right; intros H; apply Hge; clear Hge.
   inversion H; assumption.

  left; constructor.

 destruct m as [m| ]; [ right; intros H; inversion H | idtac ].
 left; constructor.
Qed.

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

 destruct m as [m| ]; [ right; intros H; inversion H | idtac ].
 right; intros H; inversion H.
Qed.

Theorem min_dec : ∀ n m, {min n m = n} + {min n m = m}.
Proof.
intros n m.
destruct n as [n| ]; [ idtac | destruct m; right; reflexivity ].
destruct m as [m| ]; [ idtac | left; reflexivity ].
destruct (Nat.min_dec n m) as [H| H].
 left; apply fin_inj_wd; assumption.

 right; apply fin_inj_wd; assumption.
Qed.

Theorem lt_trans : ∀ n m p, n < m → m < p → n < p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ].
 destruct m as [m| ]; [ simpl | inversion Hmp ].
 destruct n as [n| ]; [ simpl | inversion Hnm ].
 inversion Hnm; inversion Hmp; constructor.
 eapply Nat.lt_trans; eassumption.

 destruct n as [n| ]; [ constructor | inversion Hnm ].
Qed.

Theorem lt_le_trans : ∀ n m p, n < m → m ≤ p → n < p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ].
 destruct m as [m| ]; [ simpl | inversion Hmp ].
 destruct n as [n| ]; [ simpl | inversion Hnm ].
 inversion Hnm; inversion Hmp; constructor.
 eapply Nat.lt_le_trans; eassumption.

 destruct n as [n| ]; [ constructor | inversion Hnm ].
Qed.

Theorem le_lt_trans : ∀ n m p, n ≤ m → m < p → n < p.
Proof.
intros n m p Hnm Hmp.
destruct p as [p| ].
 destruct m as [m| ]; [ simpl | inversion Hmp ].
 destruct n as [n| ]; [ simpl | inversion Hnm ].
 inversion Hnm; inversion Hmp; constructor.
 eapply Nat.le_lt_trans; eassumption.

 destruct n as [n| ]; [ constructor | inversion Hnm ].
 subst m; assumption.
Qed.

Theorem le_0_l : ∀ n, 0 ≤ n.
Proof.
intros n.
destruct n as [n| ]; [ idtac | constructor ].
constructor; apply Nat.le_0_l.
Qed.

Theorem le_0_r : ∀ n, n ≤ 0 ↔ n = 0.
Proof.
intros n.
split; intros Hn.
 destruct n as [n| ]; [ idtac | inversion Hn ].
 apply fin_inj_wd.
 apply fin_le_mono in Hn.
 apply Nat.le_0_r; assumption.

 subst n; apply le_0_l.
Qed.

Theorem nle_gt : ∀ n m, ¬n ≤ m ↔ m < n.
Proof.
intros n m.
split; intros H.
 destruct n as [n| ].
  destruct m as [m| ]; [ idtac | exfalso; apply H; constructor ].
  apply fin_lt_mono, Nat.nlt_ge.
  intros I; apply H.
  apply fin_le_mono, le_S_n; assumption.

  destruct m; [ constructor | exfalso; apply H; constructor ].

 destruct n as [n| ].
  destruct m as [m| ]; [ idtac | inversion H ].
  apply fin_lt_mono, Nat.nle_gt in H.
  intros I; apply H; clear H.
  apply fin_le_mono; assumption.

  destruct m; [ intros I; inversion I | inversion H ].
Qed.

Theorem nlt_ge : ∀ n m, ¬(n < m) ↔ m ≤ n.
Proof.
intros n m.
split; intros H.
 destruct n as [n| ]; [ idtac | constructor ].
 destruct m as [m| ].
  apply fin_le_mono, Nat.nlt_ge.
  intros I; apply H.
  apply fin_lt_mono; assumption.

  exfalso; apply H; constructor.

 destruct n as [n| ].
  destruct m as [m| ]; [ idtac | inversion H ].
  apply fin_le_mono, Nat.nlt_ge in H.
  intros I; apply H.
  apply fin_lt_mono; assumption.

  destruct m; intros I; inversion I.
Qed.

Theorem lt_add_lt_sub_r : ∀ n m p, n + p < m ↔ n < m - p.
Proof.
intros n m p.
split; intros H.
 destruct m as [m| ]; simpl.
  destruct p as [p| ]; simpl.
   destruct n as [n| ]; simpl.
    apply fin_lt_mono in H.
    apply fin_lt_mono.
    apply Nat.lt_add_lt_sub_r; assumption.

    exfalso; apply nle_gt in H; apply H; constructor.

   exfalso; apply nle_gt in H; apply H; rewrite add_comm; constructor.

  destruct p as [p| ]; simpl.
   destruct n as [n| ]; [ constructor | simpl ].
   exfalso; apply nle_gt in H; apply H; constructor.

   exfalso; apply nle_gt in H; apply H; rewrite add_comm; constructor.

 destruct m as [m| ]; simpl.
  destruct p as [p| ]; simpl.
   destruct n as [n| ]; simpl.
    apply fin_lt_mono in H.
    apply fin_lt_mono.
    apply Nat.lt_add_lt_sub_r; assumption.

    exfalso; apply nle_gt in H; apply H; constructor.

   exfalso; apply nle_gt in H; apply H, le_0_l.

  destruct p as [p| ]; simpl.
   destruct n as [n| ]; [ constructor | simpl ].
   exfalso; apply nle_gt in H; apply H; constructor.

   exfalso; apply nle_gt in H; apply H, le_0_l.
Qed.

Theorem nlt_0_r : ∀ n, ¬(n < 0).
Proof.
intros n H.
destruct n as [n| ]; [ idtac | inversion H ].
inversion_clear H.
revert H0; apply Nat.nlt_0_r.
Qed.

Theorem mul_div_le : ∀ a b, b ≠ 0 → b ≠ ∞ → b * (a / b) ≤ a.
Proof.
intros a b Hb Hbi.
destruct a as [a| ]; [ idtac | constructor ].
destruct b as [b| ]; [ simpl | exfalso; apply Hbi; reflexivity ].
apply le_fin.
apply Nat.mul_div_le.
intros H; apply Hb.
subst b; reflexivity.
Qed.

Theorem div_mul : ∀ a b, b ≠ 0 → b ≠ ∞ → a * b / b = a.
Proof.
intros a b Hb Hbi.
destruct b as [b| ]; [ idtac | exfalso; apply Hbi; reflexivity ].
destruct b as [| b]; [ exfalso; apply Hb; reflexivity | simpl ].
destruct a as [a| ]; [ simpl | reflexivity ].
rewrite divmod_div.
rewrite Nat.div_mul; [ reflexivity | idtac ].
intros H; discriminate H.
Qed.

Theorem div_lt_upper_bound : ∀ a b q, b ≠ 0 → b ≠ ∞ → a < b * q → a / b < q.
Proof.
intros a b q Hb Hbi Ha.
destruct a as [a| ].
 destruct b as [b| ].
  destruct q as [q| ]; [ idtac | constructor ].
  apply fin_lt_mono.
  destruct b as [| b].
   exfalso; revert Ha; apply nlt_0_r.

   apply Nat.div_lt_upper_bound.
    intros H; discriminate H.

    apply fin_lt_mono; assumption.

  exfalso; apply Hbi; reflexivity.

 destruct b as [b| ]; [ inversion Ha | idtac ].
 exfalso; apply Hbi; reflexivity.
Qed.

Theorem lt_sub_lt_add_r : ∀ n m p, n ≠ ∞ → n - p < m → n < m + p.
Proof.
intros n m p Hn H.
destruct n as [n| ].
 destruct m as [m| ]; [ simpl | constructor ].
 destruct p as [p| ]; [ idtac | constructor ].
 constructor; apply Nat.lt_sub_lt_add_r.
 inversion H; subst; assumption.

 negation Hn.
Qed.

Theorem sub_add_distr : ∀ n m p, n - (m + p) = n - m - p.
Proof.
intros n m p.
destruct m as [m| ]; [ simpl | destruct p; reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.sub_add_distr; reflexivity.
Qed.

Theorem sub_gt : ∀ n m, m < n → n - m ≠ 0.
Proof.
intros n m Hmn.
destruct n as [n| ]; simpl.
 destruct m as [m| ]; simpl.
  apply fin_lt_mono in Hmn.
  apply Nat.sub_gt in Hmn.
  intros H; apply Hmn.
  injection H; clear H; intros H; rewrite H; reflexivity.

  inversion Hmn.

 destruct m as [m| ]; simpl.
  intros H; discriminate H.

  inversion Hmn.
Qed.

Theorem sub_diag : ∀ n, n - n = 0.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.sub_diag; reflexivity.
Qed.

Theorem eq_add_0 : ∀ n m, n + m = 0 ↔ n = 0 ∧ m = 0.
Proof.
intros n m.
destruct n as [n| ]; simpl.
 destruct m as [m| ]; simpl.
  split; intros H.
   injection H; clear H; intros H.
   apply Nat.eq_add_0 in H.
   destruct H; subst; split; reflexivity.

   destruct H as (Hn, Hm).
   injection Hn; intros; subst.
   injection Hm; intros; subst; reflexivity.

  split; intros H; [ discriminate H | destruct H; assumption ].

 split; intros H; [ discriminate H | destruct H; assumption ].
Qed.

Theorem add_shuffle0 : ∀ n m p, n + m + p = n + p + m.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | destruct p; reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
rewrite Nat.add_shuffle0; reflexivity.
Qed.

Theorem add_assoc : ∀ n m p, n + (m + p) = n + m + p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ rewrite Nat.add_assoc; reflexivity | reflexivity ].
Qed.

Theorem add_sub_assoc : ∀ n m p, p ≠ ∞ → p ≤ m → n + (m - p) = n + m - p.
Proof.
intros n m p Hp Hpm.
destruct n as [n| ]; simpl.
 destruct m as [m| ]; simpl.
  destruct p as [p| ]; [ simpl | exfalso; apply Hp; reflexivity ].
  apply fin_le_mono in Hpm.
  rewrite Nat.add_sub_assoc; [ reflexivity | assumption ].

  destruct p as [p| ]; [ reflexivity | exfalso; apply Hp; reflexivity ].

 destruct p as [p| ]; [ reflexivity | exfalso; apply Hp; reflexivity ].
Qed.

Theorem sub_sub_distr : ∀ n m p, m ≠ ∞ → p ≤ m → n - (m - p) = n + p - m.
Proof.
intros n m p Hm Hpm.
destruct m as [m| ]; [ idtac | exfalso; apply Hm; reflexivity ].
destruct p as [p| ].
 destruct n as [n| ]; [ simpl | reflexivity ].
 apply fin_le_mono in Hpm.
 rewrite Nat_sub_sub_distr; [ reflexivity | assumption ].

 exfalso; apply nlt_ge in Hpm; apply Hpm; constructor.
Qed.

Theorem mul_eq_0_l : ∀ n m, n * m = 0 → m ≠ 0 → n = 0.
Proof.
intros n m Hnm Hm.
destruct n as [n| ]; [ idtac | assumption ].
destruct m as [m| ]; simpl in Hnm; [ idtac | contradiction ].
injection Hnm; clear Hnm; intros Hnm.
apply Nat.mul_eq_0_l in Hnm; [ subst n; reflexivity | idtac ].
intros H; apply Hm; subst m; reflexivity.
Qed.

Theorem mul_shuffle0 : ∀ n m p, n * m * p = n * p * m.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | destruct p; reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
rewrite Nat.mul_shuffle0; reflexivity.
Qed.

Theorem mul_assoc : ∀ n m p, n * (m * p) = n * m * p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ rewrite Nat.mul_assoc; reflexivity | reflexivity ].
Qed.

Theorem mul_1_r : ∀ n, n * fin 1 = n.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.mul_1_r; reflexivity.
Qed.

Theorem mul_add_distr_r : ∀ n m p, (n + m) * p = n * p + m * p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ simpl | destruct m; reflexivity ].
destruct m; [ simpl | reflexivity ].
rewrite Nat.mul_add_distr_r; reflexivity.
Qed.

Theorem mul_sub_distr_r : ∀ n m p, p ≠ ∞ → (n - m) * p = n * p - m * p.
Proof.
intros n m p Hp.
destruct p as [p| ]; [ simpl | negation Hp ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.mul_sub_distr_r; reflexivity.
Qed.

Theorem min_id : ∀ n, min n n = n.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.min_id; reflexivity.
Qed.

Theorem max_id : ∀ n, max n n = n.
Proof.
intros n.
destruct n as [n| ]; [ simpl | reflexivity ].
rewrite Nat.max_id; reflexivity.
Qed.

Theorem add_max_distr_r : ∀ n m p, max (n + p) (m + p) = max n m + p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ simpl | destruct m; reflexivity ].
destruct m; [ simpl | reflexivity ].
rewrite Nat.add_max_distr_r; reflexivity.
Qed.

Theorem mul_max_distr_r : ∀ n m p, max (n * p) (m * p) = max n m * p.
Proof.
intros n m p.
destruct n as [n| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ simpl | destruct m; reflexivity ].
destruct m; [ simpl | reflexivity ].
rewrite Nat.mul_max_distr_r; reflexivity.
Qed.

Theorem max_comm : ∀ n m, max n m = max m n.
Proof.
intros n m.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
rewrite Nat.max_comm; reflexivity.
Qed.

Theorem max_assoc : ∀ m n p, max m (max n p) = max (max m n) p.
Proof.
intros m n p.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ simpl | reflexivity ].
destruct p as [p| ]; [ simpl | reflexivity ].
rewrite Nat.max_assoc; reflexivity.
Qed.

Theorem min_l : ∀ n m, n ≤ m → min n m = n.
Proof.
intros n m H.
destruct m as [m| ]; [ idtac | destruct n; reflexivity ].
destruct n as [n| ]; [ simpl | inversion H ].
rewrite Nat.min_l; [ reflexivity | inversion H; assumption ].
Qed.

Theorem max_l : ∀ n m, m ≤ n → max n m = n.
Proof.
intros n m H.
destruct n as [n| ]; [ simpl | destruct m; reflexivity ].
destruct m as [m| ]; [ idtac | inversion H ].
rewrite Nat.max_l; [ reflexivity | inversion H; assumption ].
Qed.

Theorem le_add_r : ∀ n m, n ≤ n + m.
Proof.
intros n m.
destruct n as [n| ]; [ idtac | constructor ].
destruct m as [m| ]; [ simpl | constructor ].
apply le_fin, Nat.le_add_r.
Qed.

Theorem le_max_l : ∀ n m, n ≤ max n m.
Proof.
intros n m.
destruct n as [n| ]; [ idtac | constructor ].
destruct m as [m| ]; [ simpl | constructor ].
apply fin_le_mono, Nat.le_max_l.
Qed.

Theorem le_max_r : ∀ n m, m ≤ max n m.
Proof.
intros n m.
destruct n as [n| ]; [ idtac | constructor ].
destruct m as [m| ]; [ simpl | constructor ].
apply fin_le_mono, Nat.le_max_r.
Qed.

Theorem max_lt_iff : ∀ n m p, p < max n m ↔ p < n ∨ p < m.
Proof.
intros n m p.
split; intros H.
 destruct p as [p| ]; [ idtac | inversion H ].
 destruct n as [n| ]; [ idtac | left; constructor ].
 destruct m as [m| ]; [ idtac | right; constructor ].
 inversion_clear H; subst.
 apply Nat.max_lt_iff in H0.
 destruct H0; [ left | right ]; constructor; assumption.

 destruct p as [p| ]; [ idtac | destruct H; inversion H ].
 destruct n as [n| ]; [ idtac | constructor ].
 destruct m as [m| ]; [ idtac | constructor ].
 constructor.
 apply Nat.max_lt_iff.
 destruct H as [H| H]; [ left | right ]; inversion H; assumption.
Qed.

Theorem lt_le_incl : ∀ n m, n < m → n ≤ m.
Proof.
intros n m H.
destruct n as [n| ]; [ idtac | inversion H ].
destruct m as [m| ]; [ idtac | constructor ].
constructor; apply Nat.lt_le_incl; inversion H; assumption.
Qed.

Theorem add_0_l : ∀ n, 0 + n = n.
Proof.
intros n.
destruct n; reflexivity.
Qed.

Theorem add_0_r : ∀ n, n + 0 = n.
Proof.
intros n.
destruct n as [n| ]; [ idtac | reflexivity ].
simpl; rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem sub_0_r : ∀ n, n - 0 = n.
Proof.
intros n.
destruct n as [n| ]; [ idtac | reflexivity ].
simpl; rewrite Nat.sub_0_r; reflexivity.
Qed.

End Nbar.

Infix "+" := Nbar.add : Nbar_scope.
Infix "-" := Nbar.sub : Nbar_scope.
Infix "*" := Nbar.mul : Nbar_scope.
Infix "/" := Nbar.div : Nbar_scope.
Infix "<" := Nbar.lt : Nbar_scope.

Close Scope Nbar_scope.

Notation "x ≤ y" := (Nbar.le x y) (at level 70) : Nbar_scope.
