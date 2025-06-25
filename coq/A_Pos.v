(* positive natural, represented by nat *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Psatz.

Record pos := { p_val : nat }.

Declare Scope pos_scope.
Delimit Scope pos_scope with pos.
Bind Scope pos_scope with pos.

Theorem Nat_1_le_mul_add_1 : ∀ a b, (1 <= (a + 1) * (b + 1))%nat.
Proof.
intros.
do 2 rewrite Nat.add_1_r; cbn.
apply -> Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.

Hint Resolve Nat_1_le_mul_add_1 : core.

Module Pos.

Definition of_nat n := {| p_val := n - 1 |}.
Definition to_nat p := p_val p + 1.

Definition of_number (n : Number.int) : option pos :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos (Decimal.D0 Decimal.Nil) => None
      | Decimal.Pos n => Some (Pos.of_nat (Nat.of_uint n))
      | Decimal.Neg n => None
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : pos) : Number.int :=
  Number.IntDecimal (Decimal.Pos (Nat.to_uint (Pos.to_nat a))).

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Definition add a b := {| p_val := p_val a + p_val b + 1 |}.
Definition sub a b := {| p_val := p_val a - p_val b - 1 |}.
Definition mul a b := {| p_val := (p_val a + 1) * (p_val b + 1) - 1 |}.

Definition compare a b := p_val a ?= p_val b.
Definition eqb a b := p_val a =? p_val b.
Definition le a b := p_val a ≤ p_val b.
Definition lt a b := p_val a < p_val b.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a ≤ b" := (Pos.le a b) : pos_scope.
Notation "a < b" := (Pos.lt a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
Notation "a =? b" := (Pos.eqb a b) : pos_scope.

Theorem eq_dec : ∀ a b : pos, {a = b} + {a ≠ b}.
Proof.
intros.
destruct (Nat.eq_dec (p_val a) (p_val b)) as [Hab| Hab]. {
  left.
  destruct a as (a).
  destruct b as (b).
  now cbn in Hab; subst.
} {
  right; intros H; apply Hab; clear Hab.
  now subst.
}
Qed.

Theorem le_dec : ∀ a b : pos, ({a ≤ b} + {¬ a ≤ b})%pos.
Proof.
intros.
now destruct (le_dec (p_val a) (p_val b)); [ left | right ].
Qed.

Theorem add_comm : ∀ a b, (a + b)%pos = (b + a)%pos.
Proof.
intros.
progress unfold Pos.add.
now rewrite (Nat.add_comm (p_val a)).
Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%pos = (a + c + b)%pos.
Proof.
intros.
progress unfold Pos.add.
progress f_equal; cbn.
progress f_equal.
do 4 rewrite <- Nat.add_assoc.
progress f_equal.
do 2 rewrite (Nat.add_comm (p_val _)).
apply Nat.add_shuffle0.
Qed.

Theorem add_sub : ∀ a b, (a + b - b)%pos = a.
Proof.
intros.
progress unfold Pos.sub, Pos.add; cbn.
rewrite Nat.add_shuffle0, Nat.add_sub, Nat.add_sub.
now destruct a.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%pos = (b * a)%pos.
Proof.
intros.
progress unfold Pos.mul.
now rewrite (Nat.mul_comm (p_val a + 1)).
Qed.

Theorem mul_mul_swap : ∀ a b c, (a * b * c)%pos = (a * c * b)%pos.
Proof.
intros.
progress unfold Pos.mul.
progress f_equal; cbn.
progress f_equal.
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.sub_add; [ | easy ].
apply Nat.mul_shuffle0.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%pos = a.
Proof.
intros.
progress unfold Pos.mul; cbn.
rewrite Nat.add_0_r, Nat.add_sub.
now destruct a.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%pos = a.
Proof.
intros.
progress unfold Pos.mul; cbn.
rewrite Nat.mul_1_r, Nat.add_sub.
now destruct a.
Qed.

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c) = a * b + a * c)%pos.
Proof.
intros.
progress unfold Pos.mul, Pos.add; cbn.
progress f_equal.
rewrite (Nat.add_shuffle0 (p_val b)).
rewrite <- Nat.add_assoc.
rewrite Nat.mul_add_distr_l.
rewrite <- Nat.add_sub_swap; [ | easy ].
rewrite Nat.add_sub_assoc; [ | easy ].
symmetry; apply Nat.sub_add.
apply Nat.le_add_le_sub_l.
now apply Nat.add_le_mono.
Qed.

Theorem le_sub_1 : ∀ a b, (a ≤ b + 1 → a - b = 1)%pos.
Proof.
progress unfold Pos.sub, Pos.le.
intros * Hab.
cbn in Hab; rewrite Nat.add_0_r in Hab.
f_equal.
rewrite <- Nat.sub_add_distr.
now apply Nat.sub_0_le.
Qed.

Theorem add_sub_eq_l : ∀ a b c, (b + c = a → a - b = c)%pos.
Proof.
intros; subst.
rewrite Pos.add_comm.
apply Pos.add_sub.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem sub_sub_swap : ∀ a b c, (a - b - c = a - c - b)%pos.
Proof.
intros.
progress unfold Pos.sub; cbn.
progress f_equal.
progress f_equal.
do 2 rewrite (Nat_sub_sub_swap _ 1).
progress f_equal.
apply Nat_sub_sub_swap.
Qed.

Theorem ge_1 : ∀ a, (1 ≤ a)%pos.
Proof.
intros.
progress unfold Pos.le; cbn.
apply Nat.le_0_l.
Qed.

Theorem sub_add : ∀ a b, (b < a → a - b + b = a)%pos.
Proof.
intros * Hba.
progress unfold Pos.sub, Pos.add; cbn.
rewrite Nat.add_shuffle0.
rewrite Nat.sub_add. 2: {
  progress unfold Pos.lt in Hba.
  now apply Nat.lt_add_lt_sub_r.
}
rewrite Nat.sub_add. 2: {
  progress unfold Pos.lt in Hba.
  now apply Nat.lt_le_incl.
}
now destruct a.
Qed.

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%pos.
Proof.
intros * Hab Hbc.
eapply Nat.le_trans; [ apply Hab | easy ].
Qed.

Theorem lt_le_incl : ∀ a b, (a < b → a ≤ b)%pos.
Proof.
progress unfold Pos.lt, Pos.le.
intros * Hab.
now apply Nat.lt_le_incl.
Qed.

Theorem lt_le : ∀ a b, (a < b + 1 ↔ a ≤ b)%pos.
Proof.
progress unfold Pos.lt, Pos.le; cbn.
intros.
rewrite Nat.add_0_r.
rewrite Nat.add_1_r.
progress unfold Peano.lt.
now split; intros H; apply Nat.succ_le_mono in H.
Qed.

Theorem mul_sub_distr_l :
  ∀ a b c,
  (c < b)%pos
  → (a * (b - c) = a * b - a * c)%pos.
Proof.
intros * Hbc.
progress unfold Pos.lt, Pos.sub in Hbc; cbn in Hbc.
progress unfold Pos.mul, Pos.sub; cbn.
progress f_equal.
destruct a as (a).
destruct b as (b).
destruct c as (c).
cbn in Hbc |-*.
do 4 rewrite Nat.add_1_r; cbn.
do 3 rewrite Nat.sub_0_r.
do 3 rewrite (Nat.mul_comm _ (S _)); cbn.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l.
rewrite Nat.add_sub_assoc; [ lia | ].
rewrite <- Nat.mul_sub_distr_r.
rewrite <- (Nat.mul_1_l a) at 1.
apply Nat.mul_le_mono_r.
lia.
Qed.

Theorem nat_inj : ∀ a b, p_val a = p_val b → a = b.
Proof.
intros.
destruct a as (a).
destruct b as (b).
cbn in H; now subst.
Qed.

Theorem compare_match_dec :
  ∀ a b : pos, (a ?= b)%pos =
  match lt_eq_lt_dec (p_val a) (p_val b) with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
  end.
Proof. intros; apply nat_compare_equiv. Qed.

Theorem compare_antisym : ∀ a b, ((a ?= b) = CompOpp (b ?= a))%pos.
Proof. intros; apply Nat.compare_antisym. Qed.

Theorem compare_refl : ∀ a, (a ?= a)%pos = Eq.
Proof. intros; apply Nat.compare_refl. Qed.

Theorem compare_eq_iff : ∀ a b, (a ?= b)%pos = Eq ↔ a = b.
Proof.
intros.
progress unfold Pos.compare.
split; intros H; [ | subst; apply Pos.compare_refl ].
apply Nat.compare_eq_iff in H.
now apply Pos.nat_inj.
Qed.

Theorem to_nat_neq_0 : ∀ a, Pos.to_nat a ≠ 0.
Proof.
intros.
progress unfold Pos.to_nat.
now rewrite Nat.add_comm.
Qed.

End Pos.

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a < b" := (Pos.lt a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
Notation "a =? b" := (Pos.eqb a b) : pos_scope.
