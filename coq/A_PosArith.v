(* positive natural, represented by nat *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Relations.
From Stdlib Require Import Psatz.

Record pos := { p_val : nat }.

Declare Scope pos_scope.
Delimit Scope pos_scope with pos.
Bind Scope pos_scope with pos.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

(* misc theorems *)

Theorem Nat_1_le_mul_add_1 : ∀ a b, (1 <= (a + 1) * (b + 1))%nat.
Proof.
intros.
do 2 rewrite Nat.add_1_r; cbn.
apply -> Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.

Hint Resolve Nat_1_le_mul_add_1 : core.

Theorem Nat_compare_sub_mono_l :
  ∀ a b c,
  (b <= a)%nat
  → (c <= a)%nat
  → (a - b ?= a - c)%nat = (c ?= b)%nat.
Proof.
intros * Hle1 Hle2.
revert a b Hle1 Hle2.
induction c; intros; cbn. {
  rewrite Nat.sub_0_r.
  destruct b. {
    apply Nat.compare_eq_iff.
    apply Nat.sub_0_r.
  }
  apply Nat.compare_lt_iff.
  flia Hle1.
}
destruct b. {
  apply Nat.compare_gt_iff.
  rewrite Nat.sub_0_r.
  flia Hle2.
}
destruct a; [ easy | cbn ].
apply Nat.succ_le_mono in Hle1, Hle2.
apply (IHc _ _ Hle1 Hle2).
Qed.

Theorem Nat_compare_add_mono_l :
  ∀ a b c, (a + b ?= a + c)%nat = (b ?= c)%nat.
Proof.
intros.
revert a b.
induction c; intros; cbn. {
  rewrite Nat.add_0_r.
  destruct b. {
    apply Nat.compare_eq_iff.
    apply Nat.add_0_r.
  }
  apply Nat.compare_gt_iff.
  flia.
}
destruct b. {
  rewrite Nat.add_0_r; cbn.
  apply Nat.compare_lt_iff.
  flia.
}
cbn.
do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
apply IHc.
Qed.

Theorem Nat_compare_add_mono_r :
  ∀ a b c, (a + c ?= b + c)%nat = (a ?= b)%nat.
Proof.
intros.
do 2 rewrite (Nat.add_comm _ c).
apply Nat_compare_add_mono_l.
Qed.

Theorem Nat_compare_sub_mono_r :
  ∀ a b c,
  (c <= a)%nat
  → (c <= b)%nat
  → (a - c ?= b - c)%nat = (a ?= b)%nat.
Proof.
intros * Hle1 Hle2.
revert b c Hle1 Hle2.
induction a; intros; cbn. {
  apply Nat.le_0_r in Hle1; subst c.
  now rewrite Nat.sub_0_r.
}
destruct b. {
  now apply Nat.le_0_r in Hle2; subst c.
}
destruct c; [ easy | cbn ].
apply Nat.succ_le_mono in Hle1, Hle2.
apply (IHa _ _ Hle1 Hle2).
Qed.

Theorem Nat_compare_mul_mono_l :
  ∀ a b c, a ≠ 0 → (a * b ?= a * c) = (b ?= c).
Proof.
intros * Haz.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec (a * b) (a * c)) as [[H1| H1]| H1]. {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  easy.
  flia H1 H2.
  apply Nat.mul_lt_mono_pos_l in H1; [ | flia Haz ].
  now apply Nat.lt_asymm in H1.
} {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  apply Nat.mul_cancel_l in H1; [ flia H1 H2 | easy ].
  easy.
  apply Nat.mul_cancel_l in H1; [ flia H1 H2 | easy ].
} {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  apply Nat.mul_lt_mono_pos_l in H1; [ flia H1 H2 | flia Haz ].
  now subst c; apply Nat.lt_irrefl in H1.
  easy.
}
Qed.

Theorem Nat_compare_sub_add_l : ∀ a b c, b ≤ a → (a - b ?= c) = (a ?= b + c).
Proof.
intros * Hba.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec (a - b) c) as [[H1| H1]| H1]. {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  easy.
  flia H1 H2.
  flia H1 H2.
} {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  flia Hba H1 H2.
  easy.
  flia H1 H2.
} {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  flia H1 H2.
  flia H1 H2.
  easy.
}
Qed.

Theorem Nat_compare_sub_add_r : ∀ a b c, b ≤ a → (a - b ?= c) = (a ?= c + b).
Proof.
intros * Hba.
rewrite Nat.add_comm.
now apply Nat_compare_sub_add_l.
Qed.

(* end misc theorems *)

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

Theorem of_nat_to_nat : ∀ a, Pos.of_nat (Pos.to_nat a) = a.
Proof.
intros.
progress unfold Pos.of_nat, Pos.to_nat.
rewrite Nat.add_sub.
now destruct a.
Qed.

Theorem to_nat_of_nat : ∀ a, a ≠ 0 → Pos.to_nat (Pos.of_nat a) = a.
Proof.
intros * Haz.
progress unfold Pos.of_nat, Pos.to_nat; cbn.
apply Nat.sub_add.
now apply Nat.neq_0_lt_0.
Qed.

Theorem to_nat_neq_0 : ∀ a, Pos.to_nat a ≠ 0.
Proof.
intros.
progress unfold to_nat.
now rewrite Nat.add_1_r.
Qed.

Theorem add_to_nat_neq_0 : ∀ a b, Pos.to_nat a + Pos.to_nat b ≠ 0.
Proof.
intros * H.
apply Nat.eq_add_0 in H.
destruct H as (H, _).
now apply Pos.to_nat_neq_0 in H.
Qed.

Theorem add_to_nat_ge_1 : ∀ a b, 1 ≤ Pos.to_nat a + Pos.to_nat b.
Proof.
intros.
apply Nat.neq_0_lt_0.
apply Pos.add_to_nat_neq_0.
Qed.

Theorem mul_to_nat_neq_0 : ∀ a b, Pos.to_nat a * Pos.to_nat b ≠ 0.
Proof.
intros * H.
apply Nat.eq_mul_0 in H.
now destruct H as [H| H]; apply Pos.to_nat_neq_0 in H.
Qed.

Definition nat2 f a b := Pos.of_nat (f (Pos.to_nat a) (Pos.to_nat b)).

Definition add := nat2 Nat.add.
Definition sub := nat2 Nat.sub.
Definition mul := nat2 Nat.mul.

Definition nat2a {A} (f : nat → nat → A) a b :=
  f (Pos.to_nat a) (Pos.to_nat b).

Definition compare a b := p_val a ?= p_val b.
Definition eqb a b := p_val a =? p_val b.
Definition le := nat2a le.
Definition lt a b := p_val a < p_val b.

Definition div a b := Pos.of_nat (Pos.to_nat a / Pos.to_nat b).
Definition rem a b := Pos.of_nat (Pos.to_nat a mod Pos.to_nat b).

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
progress unfold Pos.le, nat2a.
now destruct (le_dec (to_nat a) (to_nat b)); [ left | right ].
Qed.

Theorem add_comm : ∀ a b, (a + b)%pos = (b + a)%pos.
Proof.
intros.
progress unfold Pos.add, nat2.
f_equal; apply Nat.add_comm.
Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%pos = (a + c + b)%pos.
Proof.
intros.
progress unfold Pos.add, nat2.
rewrite Pos.to_nat_of_nat; [ | apply Pos.add_to_nat_neq_0 ].
rewrite Pos.to_nat_of_nat; [ | apply Pos.add_to_nat_neq_0 ].
f_equal; apply Nat.add_shuffle0.
Qed.

Theorem add_sub : ∀ a b, (a + b - b)%pos = a.
Proof.
intros.
progress unfold Pos.sub, Pos.add, nat2; cbn.
rewrite Nat.sub_add; [ | apply Pos.add_to_nat_ge_1 ].
rewrite Nat.add_sub.
apply Pos.of_nat_to_nat.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%pos = (b * a)%pos.
Proof.
intros.
progress unfold Pos.mul, nat2.
f_equal; apply Nat.mul_comm.
Qed.

Theorem mul_mul_swap : ∀ a b c, (a * b * c)%pos = (a * c * b)%pos.
Proof.
intros.
progress unfold Pos.mul, nat2.
rewrite Pos.to_nat_of_nat; [ | apply Pos.mul_to_nat_neq_0 ].
rewrite Pos.to_nat_of_nat; [ | apply Pos.mul_to_nat_neq_0 ].
f_equal; apply Nat.mul_shuffle0.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%pos = ((a * b) * c)%pos.
Proof.
intros.
rewrite Pos.mul_comm.
rewrite Pos.mul_mul_swap.
progress f_equal.
apply Pos.mul_comm.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%pos = a.
Proof.
intros.
progress unfold Pos.mul, nat2.
rewrite Nat.mul_1_l.
apply Pos.of_nat_to_nat.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%pos = a.
Proof.
intros.
rewrite Pos.mul_comm.
apply Pos.mul_1_l.
Qed.

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c) = a * b + a * c)%pos.
Proof.
intros.
progress unfold Pos.mul, Pos.add, nat2; cbn.
progress f_equal.
rewrite Nat.sub_add; [ | apply Pos.add_to_nat_ge_1 ].
rewrite Nat.sub_add; [ | apply Nat.neq_0_lt_0, Pos.mul_to_nat_neq_0 ].
rewrite Nat.sub_add; [ | apply Nat.neq_0_lt_0, Pos.mul_to_nat_neq_0 ].
apply Nat.mul_add_distr_l.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem le_sub_1 : ∀ a b, (a ≤ b + 1 → a - b = 1)%pos.
Proof.
progress unfold Pos.sub, Pos.le, nat2, nat2a.
intros * Hab; cbn in Hab.
rewrite Nat.add_sub in Hab.
progress unfold Pos.of_nat.
f_equal.
apply Nat.sub_0_le.
now apply Nat.le_sub_le_add_l.
Qed.

Theorem add_sub_eq_l : ∀ a b c, (b + c = a → a - b = c)%pos.
Proof.
intros; subst.
rewrite Pos.add_comm.
apply Pos.add_sub.
Qed.

Theorem sub_sub_swap : ∀ a b c, (a - b - c = a - c - b)%pos.
Proof.
intros.
progress unfold Pos.sub, nat2; cbn.
progress unfold Pos.to_nat.
rewrite (Nat.add_comm (p_val b)).
rewrite (Nat.add_comm (p_val c)).
do 4 rewrite Nat.sub_add_distr.
do 3 rewrite Nat.add_sub.
rewrite Nat_sub_sub_swap.
rewrite (Nat_sub_sub_swap (p_val a)).
rewrite Nat_sub_sub_swap.
easy.
Qed.

Theorem le_1_l : ∀ a, (1 ≤ a)%pos.
Proof.
intros.
progress unfold Pos.le, nat2a; cbn.
progress unfold to_nat.
apply Nat.le_add_l.
Qed.

Theorem sub_add : ∀ a b, (b < a → a - b + b = a)%pos.
Proof.
intros * Hba.
progress unfold Pos.sub, Pos.add, nat2; cbn.
progress unfold Pos.to_nat.
rewrite (Nat.add_comm (p_val b)).
rewrite Nat.sub_add_distr.
rewrite Nat.add_sub.
rewrite Nat.add_assoc.
do 2 rewrite (Nat.add_shuffle0 _ _ (p_val b)).
rewrite <- Nat.add_sub_swap.
...
rewrite (Nat.add_comm (p_val c)).
...
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

Theorem lt_trans : ∀ a b c, (a < b → b < c → a < c)%pos.
Proof.
intros a b c Hab Hbc.
eapply Nat.lt_trans; [ apply Hab | easy ].
Qed.

Add Parametric Relation : _ Pos.le
  transitivity proved by Pos.le_trans
as le_rel.

Add Parametric Relation : _ Pos.lt
  transitivity proved by Pos.lt_trans
as lt_rel.

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
split; intros H; [ | subst; apply Pos.compare_refl ].
now apply Nat.compare_eq_iff, Pos.nat_inj in H.
Qed.

Theorem compare_lt_iff : ∀ a b, (a ?= b)%pos = Lt ↔ (a < b)%pos.
Proof. intros; apply Nat.compare_lt_iff. Qed.

Theorem compare_gt_iff : ∀ a b, (a ?= b)%pos = Gt ↔ (b < a)%pos.
Proof. intros; apply Nat.compare_gt_iff. Qed.

Theorem compare_le_iff : ∀ a b, (a ?= b)%pos ≠ Gt ↔ (a ≤ b)%pos.
Proof. intros; apply Nat.compare_le_iff. Qed.

Theorem eqb_refl : ∀ a, (a =? a)%pos = true.
Proof. intros; apply Nat.eqb_refl. Qed.

Theorem eqb_eq : ∀ a b, (a =? b)%pos = true ↔ a = b.
Proof.
intros.
split; intros H; [ | now subst; apply Nat.eqb_eq ].
now apply Nat.eqb_eq, Pos.nat_inj in H.
Qed.

Theorem to_nat_neq_0 : ∀ a, Pos.to_nat a ≠ 0.
Proof.
intros.
progress unfold Pos.to_nat.
now rewrite Nat.add_comm.
Qed.

Theorem to_nat_inj_add :
  ∀ a b, Pos.to_nat (a + b) = Pos.to_nat a + Pos.to_nat b.
Proof.
intros.
progress unfold Pos.to_nat; cbn.
rewrite (Nat.add_shuffle0 (p_val a)).
symmetry; apply Nat.add_assoc.
Qed.

Theorem to_nat_inj_mul :
  ∀ a b, Pos.to_nat (a * b) = Pos.to_nat a * Pos.to_nat b.
Proof.
intros.
progress unfold Pos.to_nat; cbn.
now apply Nat.sub_add.
Qed.

Theorem of_nat_inj_succ :
  ∀ a, a ≠ 0 → Pos.of_nat (S a) = (Pos.of_nat a + 1)%pos.
Proof.
intros * Haz.
progress unfold Pos.add; cbn.
rewrite Nat.add_0_r.
rewrite Nat.sub_add; [ | now apply Nat.neq_0_lt_0 ].
progress unfold Pos.of_nat; cbn.
now rewrite Nat.sub_0_r.
Qed.

Theorem of_nat_inj_le :
  ∀ a b, b ≠ 0 → (a ≤ b)%nat ↔ (Pos.of_nat a ≤ Pos.of_nat b)%pos.
Proof.
intros * Haz.
destruct b; [ easy | clear Haz ].
destruct a. {
  split; intros H; [ | apply Nat.le_0_l ].
  apply Pos.le_1_l.
}
progress unfold Pos.of_nat, Pos.le; cbn.
do 2 rewrite Nat.sub_0_r.
symmetry.
apply Nat.succ_le_mono.
Qed.

Theorem of_nat_inj_lt :
  ∀ a b, a ≠ 0 → (a < b)%nat ↔ (Pos.of_nat a < Pos.of_nat b)%pos.
Proof.
intros * Haz.
destruct b. {
  split; intros; [ easy | ].
  progress unfold Pos.of_nat, Pos.lt in H.
  cbn in H; flia H.
}
destruct a; [ easy | clear Haz ].
progress unfold Pos.of_nat, Pos.lt; cbn.
do 2 rewrite Nat.sub_0_r.
symmetry.
apply Nat.succ_lt_mono.
Qed.

Theorem of_nat_mul :
  ∀ a b,
  a ≠ 0
  → b ≠ 0
  → Pos.of_nat (a * b) = (Pos.of_nat a * Pos.of_nat b)%pos.
Proof.
intros * Haz Hbz.
progress unfold Pos.of_nat, Pos.mul; cbn.
progress f_equal.
destruct a; [ easy | ].
destruct b; [ easy | cbn ].
do 3 rewrite Nat.sub_0_r.
do 2 rewrite Nat.add_1_r.
rewrite (Nat.mul_comm _ (S _)); cbn.
rewrite (Nat.mul_comm _ (S _)); cbn.
now rewrite Nat.sub_0_r.
Qed.

(* gcd *)

Definition gcd a b := Pos.of_nat (Nat.gcd (Pos.to_nat a) (Pos.to_nat b)).

Theorem gcd_comm : ∀ a b, Pos.gcd a b = Pos.gcd b a.
Proof.
intros.
progress unfold Pos.gcd.
progress f_equal.
apply Nat.gcd_comm.
Qed.

(* end gcd *)

Theorem compare_sub_mono_l :
  ∀ a b c,
  (b < a)%pos
  → (c < a)%pos
  → (a - b ?= a - c)%pos = (c ?= b)%pos.
Proof.
intros * Hba Hca.
destruct a as (a).
destruct b as (b).
destruct c as (c).
progress unfold Pos.lt in Hba, Hca.
cbn in Hba, Hca |-*.
do 2 rewrite <- (Nat_sub_sub_swap _ 1).
apply Nat_compare_sub_mono_l; [ flia Hba | flia Hca ].
Qed.

Theorem compare_sub_mono_r :
  ∀ a b c,
  (c < a)%pos
  → (c < b)%pos
  → (a - c ?= b - c)%pos = (a ?= b)%pos.
Proof.
intros * Hca Hcb.
destruct a as (a).
destruct b as (b).
destruct c as (c).
progress unfold Pos.lt in Hca, Hcb.
cbn in Hca, Hcb |-*.
do 2 rewrite <- Nat.sub_add_distr.
apply Nat_compare_sub_mono_r; [ flia Hca | flia Hcb ].
Qed.

Theorem le_refl : ∀ a, (a ≤ a)%pos.
Proof. intros; apply Nat.le_refl. Qed.

Theorem lt_eq_cases : ∀ a b, (a ≤ b)%pos ↔ (a < b)%pos ∨ a = b.
Proof.
intros.
split; intros H. {
  apply Nat.lt_eq_cases in H.
  destruct H as [H| H]; [ now left | ].
  now right; apply Pos.nat_inj.
} {
  destruct H as [H| H]; [ now apply Pos.lt_le_incl | ].
  subst. apply Pos.le_refl.
}
Qed.

End Pos.

Number Notation pos Pos.of_number Pos.to_number : pos_scope.

Notation "a + b" := (Pos.add a b) : pos_scope.
Notation "a - b" := (Pos.sub a b) : pos_scope.
Notation "a * b" := (Pos.mul a b) : pos_scope.
Notation "a / b" := (Pos.div a b) : pos_scope.
Notation "a ≤ b" := (Pos.le a b) : pos_scope.
Notation "a < b" := (Pos.lt a b) : pos_scope.
Notation "a ?= b" := (Pos.compare a b) : pos_scope.
Notation "a =? b" := (Pos.eqb a b) : pos_scope.
Notation "a 'mod' b" := (Pos.rem a b) : pos_scope.
