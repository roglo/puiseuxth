(** * A ℚ arithmetics *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Morphisms.
Require Import A_PosArith A_ZArith.

Record Q := mk_q
  { q_num : Z;
    q_den : pos }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Definition q_Den a := Z.of_pos (q_den a).

(* misc *)

Theorem Nat_sub_lt_mono_l :
  ∀ a b c, (c < a ∨ b <= a → c < b → a - b < a - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem Nat_sub_lt_mono_r :
  ∀ a b c, (c < b ∨ c <= a → a < b → a - c < b - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem Nat_add_1_r_pos : ∀ a, (0 < a + 1)%nat.
Proof. flia. Qed.

Theorem q_Den_num_den : ∀ a b, q_Den (mk_q a b) = Z.of_pos b.
Proof. easy. Qed.

Theorem q_Den_neq_0 : ∀ a, q_Den a ≠ 0%Z.
Proof. easy. Qed.

Theorem q_Den_pos : ∀ a, (0 < q_Den a)%Z.
Proof. easy. Qed.

Theorem q_Den_nonneg : ∀ a, (0 ≤ q_Den a)%Z.
Proof. easy. Qed.

Hint Resolve Nat_add_1_r_pos : core.
Hint Resolve q_Den_pos : core.

(* end misc *)

Module Q.

Open Scope Z_scope.

Definition add a b :=
  mk_q
    (q_num a * q_Den b + q_num b * q_Den a)
    (Pos.mul (q_den a) (q_den b)).

Definition opp a := mk_q (- q_num a) (q_den a).
Definition sub a b := add a (opp b).

Definition mul a b :=
  mk_q (q_num a * q_num b) (Pos.mul (q_den a) (q_den b)).

Definition inv a :=
  mk_q (Z.sgn (q_num a) * q_Den a) (Z.to_pos (Z.abs (q_num a))).

Definition div a b := mul a (inv b).

Definition compare a b :=
  q_num a * q_Den b ?= q_num b * q_Den a.

Definition eq a b := Q.compare a b = Eq.
Definition le a b := Q.compare a b ≠ Gt.
Definition lt a b := Q.compare a b = Lt.

Definition of_number (n : Number.int) : option Q :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_q (Z.of_nat (Nat.of_uint n)) 1)
      | Decimal.Neg n => Some (mk_q (- Z.of_nat (Nat.of_uint n)) 1)
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Q) : option Number.int :=
  match q_den a with
  | 1%pos => Some (Z.to_number (q_num a))
  | _ => None
  end.

Number Notation Q of_number to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a '⁻¹'" := (Q.inv a) (at level 1, format "a ⁻¹") : Q_scope.
Notation "a ≤ b" := (Q.le a b) : Q_scope.
Notation "a < b" := (Q.lt a b) : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a (b - 1)) (at level 55) : Q_scope.

Theorem q_Den_mul : ∀ a b, q_Den (a * b) = (q_Den a * q_Den b)%Z.
Proof. easy. Qed.

Theorem eq_refl : ∀ a, (a == a)%Q.
Proof.
now intros; apply Z.compare_eq_iff.
Qed.

Theorem eq_symm : ∀ a b, (a == b → b == a)%Q.
Proof.
intros * H.
apply Z.compare_eq_iff in H.
apply Z.compare_eq_iff.
easy.
Qed.

Theorem eq_trans : ∀ a b c, (a == b → b == c → a == c)%Q.
Proof.
intros * Hab Hbc.
progress unfold eq in Hab, Hbc |-*.
apply Z.compare_eq_iff in Hab, Hbc.
apply Z.compare_eq_iff.
apply (f_equal (Z.mul (q_Den c))) in Hab.
apply (f_equal (Z.mul (q_Den a))) in Hbc.
do 2 rewrite (Z.mul_comm (q_Den c)) in Hab.
rewrite (Z.mul_comm (q_num b)) in Hab.
rewrite (Z.mul_comm (q_num c)) in Hbc.
do 2 rewrite Z.mul_assoc in Hbc.
rewrite Hbc in Hab.
do 2 rewrite <- (Z.mul_mul_swap _ _ (q_Den b)) in Hab.
rewrite (Z.mul_comm (q_Den a)) in Hab.
now apply Z.mul_cancel_r in Hab.
Qed.

Add Parametric Relation : Q Q.eq
  reflexivity proved by eq_refl
  symmetry proved by eq_symm
  transitivity proved by eq_trans
  as eq_rel.

Theorem add_comm : ∀ a b, (a + b)%Q = (b + a)%Q.
Proof.
intros.
progress unfold add.
rewrite Z.add_comm.
rewrite Pos.mul_comm.
easy.
Qed.

Theorem fold_q_Den : ∀ a, Z.of_pos (q_den a) = q_Den a.
Proof. easy. Qed.

Theorem add_assoc : ∀ a b c, (a + (b + c))%Q = ((a + b) + c)%Q.
Proof.
intros.
progress unfold Q.add.
cbn.
do 2 rewrite q_Den_num_den.
rewrite Pos.mul_assoc.
progress f_equal.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite Z.mul_add_distr_r.
do 2 rewrite Z.mul_assoc.
rewrite <- Z.add_assoc.
progress f_equal.
do 2 rewrite (Z.mul_mul_swap _ _ (q_Den a)).
easy.
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Q = a.
Proof.
intros.
progress unfold add; cbn.
rewrite Z.mul_1_r, Pos.mul_1_l.
now destruct a.
Qed.

Theorem add_0_r : ∀ a, (a + 0)%Q = a.
Proof.
intros.
rewrite add_comm.
apply add_0_l.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%Q = (b * a)%Q.
Proof.
intros.
progress unfold mul.
progress unfold Pos.mul.
now rewrite Z.mul_comm, Nat.mul_comm.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Q = ((a * b) * c)%Q.
Proof.
intros.
progress unfold mul.
progress unfold Pos.mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
now rewrite Z.mul_assoc, Nat.mul_assoc.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Q = a.
Proof.
intros.
progress unfold mul.
rewrite Z.mul_1_l, Pos.mul_1_l.
now destruct a.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Q = a.
Proof.
intros.
rewrite mul_comm.
apply mul_1_l.
Qed.

Theorem opp_involutive : ∀ a, (- - a)%Q = a.
Proof.
intros.
progress unfold opp; cbn.
rewrite Z.opp_involutive.
now destruct a.
Qed.

Theorem nle_gt : ∀ a b, ¬ (a ≤ b)%Q ↔ (b < a)%Q.
Proof. intros; apply Z.nle_gt. Qed.

Theorem le_antisymm : ∀ a b, (a ≤ b)%Q → (b ≤ a)%Q → (a == b)%Q.
Proof.
intros * Hab Hba.
progress unfold Q.le in Hab, Hba.
progress unfold Q.eq.
apply Z.compare_le_iff in Hab, Hba.
apply Z.compare_eq_iff.
now apply Z.le_antisymm.
Qed.

Theorem le_refl : ∀ a, (a ≤ a)%Q.
Proof. intros; apply Z.le_refl. Qed.

Theorem lt_le_incl : ∀ a b, (a < b)%Q → (a ≤ b)%Q.
Proof. intros * Hab; congruence. Qed.

Theorem mul_opp_l : ∀ x y, ((- x) * y = - (x * y))%Q.
Proof.
intros.
progress unfold "*"%Q.
progress unfold Q.opp.
progress f_equal.
apply Z.mul_opp_l.
Qed.

Theorem mul_opp_r : ∀ x y, (x * - y = - (x * y))%Q.
Proof.
intros.
do 2 rewrite (Q.mul_comm x).
apply Q.mul_opp_l.
Qed.

Theorem order_eq_le_l : ∀ a b c, (a == b → c ≤ b → c ≤ a)%Q.
Proof.
intros * Heq Hle.
apply Z.compare_eq_iff in Heq.
apply Z.compare_le_iff in Hle.
apply Z.compare_le_iff.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite (Z.mul_comm (q_num a)), <- (Z.mul_assoc (q_Den c)), Heq.
rewrite Z.mul_mul_swap, Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem order_eq_le_r : ∀ a b c, (a == b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Heq Hle.
apply Z.compare_eq_iff in Heq.
apply Z.compare_le_iff in Hle.
apply Z.compare_le_iff.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite (Z.mul_comm (q_num a)), <- (Z.mul_assoc (q_Den c)), Heq.
rewrite Z.mul_mul_swap, Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem add_compat_l : ∀ a b c, (b == c → a + b == a + c)%Q.
Proof.
intros * Heq.
apply Z.compare_eq_iff in Heq.
apply Z.compare_eq_iff.
cbn.
do 2 rewrite (Z.mul_comm (_ + _)).
do 2 rewrite (Z.add_comm (q_num a * _)).
progress unfold Q.add.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite Z.mul_add_distr_l.
do 4 rewrite Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)), Heq.
rewrite (Z.mul_comm (q_num c)).
progress f_equal.
rewrite Z.mul_comm, <- Z.mul_assoc.
progress f_equal.
apply Z.mul_comm.
Qed.

Theorem add_compat_r : ∀ a b c, (a == b → a + c == b + c)%Q.
Proof.
intros * Heq.
do 2 rewrite (Q.add_comm _ c).
now apply Q.add_compat_l.
Qed.

Theorem mul_compat_l : ∀ a b c, (b == c → a * b == a * c)%Q.
Proof.
intros * Heq.
apply Z.compare_eq_iff in Heq.
apply Z.compare_eq_iff; cbn.
do 2 rewrite Q.q_Den_mul.
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite (Z.mul_comm (q_num _)).
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite (Z.mul_comm _ (q_num _)).
easy.
Qed.

Theorem mul_compat_r : ∀ a b c, (a == b → a * c == b * c)%Q.
Proof.
intros * Heq.
do 2 rewrite (Q.mul_comm _ c).
now apply Q.mul_compat_l.
Qed.

Theorem lt_le_dec: ∀ a b, ({a < b} + {b ≤ a})%Q.
Proof.
intros.
progress unfold Q.lt, Q.le.
apply Z.lt_le_dec.
Qed.

Global Instance add_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.add.
Proof.
intros a b Hab c d Hcd.
transitivity (a + d)%Q.
now apply Q.add_compat_l.
now apply Q.add_compat_r.
Qed.

Global Instance opp_morph : Proper (Q.eq ==> Q.eq) Q.opp.
Proof.
intros a b Hab.
apply Z.compare_eq_iff in Hab.
apply Z.compare_eq_iff.
progress unfold Q.opp; cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Z.mul_opp_l.
now f_equal.
Qed.

Theorem sub_compat_l : ∀ a b c, (b == c → a - b == a - c)%Q.
Proof.
intros * Heq.
progress unfold Q.sub.
apply Q.add_compat_l.
now rewrite Heq.
Qed.

Theorem sub_compat_r : ∀ a b c, (a == b → a - c == b - c)%Q.
Proof.
intros * Heq.
progress unfold Q.sub.
do 2 rewrite (Q.add_comm _ (- c)).
now apply Q.add_compat_l.
Qed.

Global Instance sub_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.sub.
Proof.
intros a b Hab c d Hcd.
transitivity (a - d)%Q.
now apply Q.sub_compat_l.
now apply Q.sub_compat_r.
Qed.

Global Instance mul_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.mul.
Proof.
intros a b Hab c d Hcd.
transitivity (a * d)%Q.
now apply Q.mul_compat_l.
now apply Q.mul_compat_r.
Qed.

Global Instance inv_morph : Proper (Q.eq ==> Q.eq) Q.inv.
Proof.
intros a b Hab.
apply Z.compare_eq_iff in Hab.
apply Z.compare_eq_iff; cbn.
progress unfold Q.inv; cbn.
do 2 rewrite q_Den_num_den.
destruct (Z.eq_dec (q_num a) 0) as [Haz| Haz]. {
  rewrite Haz in Hab |-*.
  cbn in Hab |-*.
  symmetry in Hab.
  apply Z.integral in Hab.
  cbn in Hab.
  destruct Hab as [Hab| Hab]; [ now rewrite Hab | easy ].
}
destruct (Z.eq_dec (q_num b) 0) as [Hbz| Hbz]. {
  rewrite Hbz in Hab |-*.
  cbn in Hab |-*.
  apply Z.integral in Hab.
  cbn in Hab.
  destruct Hab as [Hab| Hab]; [ now rewrite Hab | easy ].
}
rewrite Z2Pos.id. 2: {
  destruct (q_num b) as [| sb vb]; [ easy | cbn ].
  replace 1 with (Z.of_nat 1) by easy.
  apply Nat2Z.inj_le.
  progress unfold Pos.to_nat.
  apply Nat.le_add_l.
}
rewrite Z2Pos.id. 2: {
  destruct (q_num a) as [| sa va]; [ easy | cbn ].
  replace 1 with (Z.of_nat 1) by easy.
  apply Nat2Z.inj_le.
  progress unfold Pos.to_nat.
  apply Nat.le_add_l.
}
(**)
do 2 rewrite <- Z.mul_assoc.
f_equal. {
  apply (f_equal Z.sgn) in Hab.
  do 2 rewrite Z.sgn_mul in Hab.
  progress unfold q_Den in Hab.
  now do 2 rewrite Z.mul_1_r in Hab.
}
do 2 rewrite (Z.mul_comm (q_Den _)).
symmetry.
destruct (Z.le_dec (q_num a) 0) as [Haz1| Haz1]. {
  rewrite (Z.abs_nonpos_eq (q_num a)); [ | easy ].
  rewrite Z.mul_opp_l.
  destruct (Z.le_dec (q_num b) 0) as [Hbz1| Hbz1]. {
    rewrite (Z.abs_nonpos_eq (q_num b)); [ | easy ].
    rewrite Z.mul_opp_l.
    now f_equal.
  } {
    exfalso.
    apply Z.nle_gt in Hbz1.
    apply Z.nlt_ge in Haz1.
    apply Haz1; clear Haz1.
    apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
    rewrite Hab; cbn.
    now apply Z.mul_pos_pos.
  }
}
destruct (Z.le_dec (q_num b) 0) as [Hbz1| Hbz1]. {
  exfalso.
  apply Haz1; clear Haz1.
  apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
  rewrite Hab; cbn.
  apply Z.mul_nonpos_nonneg; [ easy | apply q_Den_nonneg ].
}
apply Z.nle_gt, Z.lt_le_incl in Haz1, Hbz1.
rewrite Z.abs_nonneg_eq; [ | easy ].
rewrite Z.abs_nonneg_eq; [ | easy ].
easy.
Qed.

Global Instance div_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.div.
Proof.
intros a b Hab c d Hcd.
progress unfold Q.div.
transitivity (a * d⁻¹)%Q; [ | now apply Q.mul_compat_r ].
rewrite Hcd.
apply Q.mul_compat_l.
apply Q.eq_refl.
Qed.

Global Instance le_morph : Proper (Q.eq ==> Q.eq ==> iff) Q.le.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
split; intros Hac. {
  apply (@Q.order_eq_le_l _ c); [ now symmetry | ].
  now apply (@Q.order_eq_le_r _ a).
} {
  apply (@Q.order_eq_le_r _ b); [ easy | ].
  now apply (@Q.order_eq_le_l _ d).
}
Qed.

Theorem lt_iff : ∀ a b, (a < b)%Q ↔ (a ≤ b)%Q ∧ ¬ (a == b)%Q.
Proof.
intros.
split. {
  intros Hlt.
  split; [ now apply Q.lt_le_incl | ].
  intros H.
  apply Q.nle_gt in Hlt.
  apply Hlt; clear Hlt.
  rewrite H.
  apply Q.le_refl.
} {
  intros (Hle, Heq).
  apply Q.nle_gt.
  intros H; apply Heq; clear Heq.
  now apply Q.le_antisymm.
}
Qed.

Theorem order_eq_lt_l : ∀ a b c, (a == b → c < b → c < a)%Q.
Proof.
intros * Heq Hlt.
generalize Hlt; intros Hle.
apply Q.lt_le_incl in Hle.
apply Q.lt_iff.
split; [ now apply (Q.order_eq_le_l _ b) | ].
intros H.
rewrite <- H in Heq.
clear a H Hle.
apply Q.nle_gt in Hlt.
apply Hlt; clear Hlt.
rewrite Heq.
apply Q.le_refl.
Qed.

Theorem order_eq_lt_r : ∀ a b c, (a == b → b < c → a < c)%Q.
Proof.
intros * Heq Hlt.
generalize Hlt; intros Hle.
apply Q.lt_le_incl in Hle.
apply Q.lt_iff.
split; [ now apply (Q.order_eq_le_r _ b) | ].
intros H.
rewrite H in Heq.
clear a H Hle.
apply Q.nle_gt in Hlt.
apply Hlt; clear Hlt.
rewrite Heq.
apply Q.le_refl.
Qed.

Theorem compare_eq_iff : ∀ a b, (a ?= b)%Q = Eq ↔ (a == b)%Q.
Proof. easy. Qed.

Theorem compare_lt_iff : ∀ a b, (a ?= b)%Q = Lt ↔ (a < b)%Q.
Proof. easy. Qed.

Theorem compare_le_iff : ∀ a b, (a ?= b)%Q ≠ Gt ↔ (a ≤ b)%Q.
Proof. easy. Qed.

Theorem compare_gt_iff : ∀ a b, (a ?= b)%Q = Gt ↔ (b < a)%Q.
Proof. intros; apply Z.compare_gt_iff. Qed.

Global Instance lt_morph : Proper (Q.eq ==> Q.eq ==> iff) Q.lt.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
split; intros Hac. {
  apply (@Q.order_eq_lt_l _ c); [ now symmetry | ].
  now apply (@Q.order_eq_lt_r _ a).
} {
  apply (@Q.order_eq_lt_r _ b); [ easy | ].
  now apply (@Q.order_eq_lt_l _ d).
}
Qed.

Global Instance compare_morph : Proper (Q.eq ==> Q.eq ==> Logic.eq) Q.compare.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
remember (b ?= d)%Q as e eqn:He.
symmetry in He.
destruct e. {
  apply Q.compare_eq_iff in He.
  apply Q.compare_eq_iff.
  transitivity b; [ easy | ].
  transitivity d; [ easy | ].
  easy.
} {
  apply -> Q.compare_lt_iff in He.
  apply Q.compare_lt_iff.
  now rewrite Hab, Hcd.
} {
  apply Q.compare_gt_iff in He.
  apply Q.compare_gt_iff.
  now rewrite Hab, Hcd.
}
Qed.

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Hle1 Hle2.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.le_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_le_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem lt_le_trans : ∀ a b c, (a < b → b ≤ c → a < c)%Q.
Proof.
intros * Hab Hbc.
apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.lt_le_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_lt_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem le_lt_trans : ∀ a b c, (a ≤ b → b < c → a < c)%Q.
Proof.
intros * Hab Hbc.
apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.le_lt_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_le_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_lt_mono_pos_r.
Qed.

Theorem compare_add_mono_l : ∀ a b c, (a + b ?= a + c)%Q = (b ?= c)%Q.
Proof.
intros.
progress unfold Q.compare.
progress unfold Q.add; cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite (Z.mul_comm (q_Den a)).
do 2 rewrite Z.mul_assoc.
rewrite Z.compare_mul_mono_pos_r; [ | easy ].
do 2 rewrite Z.mul_add_distr_r.
rewrite Z.mul_mul_swap.
rewrite Z.compare_add_mono_l.
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.compare_mul_mono_pos_r.
Qed.

Theorem compare_add_mono_r : ∀ a b c, (a + c ?= b + c)%Q = (a ?= b)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
apply Q.compare_add_mono_l.
Qed.

Theorem add_le_mono_l : ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%Q.
Proof.
intros.
split; intros H. {
  apply Q.compare_le_iff in H.
  apply -> Q.compare_le_iff.
  intros H1; apply H; clear H.
  rewrite <- H1; symmetry.
  apply Q.compare_add_mono_l.
} {
  apply Q.compare_le_iff in H.
  apply -> Q.compare_le_iff.
  intros H1; apply H; clear H.
  rewrite <- H1.
  apply Q.compare_add_mono_l.
}
Qed.

Theorem add_le_mono_r : ∀ a b c, (a ≤ b → a + c ≤ b + c)%Q.
Proof.
intros * Hle.
do 2 rewrite (Q.add_comm _ c).
now apply Q.add_le_mono_l.
Qed.

Theorem add_le_compat : ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%Q.
Proof.
intros * Hle1 Hle2.
apply (Q.le_trans _ (a + d)).
apply Q.add_le_mono_l, Hle2.
apply Q.add_le_mono_r, Hle1.
Qed.

Theorem add_lt_mono_l : ∀ a b c, (b < c ↔ a + b < a + c)%Q.
Proof.
intros.
split; intros H. {
  apply Q.compare_lt_iff in H.
  apply -> Q.compare_lt_iff.
  rewrite <- H.
  apply Q.compare_add_mono_l.
} {
  apply Q.compare_lt_iff in H.
  apply -> Q.compare_lt_iff.
  rewrite <- H; symmetry.
  apply Q.compare_add_mono_l.
}
Qed.

Theorem add_lt_mono_r : ∀ a b c, (a < b ↔ a + c < b + c)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
apply Q.add_lt_mono_l.
Qed.

Theorem lt_irrefl : ∀ a, ¬ (a < a)%Q.
Proof. intros; apply Z.lt_irrefl. Qed.

(* Some theorems working with syntactic equality,
   not only with equivalence relation in Q *)

Theorem add_sub_assoc : ∀ x y z, (x + (y - z) = (x + y) - z)%Q.
Proof.
intros.
apply Q.add_assoc.
Qed.

Theorem add_sub_swap : ∀ x y z, (x + y - z = x - z + y)%Q.
Proof.
intros.
rewrite Q.add_comm.
rewrite <- Q.add_sub_assoc.
apply Q.add_comm.
Qed.

Theorem sub_diag : ∀ a, (a - a == 0)%Q.
Proof.
intros.
apply Z.compare_eq_iff; cbn.
progress unfold q_Den; cbn.
rewrite Z.mul_1_r.
rewrite Z.mul_opp_l.
apply Z.add_opp_diag_r.
Qed.

Theorem add_opp_diag_l : ∀ a, (-a + a == 0)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.sub_diag.
Qed.

Theorem add_opp_diag_r : ∀ a, (a + - a == 0)%Q.
Proof. apply Q.sub_diag. Qed.

Theorem add_sub: ∀ a b, (a + b - b == a)%Q.
Proof.
intros.
rewrite <- Q.add_sub_assoc.
rewrite Q.sub_diag.
now rewrite Q.add_0_r.
Qed.

Theorem sub_add : ∀ a b, (a - b + b == a)%Q.
Proof.
intros.
rewrite <- Q.add_sub_swap.
apply Q.add_sub.
Qed.

Theorem add_move_l : ∀ a b c, (c + a == b ↔ a == b - c)%Q.
Proof.
intros.
split; intros Heq. {
  rewrite <- Heq, Q.add_comm; symmetry.
  apply Q.add_sub.
} {
  rewrite Heq, Q.add_comm.
  apply Q.sub_add.
}
Qed.

Theorem add_move_r : ∀ a b c, (a + c == b ↔ a == b - c)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.add_move_l.
Qed.

Theorem fold_sub : ∀ a b, (a + - b = a - b)%Q.
Proof. easy. Qed.

Theorem le_0_sub : ∀ a b, (0 ≤ b - a ↔ a ≤ b)%Q.
Proof.
intros.
specialize Q.add_le_compat as H1.
split; intros Hab. {
  specialize (H1 0 (b - a) a a Hab (Q.le_refl _))%Q.
  rewrite Q.sub_add in H1.
  now rewrite Q.add_0_l in H1.
} {
  specialize (H1 a b (- a) (- a) Hab (Q.le_refl _))%Q.
  rewrite Q.fold_sub in H1.
  now rewrite Q.sub_diag in H1.
}
Qed.

Theorem sub_move_0_r : ∀ a b, (a - b == 0 ↔ a == b)%Q.
Proof.
intros.
split; intros Hab; [ | rewrite Hab; apply Q.sub_diag ].
apply (Q.add_compat_r _ _ b) in Hab.
rewrite Q.sub_add in Hab.
now rewrite Q.add_0_l in Hab.
Qed.

Theorem lt_0_sub : ∀ a b, (0 < b - a ↔ a < b)%Q.
Proof.
intros.
split; intros Hab. {
  apply Q.lt_iff in Hab.
  apply Q.lt_iff.
  destruct Hab as (Hab, Habz).
  split; [ now apply Q.le_0_sub | ].
  intros H; apply Habz.
  rewrite H.
  now rewrite Q.sub_diag.
} {
  apply Q.lt_iff in Hab.
  apply Q.lt_iff.
  destruct Hab as (Hab, Habz).
  split; [ now apply Q.le_0_sub | ].
  intros H; apply Habz; clear Habz.
  symmetry in H.
  now apply -> Q.sub_move_0_r in H.
}
Qed.

Theorem opp_sub_distr : ∀ a b, (- (a - b) = b - a)%Q.
Proof.
intros.
progress unfold Q.sub.
progress unfold Q.add.
progress unfold Q.opp.
do 2 rewrite q_Den_num_den.
cbn.
rewrite (Pos.mul_comm (q_den a)).
progress f_equal.
do 2 rewrite Z.mul_opp_l.
do 2 rewrite Z.add_opp_r.
apply Z.opp_sub_distr.
Qed.

Theorem sub_sub_distr : ∀ a b c, (a - (b - c) = (a - b) + c)%Q.
Proof.
intros.
progress unfold Q.sub at 1.
rewrite Q.opp_sub_distr.
progress unfold Q.sub.
rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c = a + c + b)%Q.
Proof.
intros.
do 2 rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem mul_div_assoc : ∀ a b c, (a * (b / c) = (a * b) / c)%Q.
Proof. intros; apply Q.mul_assoc. Qed.

Theorem mul_div_swap : ∀ a b c, (a / b * c = a * c / b)%Q.
Proof.
intros.
progress unfold Q.div.
do 2 rewrite <- Q.mul_assoc.
progress f_equal.
apply Q.mul_comm.
Qed.

Theorem opp_0 : (- 0 = 0)%Q.
Proof. easy. Qed.

Theorem sub_0_r : ∀ a, (a - 0 = a)%Q.
Proof.
intros.
progress unfold Q.sub.
rewrite Q.opp_0.
apply Q.add_0_r.
Qed.

Definition Q1 x := mk_q (q_Den x) (q_den x).

Theorem mul_add_distr_l' : ∀ x y z, (x * (y + z) * Q1 x = x * y + x * z)%Q.
Proof.
intros.
progress unfold Q.add.
progress unfold Q.mul.
cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos.mul_assoc.
rewrite Pos.mul_mul_swap.
progress f_equal.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 3 rewrite <- Z.mul_assoc.
rewrite <- Z.mul_add_distr_l.
f_equal.
do 2 rewrite Z.mul_assoc.
do 2 rewrite (Z.mul_mul_swap _ (q_Den x)).
apply Z.mul_add_distr_r.
Qed.

Theorem mul_add_distr_r' : ∀ x y z, ((x + y) * z * Q1 z = x * z + y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q.mul_add_distr_l'.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem mul_Q1_r : ∀ x y, (x * Q1 y == x)%Q.
Proof.
intros.
apply Z.compare_eq_iff; cbn.
rewrite <- Z.mul_assoc.
progress f_equal.
rewrite Z.mul_comm.
symmetry.
now rewrite q_Den_mul.
Qed.

(* *)

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c) == a * b + a * c)%Q.
Proof.
intros.
rewrite <- Q.mul_add_distr_l'.
symmetry.
apply Q.mul_Q1_r.
Qed.

Theorem mul_add_distr_r : ∀ x y z, ((x + y) * z == x * z + y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q.mul_add_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem mul_sub_distr_l : ∀ x y z, (x * (y - z) == x * y - x * z)%Q.
Proof.
intros.
progress unfold Q.sub.
rewrite Q.mul_add_distr_l.
apply Q.add_compat_l.
now rewrite Q.mul_opp_r.
Qed.

Theorem mul_sub_distr_r : ∀ x y z, ((x - y) * z == x * z - y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ - _)).
rewrite Q.mul_sub_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem lt_sub_lt_add_l : ∀ a b c, (a - b < c ↔ a < b + c)%Q.
Proof.
intros.
split; intros H. {
  apply (Q.add_lt_mono_r _ _ b) in H.
  rewrite Q.sub_add in H.
  now rewrite Q.add_comm in H.
} {
  apply (Q.add_lt_mono_r _ _ b).
  rewrite Q.sub_add.
  now rewrite Q.add_comm.
}
Qed.

Theorem lt_sub_lt_add_r : ∀ a b c, (a - c < b ↔ a < b + c)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.lt_sub_lt_add_l.
Qed.

Theorem lt_add_lt_sub_l : ∀ a b c, (a + b < c ↔ b < c - a)%Q.
Proof.
intros.
rewrite Q.add_comm.
split; intros Hlt. {
  apply (Q.add_lt_mono_r _ _ a).
  now rewrite Q.sub_add.
} {
  apply (Q.add_lt_mono_r _ _ a) in Hlt.
  now rewrite Q.sub_add in Hlt.
}
Qed.

Theorem lt_add_lt_sub_r : ∀ a b c, (a + b < c ↔ a < c - b)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.lt_add_lt_sub_l.
Qed.

Theorem mul_inv_diag_l : ∀ a, (¬ a == 0 → a⁻¹ * a == 1)%Q.
Proof.
intros * Hnz.
apply Z.compare_eq_iff.
apply Z.compare_neq_iff in Hnz.
rewrite Z.mul_1_r.
rewrite Z.mul_1_l.
progress unfold q_Den; cbn.
rewrite Z.mul_mul_swap.
rewrite <- Z.abs_sgn.
rewrite Pos2Z.inj_mul.
f_equal.
symmetry.
apply Z2Pos.id.
destruct a as (an, ad).
cbn in Hnz |-*.
rewrite Z.mul_1_r in Hnz.
clear ad.
apply Z.divide_pos_le. 2: {
  exists (Z.abs an); symmetry.
  apply Z.mul_1_r.
}
now apply Z.abs_pos.
Qed.

Theorem mul_inv_diag_r : ∀ a, (¬ a == 0 → a * a⁻¹ == 1)%Q.
Proof.
intros * Hnz.
rewrite Q.mul_comm.
now apply Q.mul_inv_diag_l.
Qed.

Theorem div_same : ∀ a, (¬ a == 0 → a / a == 1)%Q.
Proof. apply Q.mul_inv_diag_r. Qed.

Theorem mul_div : ∀ a b, (¬ b == 0 → a * b / b == a)%Q.
Proof.
intros * Hz.
progress unfold Q.div.
rewrite <- Q.mul_assoc.
rewrite <- (Q.mul_1_r a) at 2.
apply Q.mul_compat_l.
now apply Q.mul_inv_diag_r.
Qed.

Theorem mul_move_l : ∀ a b c, (¬ c == 0 → c * a == b ↔ a == b / c)%Q.
Proof.
intros * Hnz.
split; intros H. {
  rewrite <- H; symmetry.
  rewrite Q.mul_comm.
  now apply Q.mul_div.
} {
  rewrite H, Q.mul_comm.
  rewrite Q.mul_div_swap.
  now apply Q.mul_div.
}
Qed.

Theorem mul_move_r : ∀ a b c, (¬ c == 0 → a * c == b → a == b / c)%Q.
Proof.
intros * Hnz H.
apply Q.mul_move_l; [ easy | ].
now rewrite Q.mul_comm.
Qed.

Theorem inv_add_distr : ∀ a b c, (a + b # c == (a # c) + (b # c))%Q.
Proof.
intros.
apply Z.compare_eq_iff.
progress unfold Q.add; cbn.
do 4 rewrite q_Den_num_den.
rewrite <- Z.mul_add_distr_r.
rewrite Pos2Z.inj_mul.
apply Z.mul_assoc.
Qed.

Theorem inv_sub_distr : ∀ a b c, (a - b # c == (a # c) - (b # c))%Q.
Proof.
intros.
progress unfold Z.sub.
now rewrite Q.inv_add_distr.
Qed.

Theorem apart_0_1: ¬ (1 == 0)%Q.
Proof. easy. Qed.

Theorem eq_dec : ∀ a b, ({a == b} + {¬ a == b})%Q.
Proof.
intros.
progress unfold Q.eq.
remember (a ?= b)%Q as ab eqn:Hab.
symmetry in Hab.
now destruct ab; [ left | right | right ].
Qed.

(* min/max *)

Definition min x y := if Q.lt_le_dec x y then x else y.

Theorem min_dec : ∀ n m, {Q.min n m = n} + {Q.min n m = m}.
Proof.
intros n m.
unfold Q.min.
destruct (Q.lt_le_dec n m); [ left | right ]; reflexivity.
Qed.

Theorem min_comm : ∀ n m, (Q.min n m == Q.min m n)%Q.
Proof.
intros n m.
unfold Q.min.
destruct (Q.lt_le_dec n m) as [H₁| H₁]. {
  destruct (Q.lt_le_dec m n) as [H₂| H₂]; [ idtac | reflexivity ].
  apply Q.lt_le_incl in H₂.
  now apply Q.nle_gt in H₁.
}
destruct (Q.lt_le_dec m n) as [H₂| H₂]; [ reflexivity | idtac ].
apply Q.le_antisymm; assumption.
Qed.

Theorem min_l : ∀ n m, (n ≤ m)%Q → (Q.min n m == n)%Q.
Proof.
intros n m H.
unfold Q.min.
destruct (Q.lt_le_dec n m) as [| Hge]; [ reflexivity | idtac ].
apply Q.le_antisymm; assumption.
Qed.

End Q.

Number Notation Q Q.of_number Q.to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "a <= b" := (Q.le a b) : Q_scope.
Notation "a ≤ b" := (Q.le a b) : Q_scope.
Notation "a < b" := (Q.lt a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a '⁻¹'" := (Q.inv a) (at level 1, format "a ⁻¹") : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a (b - 1)) (at level 55) : Q_scope.

Notation "a ≤ b ≤ c" := (Q.le a b ∧ Q.le b c) : Q_scope.

Theorem eq_qeq : ∀ a b, a = b → (a == b)%Q.
Proof. now intros; subst. Qed.

Definition Q_ring_theory : ring_theory 0%Q 1%Q Q.add Q.mul Q.sub Q.opp Q.eq :=
  {| Radd_0_l a := eq_qeq _ _ (Q.add_0_l a);
     Radd_comm a b := eq_qeq _ _ (Q.add_comm a b);
     Radd_assoc a b c := eq_qeq _ _ (Q.add_assoc a b c);
     Rmul_1_l a := eq_qeq _ _ (Q.mul_1_l a);
     Rmul_comm a b := eq_qeq _ _ (Q.mul_comm a b);
     Rmul_assoc a b c := eq_qeq _ _ (Q.mul_assoc a b c);
     Rdistr_l := Q.mul_add_distr_r;
     Rsub_def a b := reflexivity (a + - b)%Q;
     Ropp_def := Q.add_opp_diag_r |}.

From Stdlib Require Import Ring.
Add Ring Q_ring : Q_ring_theory.

From Stdlib Require Import Field_theory.

Definition Q_field_theory :
  field_theory 0%Q 1%Q Q.add Q.mul Q.sub Q.opp Q.div Q.inv Q.eq :=
  {| F_R := Q_ring_theory;
     F_1_neq_0 := Q.apart_0_1;
     Fdiv_def a b := reflexivity _;
     Finv_l := Q.mul_inv_diag_l |}.

From Stdlib Require Import Field.
Add Field Q_field : Q_field_theory.
