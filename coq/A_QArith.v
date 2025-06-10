(** * A ℚ arithmetics

  [mk_q d n] represents the rationnal d/(n+1)
*)

From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Morphisms.
Require Import A_ZArith.
Require Import RingLike.Misc.

Record Q := mk_q
  { q_num : Z;
    q_den : nat }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Definition q_Den a := Z.of_nat (q_den a + 1).
Definition pos_mul a b := (a + 1) * (b + 1) - 1.

(* misc *)

Theorem Nat_compare_sub_cancel_l :
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

Theorem Nat_compare_sub_cancel_r :
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

Theorem Nat_1_le_mul_add_1 : ∀ a b, (1 <= (a + 1) * (b + 1))%nat.
Proof. flia. Qed.

Theorem Nat_add_1_r_pos : ∀ a, (0 < a + 1)%nat.
Proof. flia. Qed.

Hint Resolve Nat_1_le_mul_add_1 : core.
Hint Resolve Nat_add_1_r_pos : core.

(* end misc *)

Module Q.

Open Scope Z_scope.

Definition eq a b := q_num a * q_Den b = q_num b * q_Den a.

Definition add a b :=
  mk_q
    (q_num a * q_Den b + q_num b * q_Den a)
    (pos_mul (q_den a) (q_den b)).

Definition opp a := mk_q (- q_num a) (q_den a).
Definition sub a b := add a (opp b).

Definition mul a b :=
  mk_q (q_num a * q_num b) (pos_mul (q_den a) (q_den b)).

Definition inv a :=
  match q_num a with
  | z_zero => mk_q 0 0
  | z_val s v => mk_q (q_Den a) v
  end.

Definition div a b := mul a (inv b).

Definition compare a b :=
  q_num a * q_Den b ?= q_num b * q_Den a.

Definition le x y := (q_num x * q_Den y ≤ q_num y * q_Den x)%Z.
Definition lt x y := (q_num x * q_Den y < q_num y * q_Den x)%Z.

Definition of_number (n : Number.int) : option Q :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_q (Z.of_nat (Nat.of_uint n)) 0)
      | Decimal.Neg n => Some (mk_q (- Z.of_nat (Nat.of_uint n)) 0)
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Q) : option Number.int :=
  match q_den a with
  | 0%nat => Some (Z.to_number (q_num a))
  | _ => None
  end.

Number Notation Q of_number to_number : Q_scope.

Notation "a == b" := (eq a b) (at level 70) : Q_scope.
Notation "a + b" := (add a b) : Q_scope.
Notation "a - b" := (sub a b) : Q_scope.
Notation "a * b" := (mul a b) : Q_scope.
Notation "a / b" := (div a b) : Q_scope.
Notation "- a" := (opp a) : Q_scope.
Notation "a ≤ b" := (le a b) : Q_scope.
Notation "a < b" := (lt a b) : Q_scope.

Theorem eq_refl : ∀ a, (a == a)%Q.
Proof. easy. Qed.

Theorem eq_symm : ∀ a b, (a == b → b == a)%Q.
Proof. easy. Qed.

Theorem eq_trans : ∀ a b c, (a == b → b == c → a == c)%Q.
Proof.
intros * Hab Hbc.
progress unfold eq in Hab, Hbc |-*.
apply (f_equal (Z.mul (q_Den c))) in Hab.
apply (f_equal (Z.mul (q_Den a))) in Hbc.
do 2 rewrite (Z.mul_comm (q_Den c)) in Hab.
rewrite (Z.mul_comm (q_num b)) in Hab.
rewrite (Z.mul_comm (q_num c)) in Hbc.
do 2 rewrite Z.mul_assoc in Hbc.
rewrite Hbc in Hab.
do 2 rewrite <- (Z.mul_mul_swap _ _ (q_Den b)) in Hab.
rewrite (Z.mul_comm (q_Den a)) in Hab.
apply Z.mul_cancel_r in Hab; [ easy | ].
progress unfold q_Den.
now rewrite Nat.add_comm.
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
progress unfold pos_mul.
rewrite (Nat.mul_comm (q_den b + 1)).
easy.
Qed.

Theorem add_assoc : ∀ a b c, (a + (b + c))%Q = ((a + b) + c)%Q.
Proof.
intros.
progress unfold add.
progress unfold pos_mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
f_equal; [ | now rewrite Nat.mul_assoc ].
progress unfold q_Den; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
do 2 rewrite Nat2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
rewrite <- Z.add_assoc.
f_equal; [ apply Z.mul_assoc | ].
f_equal; [ apply Z.mul_mul_swap | ].
rewrite <- Z.mul_assoc.
f_equal; apply Z.mul_comm.
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Q = a.
Proof.
intros.
progress unfold add; cbn.
rewrite Z.mul_1_r, Nat.add_0_r.
rewrite Nat.add_sub.
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
progress unfold pos_mul.
now rewrite Z.mul_comm, Nat.mul_comm.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Q = ((a * b) * c)%Q.
Proof.
intros.
progress unfold mul.
progress unfold pos_mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
now rewrite Z.mul_assoc, Nat.mul_assoc.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Q = a.
Proof.
intros.
progress unfold mul; cbn.
destruct a as (na, da); cbn.
rewrite Nat.add_0_r, Nat.add_sub.
progress f_equal.
destruct na as [| sa va]; [ easy | ].
rewrite Nat.add_0_r, Nat.add_sub.
now destruct sa.
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
progress unfold le in Hab, Hba.
progress unfold eq.
now apply Z.le_antisymm.
Qed.

Theorem le_refl : ∀ a, (a ≤ a)%Q.
Proof. intros; apply Z.le_refl. Qed.

Theorem lt_le_incl : ∀ a b, (a < b)%Q → (a ≤ b)%Q.
Proof. intros * Hab; congruence. Qed.

Theorem q_Den_neq_0 : ∀ a, q_Den a ≠ 0%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

Theorem q_Den_pos : ∀ a, (0 < q_Den a)%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

Theorem q_Den_nonneg : ∀ a, (0 ≤ q_Den a)%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

Theorem order_eq_le_l : ∀ a b c, (a == b → c ≤ b → c ≤ a)%Q.
Proof.
intros * Heq Hle.
progress unfold Q.eq in Heq.
progress unfold Q.le in Hle |-*.
destruct (q_num a) as [| sa va]. {
  symmetry in Heq.
  rewrite Z.mul_0_l in Heq |-*.
  apply Z.integral in Heq.
  cbn in Heq.
  destruct Heq as [Heq| Heq]. {
    rewrite Heq in Hle; cbn in Hle.
    apply Z.nlt_ge in Hle.
    apply Z.nlt_ge.
    intros Hlt; apply Hle; clear Hle.
    (* perhaps a more specific theorem to be proved and used here: *)
    specialize (Z.mul_lt_mono_pos_l (q_num c) 0 (q_Den b)) as H1.
    rewrite Z.mul_0_r in H1.
    apply H1; [ clear H1 | apply q_Den_pos ].
    (* to do: Z.mul_lt_mono_pos_r, version r of the theorem below: *)
    specialize (Z.mul_lt_mono_pos_l (q_Den a) 0 (q_num c)) as H1.
    rewrite Z.mul_0_r, Z.mul_comm in H1.
    apply H1; [ apply q_Den_pos | easy ].
  }
  destruct Heq as [Heq| Heq]; [ | now destruct Heq ].
  now apply q_Den_neq_0 in Heq.
}
destruct (q_num b) as [| sb vb]. {
  rewrite Z.mul_0_l in Heq, Hle.
  apply Z.integral in Heq.
  cbn in Heq.
  destruct Heq as [Heq| Heq]; [ easy | ].
  destruct Heq as [Heq| Heq]; [ | now destruct Heq ].
  now apply q_Den_neq_0 in Heq.
}
move sb before sa.
specialize Z.mul_le_mono_pos_l as H1.
apply (H1 (q_Den a)) in Hle; [ clear H1 | apply q_Den_pos ].
do 2 rewrite (Z.mul_comm (q_Den a)) in Hle.
rewrite (Z.mul_mul_swap (z_val sb vb)) in Hle.
rewrite <- Heq in Hle.
do 2 rewrite (Z.mul_comm _ (q_Den b)) in Hle.
do 2 rewrite <- Z.mul_assoc in Hle.
apply Z.mul_le_mono_pos_l in Hle; [ easy | apply q_Den_pos ].
Qed.

Theorem order_eq_le_r : ∀ a b c, (a == b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Heq Hle.
progress unfold Q.eq in Heq.
progress unfold Q.le in Hle |-*.
destruct (q_num a) as [| sa va]. {
  symmetry in Heq.
  rewrite Z.mul_0_l in Heq |-*.
  apply Z.integral in Heq.
  cbn in Heq.
  destruct Heq as [Heq| Heq]. {
    rewrite Heq in Hle; cbn in Hle.
    specialize (Z.mul_le_mono_pos_r (q_Den b) 0 (q_num c)) as H1.
    rewrite Z.mul_0_l in H1.
    apply H1 in Hle; [ clear H1 | apply q_Den_pos ].
    apply Z.mul_nonneg_nonneg; [ easy | apply q_Den_nonneg ].
  }
  destruct Heq as [Heq| Heq]; [ | now destruct Heq ].
  now apply q_Den_neq_0 in Heq.
}
(* exactly same tactics as for the previous theorems!
   I tried to do a common theorem (lemma) from that
   but I failed. Perhaps I should try again *)
destruct (q_num b) as [| sb vb]. {
  rewrite Z.mul_0_l in Heq, Hle.
  apply Z.integral in Heq.
  cbn in Heq.
  destruct Heq as [Heq| Heq]; [ easy | ].
  destruct Heq as [Heq| Heq]; [ | now destruct Heq ].
  now apply q_Den_neq_0 in Heq.
}
move sb before sa.
specialize Z.mul_le_mono_pos_l as H1.
apply (H1 (q_Den a)) in Hle; [ clear H1 | apply q_Den_pos ].
do 2 rewrite (Z.mul_comm (q_Den a)) in Hle.
rewrite (Z.mul_mul_swap (z_val sb vb)) in Hle.
rewrite <- Heq in Hle.
do 2 rewrite (Z.mul_comm _ (q_Den b)) in Hle.
do 2 rewrite <- Z.mul_assoc in Hle.
apply Z.mul_le_mono_pos_l in Hle; [ easy | apply q_Den_pos ].
Qed.

Global Instance Q_add_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.add.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
progress unfold Q.eq in Hab, Hcd |-*.
progress unfold Q.add; cbn.
progress unfold q_Den; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.sub_add; [ | easy ].
do 2 rewrite Nat2Z.inj_mul.
(* chais pas *)
...

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

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Hle1 Hle2.
progress unfold Q.le in Hle1, Hle2 |-*.
progress unfold q_Den in Hle1, Hle2 |-*.
remember (q_num a) as an eqn:H; clear H.
remember (q_num b) as bn eqn:H; clear H.
remember (q_num c) as cn eqn:H; clear H.
remember (q_den a) as ad eqn:H; clear H.
remember (q_den b) as bd eqn:H; clear H.
remember (q_den c) as cd eqn:H; clear H.
move cn before bn; move cd before bd.
clear a b c.
do 2 rewrite Nat.add_1_r in Hle1, Hle2 |-*.
destruct bn as [| sb vb]. {
  destruct an as [| sa va]; [ now destruct cn | ].
  destruct sa; [ easy | ].
  destruct cn as [| sc vc]; [ easy | now destruct sc ].
}
destruct sb. {
  destruct an as [| sa va]. {
    destruct cn as [| sc vc]; [ easy | now destruct sc ].
  }
  destruct sa. {
    destruct cn as [| sc vc]; [ easy | ].
    destruct sc; [ | easy ].
    progress unfold Z.le in Hle1, Hle2 |-*.
    cbn in Hle1, Hle2 |-*.
    rewrite Nat_compare_sub_cancel_r in Hle1; [ | easy | easy ].
    rewrite Nat_compare_sub_cancel_r in Hle2; [ | easy | easy ].
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    apply Nat.compare_le_iff in Hle1, Hle2.
    apply Nat.compare_le_iff.
    apply (Nat.mul_le_mono_pos_r _ _ ((bd + 1) * (vb + 1))); [ flia | ].
    do 2 rewrite Nat.mul_assoc.
    progress replace ((va + 1) * (cd + 1) * (bd + 1) * (vb + 1))%nat with
      (((va + 1) * (bd + 1)) * ((vb + 1) * (cd + 1)))%nat by flia.
    progress replace ((vc + 1) * (ad + 1) * (bd + 1) * (vb + 1))%nat with
      (((vb + 1) * (ad + 1)) * ((vc + 1) * (bd + 1)))%nat by flia.
    now apply Nat.mul_le_mono.
  }
  destruct cn as [| sc vc]; [ easy | now destruct sc ].
}
destruct an as [| sa va]; [ easy | ].
destruct sa; [ easy | ].
destruct cn as [| sc vc]; [ easy | ].
destruct sc; [ easy | ].
cbn in Hle1, Hle2 |-*.
progress unfold Z.le in Hle1, Hle2 |-*.
cbn in Hle1, Hle2 |-*.
rewrite Nat_compare_sub_cancel_r in Hle1; [ | easy | easy ].
rewrite Nat_compare_sub_cancel_r in Hle2; [ | easy | easy ].
rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
apply Nat.compare_le_iff in Hle1, Hle2.
apply Nat.compare_le_iff.
apply (Nat.mul_le_mono_pos_r _ _ ((bd + 1) * (vb + 1))); [ flia | ].
do 2 rewrite Nat.mul_assoc.
progress replace ((va + 1) * (cd + 1) * (bd + 1) * (vb + 1))%nat with
  (((va + 1) * (bd + 1)) * ((vb + 1) * (cd + 1)))%nat by flia.
progress replace ((vc + 1) * (ad + 1) * (bd + 1) * (vb + 1))%nat with
  (((vb + 1) * (ad + 1)) * ((vc + 1) * (bd + 1)))%nat by flia.
now apply Nat.mul_le_mono.
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
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.
