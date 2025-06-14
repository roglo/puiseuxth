(** * A ℚ arithmetics

  [mk_q d n] represents the rationnal d/(n+1)
*)

Set Nested Proofs Allowed.
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

Theorem Nat_sub_lt_mono_l :
  ∀ a b c, (c < a ∨ b <= a → c < b → a - b < a - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem Nat_sub_lt_mono_r :
  ∀ a b c, (c < b ∨ c <= a → a < b → a - c < b - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem q_Den_num_den : ∀ a b, q_Den (mk_q a b) = Z.of_nat (b + 1).
Proof. easy. Qed.

Theorem q_Den_neq_0 : ∀ a, q_Den a ≠ 0%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

Theorem q_Den_pos : ∀ a, (0 < q_Den a)%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

Theorem q_Den_nonneg : ∀ a, (0 ≤ q_Den a)%Z.
Proof. now intros; unfold q_Den; rewrite Nat.add_1_r. Qed.

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
  | z_val true v => mk_q (q_Den a) v
  | z_val false v => mk_q (- q_Den a) v
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
Notation "a # b" := (mk_q a (b - 1)) (at level 55) : Q_scope.

Theorem q_Den_mul : ∀ a b, q_Den (a * b) = (q_Den a * q_Den b)%Z.
Proof.
intros; cbn.
progress unfold q_Den; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | easy ].
apply Nat2Z.inj_mul.
Qed.

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

Theorem add_compat_l : ∀ a b c, (b == c → a + b == a + c)%Q.
Proof.
intros * Heq.
progress unfold Q.eq in Heq |-*; cbn.
do 2 rewrite (Z.mul_comm (_ + _)).
do 2 rewrite (Z.add_comm (q_num a * _)).
progress unfold Q.add; cbn.
progress unfold q_Den; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.sub_add; [ | easy ].
do 2 rewrite Nat2Z.inj_mul.
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
progress unfold q_Den in Heq.
do 2 rewrite Z.mul_add_distr_l.
do 4 rewrite Z.mul_assoc.
rewrite (Z.mul_comm _ (q_num b)).
rewrite Heq.
rewrite (Z.mul_comm (q_num c)).
progress f_equal.
do 2 rewrite (Z.mul_mul_swap _ (q_num a)).
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
progress unfold Q.eq; cbn.
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
progress unfold Q.eq in Hab.
progress unfold Q.eq, Q.opp; cbn.
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

Theorem add_le_mono_l : ∀ a b c, (b ≤ c → a + b ≤ a + c)%Q.
Proof.
intros * Hle.
progress unfold Q.le in Hle |-*.
progress unfold Q.add.
progress unfold q_Den in Hle |-*.
remember (q_num a) as an eqn:H; clear H.
remember (q_num b) as bn eqn:H; clear H.
remember (q_num c) as cn eqn:H; clear H.
remember (q_den a) as ad eqn:H; clear H.
remember (q_den b) as bd eqn:H; clear H.
remember (q_den c) as cd eqn:H; clear H.
move an after bn; move ad after bd.
clear a b c.
cbn in Hle |-*.
do 2 rewrite Nat.add_1_r in Hle.
do 5 rewrite Nat.add_1_r.
cbn in Hle |-*.
do 2 rewrite (Z.mul_comm _ (z_val _ _)) in Hle.
do 6 rewrite (Z.mul_comm _ (z_val _ _)).
cbn in Hle |-*.
destruct an as [| sa va]. {
  cbn.
  destruct bn as [| sb vb]. {
    destruct cn as [| sc vc]; [ easy | ].
    rewrite Nat.sub_add; [ | easy ].
    destruct sc; [ easy | now exfalso ].
  }
  rewrite Nat.sub_add; [ | easy ].
  destruct sb. {
    destruct cn as [| sc vc]; [ easy | ].
    rewrite Nat.sub_add; [ | easy ].
    destruct sc; [ | now exfalso ].
    progress unfold Z.le in Hle; cbn in Hle.
    progress unfold Z.le; cbn.
    intros Hgt; apply Hle; clear Hle.
    rewrite Nat_compare_sub_cancel_r in Hgt; [ | flia | flia ].
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    apply Nat.compare_gt_iff in Hgt.
    apply Nat.compare_gt_iff.
    progress unfold pos_mul in Hgt.
    rewrite Nat.sub_add in Hgt; [ | easy ].
    rewrite Nat.sub_add in Hgt; [ | easy ].
    do 2 rewrite Nat.mul_assoc in Hgt.
    do 2 rewrite (Nat.mul_shuffle0 _ _ (ad + 1)) in Hgt.
    do 2 rewrite <- (Nat.mul_assoc ((ad + 1) * (ad + 1))) in Hgt.
    apply Nat.mul_lt_mono_pos_l in Hgt; [ easy | flia ].
  } {
    destruct cn as [| sc vc]; [ easy | ].
    destruct sc; [ easy | ].
    progress unfold Z.le in Hle |-*; cbn in Hle |-*.
    apply Nat.compare_le_iff in Hle.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    rewrite Nat.sub_add; [ | easy ].
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    apply Nat.nlt_ge in Hle.
    apply Nat.nlt_ge.
    intros Hgt; apply Hle; clear Hle.
    apply Nat_sub_lt_mono_r; [ right; easy | ].
    do 2 rewrite Nat.mul_assoc in Hgt.
    do 2 rewrite (Nat.mul_shuffle0 _ _ (ad + 1)) in Hgt.
    do 2 rewrite <- (Nat.mul_assoc ((ad + 1) * (ad + 1))) in Hgt.
    apply Nat.mul_lt_mono_pos_l in Hgt; [ easy | flia ].
  }
}
destruct sa. {
  destruct bn as [| sb vb]. {
    rewrite Z.add_0_r.
    rewrite Nat.sub_add; [ | easy ].
    destruct cn as [| sc bc]. {
      cbn.
      rewrite Nat.sub_add; [ | easy ].
      progress unfold Z.le; cbn.
      rewrite Nat_compare_sub_cancel_r; [ | flia | flia ].
      apply Nat.compare_le_iff.
      progress unfold pos_mul.
      rewrite Nat.sub_add; [ | easy ].
      rewrite Nat.sub_add; [ | easy ].
      do 2 rewrite Nat.mul_assoc.
      rewrite (Nat.mul_shuffle0 (ad + 1)).
      apply Nat.le_refl.
    }
    destruct sc; [ clear Hle; cbn | easy ].
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.sub_add; [ | flia ].
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat_compare_sub_cancel_r; [ | flia | flia ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.sub_add; [ | easy ].
    apply Nat.compare_le_iff.
    flia.
  }
  destruct sb. {
    destruct cn as [| sc vc]; [ easy | ].
    destruct sc; [ cbn | easy ].
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.sub_add; [ | flia ].
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat_compare_sub_cancel_r; [ | flia | flia ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.sub_add; [ | easy ].
    apply Nat.compare_le_iff.
    progress unfold Z.le in Hle.
    cbn in Hle.
    rewrite Nat_compare_sub_cancel_r in Hle; [ | easy | easy ].
    apply Nat.compare_le_iff in Hle.
    do 2 rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.sub_add; [ | flia ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.mul_add_distr_l (cd + 1)).
    rewrite (Nat.mul_add_distr_l _ (_ * _) (_ * _)).
    do 4 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_comm (cd + 1)).
    apply Nat.add_le_mono_l.
    do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
    now apply Nat.mul_le_mono_r.
  }
  destruct cn as [| sc vc]. {
    clear Hle; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat.sub_add; [ | easy ].
    remember (_ ?= _)%nat as x eqn:Hx.
    symmetry in Hx.
    destruct x; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hx.
    progress unfold Z.le; cbn.
    rewrite Nat.sub_sub_distr; [ | easy | flia Hx ].
    rewrite Nat.sub_add; [ | flia ].
    rewrite Nat_sub_sub_swap.
    rewrite Nat.sub_add; [ | flia Hx ].
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.mul_sub_distr_l.
    do 3 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_shuffle0 _ (cd + 1)).
    apply Nat.compare_le_iff.
    flia.
  }
  destruct sc. {
    clear Hle; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    remember (_ ?= _)%nat as x eqn:Hx.
    symmetry in Hx.
    destruct x; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hx.
    progress unfold Z.le; cbn.
    rewrite Nat.sub_sub_distr; [ | easy | flia Hx ].
    rewrite Nat.sub_add; [ | flia ].
    rewrite Nat_sub_sub_swap.
    rewrite Nat.sub_add; [ | flia Hx ].
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.mul_sub_distr_l.
    do 2 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_shuffle0 _ (cd + 1)).
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.sub_add; [ | flia ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.mul_add_distr_l ((ad + 1) * (bd + 1)) (_ * _)).
    rewrite Nat.mul_assoc.
    apply Nat.compare_le_iff.
    flia.
  }
  cbn.
  rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
  rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
  progress unfold Z.le in Hle.
  cbn in Hle.
  rewrite Nat_compare_sub_cancel_r in Hle; [ | easy | easy ].
  apply Nat.compare_le_iff in Hle.
  remember (_ ?= _)%nat as x eqn:Hx.
  symmetry in Hx.
  destruct x. {
    apply Nat.compare_eq_iff in Hx.
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y; [ easy | exfalso | easy ].
    apply Nat.compare_lt_iff in Hy.
    apply Nat.nle_gt in Hy.
    apply Hy; clear Hy.
    apply (Nat.mul_le_mono_r _ _ ((bd + 1) * (va + 1))) in Hle.
    rewrite Hx in Hle at 1.
    rewrite Nat.mul_assoc in Hle.
    rewrite (Nat.mul_shuffle0 (bd + 1)) in Hle.
    rewrite (Nat.mul_comm ((cd + 1) * (vb + 1))) in Hle.
    rewrite Nat.mul_assoc in Hle.
    apply <- Nat.mul_le_mono_pos_r in Hle; [ | flia ].
    do 2 rewrite <- Nat.mul_assoc in Hle.
    apply <- Nat.mul_le_mono_pos_l in Hle; [ | flia ].
    flia Hle.
  } {
    apply Nat.compare_lt_iff in Hx.
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y; [ easy | | easy ].
    apply Nat.compare_lt_iff in Hy.
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.sub_add _ (_ * _)); [ | easy ].
    do 2 rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hy ].
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hx ].
    do 2 rewrite Nat.mul_sub_distr_l.
    do 4 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_comm (cd + 1) (bd + 1)).
    apply Nat.sub_le_mono_r.
    do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
    now apply Nat.mul_le_mono_pos_r.
  } {
    apply Nat.compare_gt_iff in Hx.
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y. {
      exfalso.
      apply Nat.compare_eq_iff in Hy.
      apply Nat.nle_gt in Hx.
      apply Hx; clear Hx.
      apply (Nat.mul_le_mono_pos_l _ _ (cd + 1)); [ flia | ].
      rewrite Nat.mul_comm.
      rewrite Nat.mul_shuffle0.
      rewrite <- Nat.mul_assoc, Hy.
      do 2 rewrite Nat.mul_assoc.
      do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
      now apply Nat.mul_le_mono_pos_r.
    } {
      exfalso.
      apply Nat.compare_lt_iff in Hy.
      apply Nat.nle_gt in Hx.
      apply Hx; clear Hx.
      rewrite Nat.mul_comm.
      apply (Nat.mul_le_mono_pos_r _ _ ((vc + 1) * (cd + 1))); [ flia | ].
      do 2 rewrite Nat.mul_assoc.
      replace ((va + 1) * (bd + 1) * (vc + 1) * (cd + 1))%nat with
        (((bd + 1) * (vc + 1)) * ((cd + 1) * (va + 1)))%nat by flia.
      replace ((ad + 1) * (vb + 1) * (vc + 1) * (cd + 1))%nat with
        (((cd + 1) * (vb + 1)) * ((ad + 1) * (vc + 1)))%nat by flia.
      apply Nat.lt_le_incl in Hy.
      now apply Nat.mul_le_mono.
    }
    apply Nat.compare_gt_iff in Hy.
    (* j'ai déjà vu ce code plus haut... *)
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.sub_add _ (_ * _)); [ | easy ].
    do 2 rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hx ].
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hy ].
    do 2 rewrite Nat.mul_sub_distr_l.
    do 4 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_comm (cd + 1) (bd + 1)).
    apply Nat.sub_le_mono_l.
    do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
    now apply Nat.mul_le_mono_pos_r.
  }
}
destruct bn as [| sb vb]. {
  rewrite Z.add_0_r.
  rewrite Nat.sub_add; [ | easy ].
  destruct cn as [| sc vc]. {
    clear Hle; cbn.
    rewrite Nat.sub_add; [ | easy ].
    progress unfold Z.le; cbn.
    apply Nat.compare_le_iff.
    progress unfold pos_mul.
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    flia.
  } {
    destruct sc; [ clear Hle; cbn | easy ].
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    remember (_ ?= _)%nat as x eqn:Hx in |-*.
    symmetry in Hx.
    destruct x; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hx.
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.sub_add _ (_ * _)); [ flia | easy ].
  }
}
destruct sb. {
  destruct cn as [| sc vc]; [ easy | ].
  destruct sc; [ cbn | easy ].
  progress unfold Z.le in Hle; cbn in Hle.
  rewrite Nat_compare_sub_cancel_r in Hle; [ | easy | easy ].
  rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
  apply Nat.compare_le_iff in Hle.
  remember (_ ?= _)%nat as x eqn:Hx.
  symmetry in Hx.
  destruct x. {
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    apply Nat.compare_eq_iff in Hx.
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y; [ easy | easy | exfalso ].
    apply Nat.compare_gt_iff in Hy.
    apply Nat.nle_gt in Hy.
    apply Hy; clear Hy.
    apply (Nat.mul_le_mono_pos_r _ _ (vb + 1)); [ easy | ].
    rewrite (Nat.mul_shuffle0 (ad + 1)).
    rewrite <- Hx.
    do 2 rewrite (Nat.mul_shuffle0 _ (va + 1)).
    now apply Nat.mul_le_mono_r.
  } {
    apply Nat.compare_lt_iff in Hx.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y. {
      exfalso.
      apply Nat.compare_eq_iff in Hy.
      apply Nat.nle_gt in Hx.
      apply Hx; clear Hx.
      apply (Nat.mul_le_mono_pos_r _ _ (vc + 1)); [ easy | ].
      rewrite Nat.mul_shuffle0.
      rewrite <- Hy.
      do 2 rewrite (Nat.mul_shuffle0 _ (va + 1)).
      now apply Nat.mul_le_mono_r.
    } {
      apply Nat.compare_lt_iff in Hy.
      progress unfold Z.le; cbn.
      progress unfold pos_mul.
      apply Nat.compare_le_iff.
      apply Nat.sub_le_mono_r.
      rewrite Nat.sub_add; [ | easy ].
      rewrite (Nat.sub_add _ (_ * _)); [ | easy ].
      do 2 rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono_l.
      rewrite (Nat_sub_sub_swap _ 1).
      rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
      rewrite Nat.add_sub.
      rewrite Nat.sub_add; [ | flia Hx ].
      rewrite (Nat_sub_sub_swap _ 1).
      rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
      rewrite Nat.add_sub.
      rewrite Nat.sub_add; [ | flia Hy ].
      do 2 rewrite Nat.mul_sub_distr_l.
      do 4 rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm (cd + 1) (bd + 1)).
      apply Nat.sub_le_mono_r.
      do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
      now apply Nat.mul_le_mono_pos_r.
    } {
      exfalso.
      apply Nat.compare_gt_iff in Hy.
      apply Nat.nle_gt in Hx.
      apply Hx; clear Hx.
      rewrite Nat.mul_comm.
      apply (Nat.mul_le_mono_pos_r _ _ ((vc + 1) * (cd + 1))); [ flia | ].
      do 2 rewrite Nat.mul_assoc.
      replace ((vb + 1) * (ad + 1) * (vc + 1) * (cd + 1))%nat with
        (((ad + 1) * (vc + 1)) * ((cd + 1) * (vb + 1)))%nat by flia.
      replace ((bd + 1) * (va + 1) * (vc + 1) * (cd + 1))%nat with
        (((cd + 1) * (va + 1)) * ((bd + 1) * (vc + 1)))%nat by flia.
      apply Nat.lt_le_incl in Hy.
      now apply Nat.mul_le_mono.
    }
  } {
    apply Nat.compare_gt_iff in Hx.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    remember (_ ?= _)%nat as y eqn:Hy in |-*.
    symmetry in Hy.
    destruct y; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hy.
    progress unfold Z.le; cbn.
    progress unfold pos_mul.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    rewrite Nat.sub_add; [ | easy ].
    rewrite (Nat.sub_add _ (_ * _)); [ | easy ].
    do 2 rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hy ].
    rewrite (Nat_sub_sub_swap _ 1).
    rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
    rewrite Nat.add_sub.
    rewrite Nat.sub_add; [ | flia Hx ].
    do 2 rewrite Nat.mul_sub_distr_l.
    do 4 rewrite Nat.mul_assoc.
    rewrite (Nat.mul_comm (cd + 1) (bd + 1)).
    apply Nat.sub_le_mono_l.
    do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
    now apply Nat.mul_le_mono_pos_r.
  }
}
destruct cn as [| sc vc]. {
  clear Hle; cbn.
  progress unfold Z.le; cbn.
  progress unfold pos_mul.
  apply Nat.compare_le_iff.
  apply Nat.sub_le_mono_r.
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  rewrite <- Nat.add_sub_swap; [ | easy ].
  rewrite Nat.sub_add; [ | flia ].
  flia.
}
destruct sc. {
  clear Hle; cbn.
  rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
  remember (_ ?= _)%nat as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ easy | easy | ].
  apply Nat.compare_gt_iff in Hx.
  progress unfold Z.le.
  progress unfold pos_mul; cbn.
  rewrite Nat.sub_add; [ | easy ].
  rewrite (Nat.sub_add _ (_ * _)); [ | easy ].
  rewrite (Nat_sub_sub_swap _ 1).
  rewrite Nat.sub_sub_distr; [ | easy | now apply Nat.lt_le_incl ].
  rewrite Nat.add_sub.
  rewrite Nat.sub_add; [ | flia Hx ].
  rewrite <- Nat.add_sub_swap; [ | easy ].
  rewrite Nat.sub_add; [ | flia ].
  apply Nat.compare_le_iff; flia.
}
cbn.
progress unfold Z.le in Hle; cbn in Hle.
rewrite Nat_compare_sub_cancel_r in Hle; [ | easy | easy ].
apply Nat.compare_le_iff in Hle.
progress unfold Z.le; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.sub_add; [ | easy ].
rewrite Nat_compare_sub_cancel_r; [ | flia | flia ].
rewrite <- Nat.add_sub_swap; [ | easy ].
rewrite Nat.sub_add; [ | flia ].
rewrite <- Nat.add_sub_swap; [ | easy ].
rewrite Nat.sub_add; [ | flia ].
apply Nat.compare_le_iff.
do 2 rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono_pos_l; [ easy | ].
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
do 2 rewrite (Nat.mul_add_distr_l _ (_ * _)).
do 4 rewrite Nat.mul_assoc.
rewrite (Nat.mul_comm (cd + 1)).
apply Nat.add_le_mono_l.
do 2 rewrite (Nat.mul_shuffle0 _ (ad + 1)).
now apply Nat.mul_le_mono_pos_r.
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
progress unfold Q.eq; cbn.
progress unfold q_Den; cbn.
rewrite Z.mul_1_r.
rewrite Z.mul_opp_l.
apply Z.add_opp_diag_r.
Qed.

Theorem sub_add : ∀ a b, (a - b + b == a)%Q.
Proof.
intros.
rewrite <- Q.add_sub_swap.
rewrite <- Q.add_sub_assoc.
rewrite Q.sub_diag.
now rewrite Q.add_0_r.
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
progress unfold pos_mul; cbn.
rewrite (Nat.mul_comm (q_den b + 1)).
progress f_equal.
do 2 rewrite Z.mul_opp_l.
rewrite Z.add_comm.
rewrite Z.opp_add_distr.
now rewrite Z.opp_involutive.
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
progress unfold pos_mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
progress f_equal. {
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_add_distr_r.
  progress unfold q_Den; cbn.
  rewrite Nat.sub_add; [ | flia ].
  rewrite Nat.sub_add; [ | flia ].
  do 2 rewrite Nat2Z.inj_mul.
  do 4 rewrite Z.mul_assoc.
  do 2 rewrite (Z.mul_mul_swap _ (Z.of_nat (q_den x + 1))).
  easy.
} {
  do 3 rewrite <- Nat.mul_assoc.
  progress f_equal.
  progress f_equal.
  progress f_equal.
  apply Nat.mul_comm.
}
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
progress unfold Q.eq.
cbn.
rewrite <- Z.mul_assoc.
progress f_equal.
rewrite Z.mul_comm.
symmetry.
progress unfold q_Den; cbn.
progress unfold pos_mul.
rewrite Nat.sub_add; [ | flia ].
apply Nat2Z.inj_mul.
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
