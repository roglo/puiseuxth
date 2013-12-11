(* $Id: Ring.v,v 2.2 2013-12-11 06:54:52 deraugla Exp $ *)

Require Import Utf8.
Require Import Setoid.

Set Implicit Arguments.

Module Tdef.
  Record r α :=
    { zero : α;
      one : α;
      add : α → α → α;
      mul : α → α → α;
      opp : α → α;
      eq : α → α → Prop;
      eq_refl : ∀ a, eq a a;
      eq_sym : ∀ a b, eq a b → eq b a;
      eq_trans : ∀ a b c, eq a b → eq b c → eq a c;
      neq_1_0 : not (eq one zero);
      add_comm : ∀ a b, eq (add a b) (add b a);
      add_assoc : ∀ a b c, eq (add a (add b c)) (add (add a b) c);
      add_0_l : ∀ a, eq (add zero a) a;
      add_opp_l : ∀ a, eq (add (opp a) a) zero;
      add_compat_l : ∀ a b c, eq a b → eq (add c a) (add c b);
      mul_comm : ∀ a b, eq (mul a b) (mul b a);
      mul_assoc : ∀ a b c, eq (mul a (mul b c)) (mul (mul a b) c);
      mul_1_l : ∀ a, eq (mul one a) a;
      mul_compat_l : ∀ a b c, eq a b → eq (mul c a) (mul c b);
      mul_add_distr_l : ∀ a b c,
        eq (mul a (add b c)) (add (mul a b) (mul a c)) }.
End Tdef.

Module Type RingType.
  Parameter α : Type.
  Parameter rng : Tdef.r α.
End RingType.

Module Make (F : RingType).

  Import F.
  Import Tdef.

  Module Syntax.
    Delimit Scope ring_scope with rng.
    Notation "0" := (zero rng) : ring_scope.
    Notation "1" := (one rng) : ring_scope.
    Notation "- a" := (opp rng a) : ring_scope.
    Notation "a = b" := (eq rng a b) : ring_scope.
    Notation "a ≠ b" := (not (eq rng a b)) : ring_scope.
    Notation "a + b" := (add rng a b) : ring_scope.
    Notation "a - b" := (add rng a (opp rng b)) : ring_scope.
    Notation "a * b" := (mul rng a b) : ring_scope.
  End Syntax.

  Import Syntax.

  Add Parametric Relation : α (eq rng)
   reflexivity proved by (eq_refl rng)
   symmetry proved by (eq_sym rng)
   transitivity proved by (eq_trans rng)
   as eq_rel.

  Add Parametric Morphism : (add rng)
    with signature eq rng ==> eq rng ==> eq rng
    as add_morph.
  Proof.
  intros a b Hab c d Hcd.
  rewrite add_comm; symmetry.
  rewrite add_comm; symmetry.
  rewrite add_compat_l; [ idtac | eassumption ].
  rewrite add_comm; symmetry.
  rewrite add_comm; symmetry.
  rewrite add_compat_l; [ reflexivity | eassumption ].
  Qed.

  Add Parametric Morphism : (mul rng)
    with signature eq rng ==> eq rng ==> eq rng
    as mul_morph.
  Proof.
  intros a b Hab c d Hcd.
  rewrite mul_comm; symmetry.
  rewrite mul_comm; symmetry.
  rewrite mul_compat_l; [ idtac | eassumption ].
  rewrite mul_comm; symmetry.
  rewrite mul_comm; symmetry.
  rewrite mul_compat_l; [ reflexivity | eassumption ].
  Qed.

  Theorem add_opp_l : ∀ x, (- x + x = 0)%rng.
  Proof. apply add_opp_l. Qed.

  Theorem add_opp_r : ∀ x, (x - x = 0)%rng.
  Proof.
  intros x; rewrite add_comm.
  apply add_opp_l.
  Qed.

  Theorem mul_1_r : ∀ a, (a * 1 = a)%rng.
  Proof.
  intros a.
  rewrite mul_comm, mul_1_l.
  reflexivity.
  Qed.

  Theorem add_compat_r : ∀ a b c, (a = b)%rng → (a + c = b + c)%rng.
  Proof.
  intros a b c Hab.
  rewrite Hab; reflexivity.
  Qed.

  Theorem mul_compat_r : ∀ a b c, (a = b)%rng → (a * c = b * c)%rng.
  Proof.
  intros a b c Hab.
  rewrite Hab; reflexivity.
  Qed.

  Theorem mul_add_distr_r : ∀ x y z, ((x + y) * z = x * z + y * z)%rng.
  Proof.
  intros x y z.
  rewrite mul_comm.
  rewrite mul_add_distr_l.
  rewrite mul_comm.
  assert (eq rng (mul rng z y) (mul rng y z)) as H.
   apply mul_comm.

   rewrite H; reflexivity.
  Qed.

  Theorem add_0_r : ∀ a, (a + 0 = a)%rng.
  Proof.
  intros a.
  rewrite add_comm.
  apply add_0_l.
  Qed.

  Theorem opp_0 : (- 0 = 0)%rng.
  Proof.
  etransitivity; [ symmetry; apply add_0_l | idtac ].
  apply add_opp_r.
  Qed.

  Theorem add_reg_r : ∀ a b c, (a + c = b + c)%rng → (a = b)%rng.
  Proof.
  intros a b c Habc.
  apply add_compat_r with (c := (- c)%rng) in Habc.
  do 2 rewrite <- add_assoc in Habc.
  rewrite add_opp_r in Habc.
  do 2 rewrite add_0_r in Habc.
  assumption.
  Qed.

  Theorem add_reg_l : ∀ a b c, (c + a = c + b)%rng → (a = b)%rng.
  Proof.
  intros a b c Habc.
  apply add_reg_r with (c := c).
  rewrite add_comm; symmetry.
  rewrite add_comm; symmetry.
  assumption.
  Qed.

  Theorem add_id_uniq : ∀ a b, (a + b = a)%rng → (b = 0)%rng.
  Proof.
  intros a b Hab.
  rewrite add_comm in Hab.
  apply add_reg_r with (c := a).
  rewrite add_0_l; assumption.
  Qed.

  Theorem mul_0_l : ∀ a, (0 * a = 0)%rng.
  Proof.
  intros a.
  assert (0 * a + a = a)%rng as H.
   transitivity (0 * a + 1 * a)%rng.
    rewrite mul_1_l; reflexivity.

    rewrite <- mul_add_distr_r.
    rewrite add_0_l, mul_1_l.
    reflexivity.

   apply add_reg_r with (c := a).
   rewrite add_0_l; assumption.
  Qed.

  Theorem mul_0_r : ∀ a, (a * 0 = 0)%rng.
  Proof.
  intros a.
  rewrite mul_comm, mul_0_l.
  reflexivity.
  Qed.

  Theorem add_shuffle0 : ∀ n m p, (n + m + p = n + p + m)%rng.
  Proof.
  intros n m p.
  do 2 rewrite <- add_assoc.
  assert (eq rng (add rng m p) (add rng p m)) as H by apply add_comm.
  rewrite H; reflexivity.
  Qed.

  Theorem mul_shuffle0 : ∀ n m p,
    eq rng (mul rng (mul rng n m) p) (mul rng (mul rng n p) m).
  Proof.
  intros n m p.
  do 2 rewrite <- mul_assoc.
  assert (eq rng (mul rng m p) (mul rng p m)) as H by apply mul_comm.
  rewrite H; reflexivity.
  Qed.

  Theorem mul_eq_0 : ∀ n m, (n = 0)%rng ∨ (m = 0)%rng → (n * m = 0)%rng.
  Proof.
  intros n m H.
  destruct H as [H| H]; rewrite H; [ apply mul_0_l | apply mul_0_r ].
  Qed.

End Make.
