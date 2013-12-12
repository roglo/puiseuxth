(* $Id: Field.v,v 2.36 2013-12-12 10:51:37 deraugla Exp $ *)

Require Import Utf8.
Require Import Ring_theory.
Require Import Field_theory.
Require Import Setoid.

(* begin new
Require Ring.
end new *)

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
  Record f α :=
    { ring : r α;
      inv : α → α;
      mul_inv_l : ∀ a,
        not (eq ring a (zero ring))
        → eq ring (mul ring (inv a) a) (one ring) }.
End Tdef.

Module Type FieldType.
  Parameter α : Type.
  Parameter fld : Tdef.f α.
  Let rng := Tdef.ring fld.
End FieldType.

Module Make (F : FieldType).

  Import F.
  Include Tdef.

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

  Add Parametric Morphism : (opp rng)
    with signature eq rng ==> eq rng
    as opp_morph.
  Proof.
  intros a b Heq.
  apply add_compat_l with (c := (- b)%rng) in Heq.
  rewrite add_opp_l in Heq.
  rewrite add_comm in Heq.
  apply add_compat_l with (c := (- a)%rng) in Heq.
  rewrite add_assoc in Heq.
  rewrite add_opp_l in Heq.
  rewrite add_0_l in Heq.
  symmetry in Heq.
  rewrite add_comm in Heq.
  rewrite add_0_l in Heq.
  assumption.
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

  Theorem mul_inv_r : ∀ x, (x ≠ 0)%rng → (x * inv fld x = 1)%rng.
  Proof.
  intros x H; rewrite mul_comm.
  apply mul_inv_l; assumption.
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

  Theorem mul_reg_r : ∀ a b c, (c ≠ 0)%rng → (a * c = b * c)%rng → (a = b)%rng.
  Proof.
  intros a b c Hc Habc.
  apply mul_compat_r with (c := inv fld c) in Habc.
  do 2 rewrite <- mul_assoc in Habc.
  rewrite mul_inv_r in Habc; [ idtac | assumption ].
  do 2 rewrite mul_1_r in Habc.
  assumption.
  Qed.

  Theorem mul_reg_l : ∀ a b c, (c ≠ 0)%rng → (c * a = c * b)%rng → (a = b)%rng.
  Proof.
  intros a b c Hc Habc.
  rewrite mul_comm in Habc; symmetry in Habc.
  rewrite mul_comm in Habc; symmetry in Habc.
  eapply mul_reg_r; eassumption.
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

  Theorem mul_opp_l : ∀ a b, ((-a) * b = - (a * b))%rng.
  Proof.
  intros a b.
  apply add_reg_l with (c := (a * b)%rng).
  rewrite add_opp_r.
  rewrite <- mul_add_distr_r.
  rewrite add_opp_r, mul_0_l.
  reflexivity.
  Qed.

  Theorem mul_opp_r : ∀ a b, (a * (- b) = - (a * b))%rng.
  Proof.
  intros a b.
  rewrite mul_comm; symmetry.
  rewrite mul_comm; symmetry.
  apply mul_opp_l.
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

  Theorem eq_mul_0_l : ∀ n m, (n * m = 0)%rng → (m ≠ 0)%rng → (n = 0)%rng.
  Proof.
  intros n m Hnm Hm.
  rewrite <- mul_0_l with (a := m) in Hnm.
  apply mul_reg_r in Hnm; assumption.
  Qed.

  Theorem eq_mul_0_r : ∀ n m, (n * m = 0)%rng → (n ≠ 0)%rng → (m = 0)%rng.
  Proof.
  intros n m Hnm Hm.
  rewrite <- mul_0_r with (a := n) in Hnm.
  apply mul_reg_l in Hnm; assumption.
  Qed.

  (* AFAIK cannot be do with 'Add Parametric Morphim: (inv fld)
     because there is a condition 'a ≠ 0'; question: is is possible
     to do a conditional morphism? *)
  Theorem inv_compat : ∀ a b,
    (a ≠ 0)%rng
    → (a = b)%rng
      → (inv fld a = inv fld b)%rng.
  Proof.
  intros a b Ha Heq.
  remember Heq as Hab; clear HeqHab.
  apply mul_compat_l with (c := inv fld b) in Heq.
  unfold rng in Heq.
  rewrite mul_inv_l in Heq.
   apply mul_compat_r with (c := inv fld a) in Heq.
   rewrite mul_1_l in Heq.
   rewrite <- mul_assoc in Heq.
   rewrite mul_inv_r in Heq; [ idtac | assumption ].
   rewrite mul_1_r in Heq.
   symmetry; assumption.

   intros H.
   rewrite H in Heq at 3.
   rewrite mul_0_r in Heq.
   rewrite H in Hab.
   contradiction.
  Qed.

End Make.
